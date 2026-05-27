"""
CS292C Homework 2 — Problem 3: Agent Permission Policy Verification (25 points)
=================================================================================
Encode a realistic agent permission policy as SMT formulas and use Z3 to
analyze it for safety properties and privilege escalation vulnerabilities.
"""

from z3 import *

# ============================================================================
# Constants
# ============================================================================

FILE_READ     = 0
FILE_WRITE    = 1
SHELL_EXEC    = 2
NETWORK_FETCH = 3

ADMIN     = 0
DEVELOPER = 1
VIEWER    = 2

# ============================================================================
# Sorts and Functions
#
# Do NOT modify these declarations.
# ============================================================================

User     = DeclareSort('User')
Resource = DeclareSort('Resource')

role         = Function('role',         User,     IntSort())
is_sensitive = Function('is_sensitive', Resource, BoolSort())
in_sandbox   = Function('in_sandbox',  Resource, BoolSort())
owner        = Function('owner',        Resource, User)

allowed = Function('allowed', User, IntSort(), Resource, BoolSort())


# ============================================================================
# Part (a): Encode the Policy — 10 pts
# ============================================================================

def make_policy():
    """Return a list of Z3 constraints encoding rules R1–R5."""
    u = Const('u', User)
    r = Const('r', Resource)
    t = Int('t')

    constraints = []

    # Single closed-world iff.  Each disjunct is one permission branch.
    constraints.append(ForAll([u, t, r],
        allowed(u, t, r) ==
        Or(
            # R1: viewer — file_read, non-sensitive only
            And(role(u) == VIEWER,
                t == FILE_READ,
                Not(is_sensitive(r))),

            # R2a: developer — file_read anything
            And(role(u) == DEVELOPER,
                t == FILE_READ),

            # R2b: developer — file_write owned or sandbox
            And(role(u) == DEVELOPER,
                t == FILE_WRITE,
                Or(owner(r) == u, in_sandbox(r))),

            # R3 + R4: admin shell_exec, but only on non-sensitive resources
            #   (R4 overrides R3: sensitive shell_exec is blocked for everyone)
            And(role(u) == ADMIN,
                t == SHELL_EXEC,
                Not(is_sensitive(r))),

            # R3: admin file_read or file_write — no extra restrictions
            And(role(u) == ADMIN,
                Or(t == FILE_READ, t == FILE_WRITE)),

            # R3 + R5: admin network_fetch — only in sandbox
            #   (R5 restricts network_fetch to sandbox for all roles;
            #    only admins have network_fetch at all, so this is the sole
            #    network_fetch branch)
            And(role(u) == ADMIN,
                t == NETWORK_FETCH,
                in_sandbox(r)),
        )
    ))

    # Sanity: every user has exactly one of the three roles.
    # Not strictly required by R1–R5 but prevents degenerate models where
    # role(u) is some unconstrained integer outside {0,1,2}.
    constraints.append(ForAll([u],
        Or(role(u) == ADMIN,
           role(u) == DEVELOPER,
           role(u) == VIEWER)))

    return constraints


# ============================================================================
# Part (b): Policy Queries — 8 pts
# ============================================================================

def query(description, policy, extra):
    """Helper: check if `extra` constraints are SAT under the policy."""
    s = Solver()
    s.add(policy)
    s.add(extra)
    result = s.check()
    print(f"  {description}")
    print(f"  → {result}")
    if result == sat:
        m = s.model()
        print(f"    Model: {m}")
    print()
    return result


def part_b():
    """
    Answer the four queries from the README.
    For Q4, also demonstrate what becomes possible when R4 is removed.
    """
    policy = make_policy()
    print("=== Part (b): Policy Queries ===\n")

    # Q1: Can a developer write to a sensitive file they don't own, in sandbox?
    # Expected: SAT. 
    # R2b allows file_write when the resource is in the sandbox, regardless
    # of ownership or sensitivity. The policy has no sensitivity guard on
    # developer file_write, so Z3 can satisfy all constraints simultaneously.

    u1    = Const('u_q1', User)
    r1    = Const('r_q1', Resource)
    other = Const('other_q1', User)
    query("Q1: developer file_write on sensitive resource (not owner, in sandbox)?",
          policy,
          [role(u1)      == DEVELOPER,
           is_sensitive(r1),
           in_sandbox(r1),
           owner(r1)     == other,
           u1            != other,
           allowed(u1, FILE_WRITE, r1)])

    # Q2: Can an admin network_fetch a resource outside the sandbox?
    # Expected: UNSAT.
    # The only network_fetch branch in the policy requires in_sandbox(r).
    # Asserting Not(in_sandbox(r)) alongside allowed(admin, NETWORK_FETCH, r)
    # is a contradiction under the closed-world encoding.

    u2 = Const('u_q2', User)
    r2 = Const('r_q2', Resource)
    query("Q2: admin network_fetch outside sandbox?",
          policy,
          [role(u2) == ADMIN,
           Not(in_sandbox(r2)),
           allowed(u2, NETWORK_FETCH, r2)])

    # Q3: Is there ANY role that can shell_exec on a sensitive resource?
    # Expected: UNSAT.
    # R4 is the universal restriction: the only admin shell_exec branch
    # carries Not(is_sensitive(r)), viewers have no shell_exec branch at all,
    # and developers have no shell_exec branch in the base policy.
    # Therefore no role/user can shell_exec a sensitive resource.
    u3 = Const('u_q3', User)
    r3 = Const('r_q3', Resource)
    query("Q3: any role shell_exec on a sensitive resource?",
          policy,
          [is_sensitive(r3),
           allowed(u3, SHELL_EXEC, r3)])

    # Q4: What dangerous action becomes possible when R4 is removed?
    # Without R4, admins gain unrestricted shell_exec — including on sensitive
    # resources. This means an admin could run arbitrary shell commands against
    # secrets files, private keys, production configs, etc., and potentially
    # exfiltrate or corrupt that data. Below we rebuild the policy with the
    # sensitive guard stripped from the admin shell_exec branch and confirm
    # the attack is now SAT.
    print("--- Q4: policy without R4 ---")

    u4 = Const('u_q4', User)
    r4 = Const('r_q4', Resource)
    t4 = Int('t4')

    # Rebuild without the Not(is_sensitive) guard on the admin SHELL_EXEC branch.
    no_r4_policy = [
        ForAll([u4, t4, r4],
            allowed(u4, t4, r4) ==
            Or(
                And(role(u4) == VIEWER,
                    t4 == FILE_READ,
                    Not(is_sensitive(r4))),
                And(role(u4) == DEVELOPER,
                    t4 == FILE_READ),
                And(role(u4) == DEVELOPER,
                    t4 == FILE_WRITE,
                    Or(owner(r4) == u4, in_sandbox(r4))),
                # R4 REMOVED: admin shell_exec now has no sensitive guard
                And(role(u4) == ADMIN,
                    t4 == SHELL_EXEC),
                And(role(u4) == ADMIN,
                    Or(t4 == FILE_READ, t4 == FILE_WRITE)),
                And(role(u4) == ADMIN,
                    t4 == NETWORK_FETCH,
                    in_sandbox(r4)),
            )),
        ForAll([u4],
            Or(role(u4) == ADMIN,
               role(u4) == DEVELOPER,
               role(u4) == VIEWER)),
    ]

    u4q = Const('u_q4q', User)
    r4q = Const('r_q4q', Resource)
    query("Q4: without R4, admin shell_exec on sensitive resource? (should be SAT)",
          no_r4_policy,
          [role(u4q)        == ADMIN,
           is_sensitive(r4q),
           allowed(u4q, SHELL_EXEC, r4q)])

    # Explanation: Without R4, an admin can run a shell command against any sensitive resource
    # (e.g., /etc/shadow, a private key file, a production database config).
    # This bypasses the intent of R4 entirely and could allow an admin —
    # whether malicious or simply careless — to leak secrets, corrupt critical
    # data, or pivot to further attacks. R4 therefore functions as a hard safety
    # floor that even privileged users cannot bypass.


# ============================================================================
# Part (c): Privilege Escalation — 7 pts
#
# New rule R6: Developers may shell_exec on non-sensitive sandbox resources.
#
# Attack:
#   Step 1 — developer shell_execs r1 (non-sensitive, in sandbox; allowed by R6).
#             Side-effect: the command changes r2's sensitivity flag from
#             True → False (e.g., it overwrites an access-control config).
#   Step 2 — developer shell_execs r2. Before step 1, r2 was sensitive so
#             this would have been blocked. After step 1, r2 appears non-sensitive
#             and the permission check passes.
#
# Encoding: two snapshots (is_sensitive_before / is_sensitive_after) and two
# corresponding `allowed` functions, each derived from the full policy+R6.
# ============================================================================

def part_c():
    print("=== Part (c): Privilege Escalation ===\n")

    # Two snapshots of the world's sensitivity labelling.
    is_sensitive_before = Function('is_sensitive_before', Resource, BoolSort())
    is_sensitive_after  = Function('is_sensitive_after',  Resource, BoolSort())

    # Two copies of the `allowed` predicate, one per snapshot.
    allowed_before = Function('allowed_before', User, IntSort(), Resource, BoolSort())
    allowed_after  = Function('allowed_after',  User, IntSort(), Resource, BoolSort())

    def policy_with_r6(allowed_fn, sens_fn):
        """
        Build the full policy (R1–R5 + R6) parameterized over an allowed
        function and a sensitivity snapshot function. R6 adds:
          developer may shell_exec on non-sensitive, in-sandbox resources.
        """
        u = Const('u_pc', User)
        r = Const('r_pc', Resource)
        t = Int('t_pc')
        return ForAll([u, t, r],
            allowed_fn(u, t, r) ==
            Or(
                And(role(u) == VIEWER,    t == FILE_READ,    Not(sens_fn(r))),
                And(role(u) == DEVELOPER, t == FILE_READ),
                And(role(u) == DEVELOPER, t == FILE_WRITE,
                    Or(owner(r) == u, in_sandbox(r))),
                # R6: developer shell_exec on non-sensitive sandbox resource
                And(role(u) == DEVELOPER, t == SHELL_EXEC,
                    Not(sens_fn(r)), in_sandbox(r)),
                # R3 + R4: admin shell_exec, non-sensitive only
                And(role(u) == ADMIN,     t == SHELL_EXEC,   Not(sens_fn(r))),
                And(role(u) == ADMIN,     Or(t == FILE_READ, t == FILE_WRITE)),
                And(role(u) == ADMIN,     t == NETWORK_FETCH, in_sandbox(r)),
            ))

    base = [
        policy_with_r6(allowed_before, is_sensitive_before),
        policy_with_r6(allowed_after,  is_sensitive_after),
        ForAll([Const('u_role', User)],
            Or(role(Const('u_role', User)) == ADMIN,
               role(Const('u_role', User)) == DEVELOPER,
               role(Const('u_role', User)) == VIEWER)),
    ]

    dev = Const('dev', User)
    r1  = Const('r1', Resource)   # lever: non-sensitive sandbox resource
    r2  = Const('r2', Resource)   # target: starts sensitive, ends non-sensitive

    # ------------------------------------------------------------------
    # Attack trace (no fix)
    # ------------------------------------------------------------------
    # Step 1: developer shell_execs r1 — legal because r1 is non-sensitive
    #         and in_sandbox (R6 permits this).
    # Side-effect: r2's sensitivity flips from True → False.
    # Step 2: developer shell_execs r2 in the AFTER world — now legal because
    #         r2 is no longer sensitive. Before the flip it would have been blocked.
    attack = [
        role(dev) == DEVELOPER,

        # r1: non-sensitive sandbox resource; step-1 shell_exec is allowed
        Not(is_sensitive_before(r1)),
        in_sandbox(r1),
        allowed_before(dev, SHELL_EXEC, r1),

        # Sensitivity is stable for r1 across the two snapshots
        is_sensitive_after(r1) == is_sensitive_before(r1),

        # r2: sensitive before, non-sensitive after (the flip)
        is_sensitive_before(r2),
        Not(is_sensitive_after(r2)),
        in_sandbox(r2),

        # Step 2: developer CAN shell_exec r2 in the AFTER world
        allowed_after(dev, SHELL_EXEC, r2),

        # Confirm the escalation is real: step 2 would NOT have been allowed
        # in the BEFORE world (r2 was sensitive then)
        Not(allowed_before(dev, SHELL_EXEC, r2)),
    ]

    print("--- Escalation check (no fix) ---")
    s = Solver()
    s.add(base + attack)
    result = s.check()
    print(f"  Result: {result}")
    if result == sat:
        m = s.model()
        print(f"  Attack succeeds. Model:\n    {m}")
        print("  Interpretation: the developer used a permitted shell_exec on r1")
        print("  to flip r2's sensitivity from True → False, then shell_exec'd r2")
        print("  even though r2 was sensitive at the trace's start. R4 is bypassed.\n")
    else:
        print("  No attack found (unexpected).\n")

    # ------------------------------------------------------------------
    # The fix: sticky sensitivity
    # ------------------------------------------------------------------
    # [EXPLAIN]
    # Root cause: the step-2 permission check uses only the AFTER snapshot,
    # so the historical sensitivity of r2 is invisible to it.
    #
    # Fix — "sticky sensitivity": a resource is considered sensitive for the
    # duration of the trace if it was sensitive in ANY snapshot. Concretely,
    # define eff_sens(r) = is_sensitive_before(r) OR is_sensitive_after(r),
    # and use eff_sens in the step-2 (AFTER) policy instead of is_sensitive_after.
    # Because r2 was sensitive before, eff_sens(r2) stays True even after the
    # flip, and the shell_exec on r2 remains blocked.
    #
    # This means sensitivity labels are monotone-increasing in the trace:
    # a resource can be newly marked sensitive at any point, but can never be
    # "un-marked" in a way that affects permission checks.

    print("--- Escalation check (with fix: sticky sensitivity) ---")

    allowed_after_fixed = Function('allowed_after_fixed',
                                   User, IntSort(), Resource, BoolSort())

    def policy_sticky(allowed_fn):
        """Policy variant using eff_sens for the shell_exec guards."""
        u = Const('u_fix', User)
        r = Const('r_fix', Resource)
        t = Int('t_fix')
        # Effective sensitivity: was sensitive in before OR after
        eff_sens = lambda x: Or(is_sensitive_before(x), is_sensitive_after(x))
        return ForAll([u, t, r],
            allowed_fn(u, t, r) ==
            Or(
                And(role(u) == VIEWER,    t == FILE_READ,    Not(eff_sens(r))),
                And(role(u) == DEVELOPER, t == FILE_READ),
                And(role(u) == DEVELOPER, t == FILE_WRITE,
                    Or(owner(r) == u, in_sandbox(r))),
                # R6 with sticky sensitivity
                And(role(u) == DEVELOPER, t == SHELL_EXEC,
                    Not(eff_sens(r)), in_sandbox(r)),
                And(role(u) == ADMIN,     t == SHELL_EXEC,   Not(eff_sens(r))),
                And(role(u) == ADMIN,     Or(t == FILE_READ, t == FILE_WRITE)),
                And(role(u) == ADMIN,     t == NETWORK_FETCH, in_sandbox(r)),
            ))

    fixed_base = [
        policy_with_r6(allowed_before, is_sensitive_before),
        policy_sticky(allowed_after_fixed),
        ForAll([Const('u_role2', User)],
            Or(role(Const('u_role2', User)) == ADMIN,
               role(Const('u_role2', User)) == DEVELOPER,
               role(Const('u_role2', User)) == VIEWER)),
    ]

    # Same attack, but step 2 now uses the fixed policy
    fixed_attack = [
        role(dev) == DEVELOPER,
        Not(is_sensitive_before(r1)),
        in_sandbox(r1),
        allowed_before(dev, SHELL_EXEC, r1),
        is_sensitive_after(r1) == is_sensitive_before(r1),
        is_sensitive_before(r2),
        Not(is_sensitive_after(r2)),
        in_sandbox(r2),
        # Can the developer still shell_exec r2 under the fixed policy?
        allowed_after_fixed(dev, SHELL_EXEC, r2),
    ]

    s2 = Solver()
    s2.add(fixed_base + fixed_attack)
    result2 = s2.check()
    print(f"  Result: {result2}")
    if result2 == unsat:
        print("  ESCALATION BLOCKED")
        print("  Sticky sensitivity prevents the attacker from treating r2 as")
        print("  non-sensitive in the step-2 check — it was sensitive before, so")
        print("  eff_sens(r2) stays True and shell_exec on r2 stays denied.")
    else:
        print("  Fix failed; attack still succeeds:")
        print(f"    {s2.model()}")
    print()


# ============================================================================
if __name__ == "__main__":
    part_b()
    part_c()
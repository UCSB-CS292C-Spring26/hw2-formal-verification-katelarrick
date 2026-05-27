"""
CS292C Homework 2 — Problem 5 (Bonus): Verified Skill Composition (10 points)
===============================================================================
Verify that two sequentially composed agent skills maintain a filesystem
invariant, then show how a composition bug breaks the invariant.
"""

from z3 import *


# ============================================================================
# Filesystem Model
#
# We model the filesystem as a Z3 array: Array(Int, Int)
#   - Index = file path ID (integer)
#   - Value = content hash (integer)
#
# Two paths are special:
#   INPUT_FILE = 0   (the file Skill A reads)
#   OUTPUT_FILE = 1  (the file Skill B writes to)
# ============================================================================

INPUT_FILE  = 0
OUTPUT_FILE = 1


# ============================================================================
# Part (a): Verify correct composition — 4 pts
#
# Skill A: Reads INPUT_FILE, extracts URLs. Does NOT modify any file.
#   Pre:  true
#   Post: fs_after_A = fs_before_A  (filesystem unchanged)
#
# Skill B: Fetches URLs and writes results to OUTPUT_FILE. Does NOT modify
#          any file other than OUTPUT_FILE.
#   Pre:  true
#   Post: Select(fs_after_B, OUTPUT_FILE) = result_content
#         ∧ ∀p. p ≠ OUTPUT_FILE → Select(fs_after_B, p) = Select(fs_before_B, p)
#
# Composed postcondition:
#   Select(fs_final, INPUT_FILE)  = Select(fs_initial, INPUT_FILE)   [input preserved]
#   ∧ Select(fs_final, OUTPUT_FILE) = result_content                 [output written]
#   ∧ ∀p. p ≠ OUTPUT_FILE → Select(fs_final, p) = Select(fs_initial, p)
#                                                                    [nothing else changed]
#
# Verification strategy: to show that P → Q is valid, check that ¬(P → Q),
# i.e. P ∧ ¬Q, is UNSAT (the standard duality from propositional logic).
# ============================================================================

def verify_correct_composition():
    print("=== Part (a): Correct Composition ===")

    fs_initial     = Array('fs_initial', IntSort(), IntSort())
    fs_after_A     = Array('fs_after_A', IntSort(), IntSort())
    fs_final       = Array('fs_final',   IntSort(), IntSort())
    result_content = Int('result_content')
    p              = Int('p')

    # Skill A postcondition: filesystem unchanged
    skill_A_post = (fs_after_A == fs_initial)

    # Skill B postcondition: OUTPUT_FILE gets result_content;
    # every other path is untouched relative to fs_after_A.
    skill_B_post = And(
        Select(fs_final, OUTPUT_FILE) == result_content,
        ForAll([p], Implies(p != OUTPUT_FILE,
                            Select(fs_final, p) == Select(fs_after_A, p)))
    )

    # Composed postcondition we want to prove:
    #   (1) input file is unchanged end-to-end
    #   (2) output file holds result_content
    #   (3) every other path is unchanged end-to-end
    composed_post = And(
        Select(fs_final, INPUT_FILE)  == Select(fs_initial, INPUT_FILE),
        Select(fs_final, OUTPUT_FILE) == result_content,
        ForAll([p], Implies(p != OUTPUT_FILE,
                            Select(fs_final, p) == Select(fs_initial, p)))
    )

    # Assert premises + negation of conclusion.
    # If UNSAT → the implication is valid (no world satisfies the premises
    # while falsifying the conclusion).
    s = Solver()
    s.add(skill_A_post)
    s.add(skill_B_post)
    s.add(Not(composed_post))

    result = s.check()

    if result == unsat:
        print("  Result: UNSAT")
        print("  => Implication is VALID.")
        print("  => (skill_A_post ∧ skill_B_post) → composed_post holds for all states.")
        print("  => The correct composition preserves the filesystem invariant.")
    elif result == sat:
        print("  Result: SAT  (unexpected — the proof should pass!)")
        print(f"  Counterexample: {s.model()}")
    else:
        print(f"  Result: {result}")
    print()


# ============================================================================
# Part (b): Buggy composition — 3 pts
#
# Bug: Skill B accidentally writes to INPUT_FILE instead of OUTPUT_FILE.
#
# Buggy Skill B postcondition:
#   Select(fs_final, INPUT_FILE) = result_content     ← overwrites input!
#   ∧ ∀p. p ≠ INPUT_FILE → Select(fs_final, p) = Select(fs_after_A, p)
#
# Expected: the composed postcondition FAILS (SAT on the negation).
# Z3 produces a concrete state showing INPUT_FILE clobbered and OUTPUT_FILE
# never written.
# ============================================================================

def verify_buggy_composition():
    print("=== Part (b): Buggy Composition ===")

    fs_initial     = Array('fs_initial', IntSort(), IntSort())
    fs_after_A     = Array('fs_after_A', IntSort(), IntSort())
    fs_final       = Array('fs_final',   IntSort(), IntSort())
    result_content = Int('result_content')
    p              = Int('p')

    skill_A_post = (fs_after_A == fs_initial)

    # BUGGY Skill B: writes result_content to INPUT_FILE (path 0) rather than
    # OUTPUT_FILE (path 1).  The frame condition similarly guards the wrong path.
    buggy_B_post = And(
        Select(fs_final, INPUT_FILE) == result_content,   # ← BUG
        ForAll([p], Implies(p != INPUT_FILE,
                            Select(fs_final, p) == Select(fs_after_A, p)))
    )

    # The contract we want the composed pair to satisfy (same as Part a).
    composed_post = And(
        Select(fs_final, INPUT_FILE)  == Select(fs_initial, INPUT_FILE),
        Select(fs_final, OUTPUT_FILE) == result_content,
        ForAll([p], Implies(p != OUTPUT_FILE,
                            Select(fs_final, p) == Select(fs_initial, p)))
    )

    # Premises are skill_A_post ∧ buggy_B_post.
    # We assert those together with ¬composed_post.
    # SAT → the implication is invalid, i.e. the bug is real.
    s = Solver()
    s.add(skill_A_post)
    s.add(buggy_B_post)
    s.add(Not(composed_post))

    result = s.check()

    if result == sat:
        print("  Result: SAT")
        print("  => Implication is INVALID.  Bug confirmed.")
        m = s.model()

        # Extract concrete witness values for a human-readable explanation.
        initial_input  = m.eval(Select(fs_initial, INPUT_FILE),  model_completion=True)
        initial_output = m.eval(Select(fs_initial, OUTPUT_FILE), model_completion=True)
        final_input    = m.eval(Select(fs_final,   INPUT_FILE),  model_completion=True)
        final_output   = m.eval(Select(fs_final,   OUTPUT_FILE), model_completion=True)
        result_val     = m.eval(result_content, model_completion=True)

        print()
        print("  Counterexample witness:")
        print(f"    result_content              = {result_val}")
        print(f"    fs_initial[INPUT_FILE=0]    = {initial_input}")
        print(f"    fs_initial[OUTPUT_FILE=1]   = {initial_output}")
        print(f"    fs_final[INPUT_FILE=0]      = {final_input}   ← was {initial_input}, now clobbered")
        print(f"    fs_final[OUTPUT_FILE=1]     = {final_output}  ← was never written")
        print()
        print("  Why this breaks the contract:")
        print("    Clause 1 requires fs_final[INPUT_FILE] == fs_initial[INPUT_FILE].")
        print("    But buggy Skill B set fs_final[INPUT_FILE] := result_content,")
        print("    which may differ from the original content.  The input is corrupted.")
        print("    Clause 2 requires fs_final[OUTPUT_FILE] == result_content.")
        print("    But Skill B never touched OUTPUT_FILE, so this also fails.")
    elif result == unsat:
        print("  Result: UNSAT  (unexpected — the bug should be detectable!)")
    else:
        print(f"  Result: {result}")
    print()


# ============================================================================
# Part (c): Real-world connection — 3 pts
#
# [EXPLANATION]
#
# This composition bug occurs frequently in real agent pipelines where multiple
# skills share a working directory but have no formal contract about which paths
# each skill owns. A concrete example: a "summarize repository" agent skill reads
# a project's README (INPUT_FILE) to understand the codebase, then hands off to a
# "write release notes" skill that is supposed to produce a new file called
# RELEASE.md (OUTPUT_FILE). If the second skill constructs its output path from a
# template that accidentally resolves to README (perhaps both live at the project
# root and the skill's default is "the first .md file found"), it overwrites the
# README rather than creating the new file. Each skill reports success from its
# own perspective, but the invariant "README is unchanged" is silently violated —
# exactly the failure mode Part (b) demonstrates.
#
# A runtime monitor (analogous to the DFA monitors in Problem 4) could prevent
# this by maintaining a "read-set" for each skill: any path accessed by an
# upstream skill is recorded, and any downstream file_write whose target appears
# in that read-set is denied unless the skill has explicitly declared that path
# as an output. This is precisely the ReadBeforeWriteMonitor extended with a
# cross-skill ownership check: the monitor refuses the write before the filesystem
# changes, so the invariant holds even when the agent's path-resolution logic is
# wrong.
# ============================================================================


# ============================================================================
if __name__ == "__main__":
    verify_correct_composition()
    verify_buggy_composition()
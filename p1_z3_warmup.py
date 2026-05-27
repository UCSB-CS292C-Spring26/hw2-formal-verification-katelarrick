"""
CS292C Homework 2 — Problem 1: Z3 Warm-Up + EUF Puzzle (15 points)
===================================================================
Complete each function below. Run this file to check your answers.
"""

from z3 import *


# ---------------------------------------------------------------------------
# Part (a) — 3 pts
# Find integers x, y, z such that x + 2y = z, z > 10, x > 0, y > 0.
# ---------------------------------------------------------------------------
def part_a():
    x, y, z = Ints('x y z')
    s = Solver()

    # Added constraints
    s.add(x + 2 * y == z, z > 10, x > 0, y > 0)

    print("=== Part (a) ===")
    if s.check() == sat:
        m = s.model()
        print(f"SAT: x={m[x]}, y={m[y]}, z={m[z]}")
    else:
        print("UNSAT (unexpected!)")
    print()


# ---------------------------------------------------------------------------
# Part (b) — 3 pts
# Prove validity of: ∀x. x > 5 → x > 3
# Hint: A formula F is valid iff ¬F is unsatisfiable.
# ---------------------------------------------------------------------------
def part_b():
    x = Int('x')
    s = Solver()

    # Added the *negation* of the formula and check UNSAT
    # !(x > 5 -> x > 3)  ==  x > 5  /\  x <= 3
    s.add(x > 5, x <= 3)

    print("=== Part (b) ===")
    result = s.check()
    if result == unsat:
        print("Valid! (negation is UNSAT)")
    else:
        print(f"Not valid — counterexample: {s.model()}")
    print()


# ---------------------------------------------------------------------------
# Part (c) — 5 pts: The EUF Puzzle
#
# Formula:  f(f(x)) = x  ∧  f(f(f(x))) = x  ∧  f(x) ≠ x
#
# STEP 1: Check satisfiability with Z3. (2 pts)
#
# STEP 2: Use Z3 to derive WHY the result holds. (3 pts)
#   Write a series of Z3 validity checks that demonstrate the key reasoning
#   steps. For example, from f(f(x)) = x, what can you derive about f(f(f(x)))?
#   Each check should print what it's testing and whether it holds.
#   Hint: Apply f to both sides of the first equation.
# ---------------------------------------------------------------------------
def part_c():
    S = DeclareSort('S')
    x = Const('x', S)
    f = Function('f', S, S)
    s = Solver()

    # Added three constraints
    s.add(f(f(x)) == x, f(f(f(x))) == x, f(x) != x)

    print("=== Part (c) ===")
    result = s.check()
    if result == sat:
        print(f"SAT: {s.model()}")
    else:
        print("UNSAT")

    # Helper: prove a lemma "hyps |= conclusion" by checking that
    # hyps /\ ~conclusion is UNSAT.
    def valid(label, hyps, conclusion):
        v = Solver()
        for h in hyps:
            v.add(h)
        v.add(Not(conclusion))
        print(f"  {label}: {'holds' if v.check() == unsat else 'FAILS'}")

    print("Derivation:")

    # L1: apply f to both sides of f(f(x)) = x  (functional congruence).
    valid("L1  f(f(x)) = x  =>  f(f(f(x))) = f(x)",
          [f(f(x)) == x],
          f(f(f(x))) == f(x))

    # L2: combine L1's conclusion with the second axiom by transitivity.
    valid("L2  f(f(f(x))) = f(x)  /\\  f(f(f(x))) = x  =>  f(x) = x",
          [f(f(f(x))) == f(x), f(f(f(x))) == x],
          f(x) == x)

    # L3: f(x) = x contradicts the third axiom f(x) != x.
    valid("L3  f(x) = x  /\\  f(x) != x  =>  False",
          [f(x) == x, f(x) != x],
          BoolVal(False))

    print()


# ---------------------------------------------------------------------------
# Part (d) — 4 pts: Array Axioms
#
# Prove BOTH axioms (two separate solver checks):
#   (1) Read-over-write HIT:   i = j  →  Select(Store(a, i, v), j) = v
#   (2) Read-over-write MISS:  i ≠ j  →  Select(Store(a, i, v), j) = Select(a, j)
#
# [EXPLAIN] in a comment below: Why are these two axioms together sufficient
# to fully characterize Store/Select behavior? (2–3 sentences)
# ---------------------------------------------------------------------------
def part_d():
    a = Array('a', IntSort(), IntSort())
    i, j, v = Ints('i j v')

    print("=== Part (d) ===")

    # Axiom 1: Read-over-write HIT
    # !(i = j -> Select(Store(a, i, v), j) = v)
    #    ==  i = j  /\  Select(Store(a, i, v), j) != v
    s1 = Solver()
    s1.add(i == j, Select(Store(a, i, v), j) != v)
    r1 = s1.check()
    print(f"Axiom 1 (hit):  {'Valid' if r1 == unsat else 'INVALID'}")

    # Axiom 2: Read-over-write MISS
    # !(i != j -> Select(Store(a, i, v), j) = Select(a, j))
    #    ==  i != j  /\  Select(Store(a, i, v), j) != Select(a, j)
    s2 = Solver()
    s2.add(i != j, Select(Store(a, i, v), j) != Select(a, j))
    r2 = s2.check()
    print(f"Axiom 2 (miss): {'Valid' if r2 == unsat else 'INVALID'}")
    print()

    # EXPLANATION: Together these two axioms fully characterize Store/Select because
    # every read of the form Select(Store(a, i, v), j) falls into exactly one of two
    # mutually exclusive cases: either j = i (HIT — the read returns the just-
    # written value v) or j != i (MISS — the write is irrelevant and the read
    # defers to the underlying array a). Since the two cases are exhaustive,
    # induction on the number of nested Store operations lets us reduce any
    # read over an arbitrary sequence of writes to either a written constant or
    # a Select on the original array, which uniquely determines its value.


# ---------------------------------------------------------------------------
if __name__ == "__main__":
    part_a()
    part_b()
    part_c()
    part_d()
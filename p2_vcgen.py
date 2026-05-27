"""
CS292C Homework 2 — Problem 2: Hoare Logic VCG for IMP (30 points)
===================================================================
Implement weakest-precondition-based verification condition generation
for a simple IMP language, using Z3 to discharge the VCs.

Part (a): Compute wp using your VCG and analyze preconditions with Z3.
          NOTE: Part (a) depends on Part (b). Implement Part (b) first, then come back to Part (a).
Part (b): Implement wp() and verify() below.
Part (c): Discover loop invariants for three programs.
Part (d): Find and fix a bug in a provided invariant.
"""

from z3 import *
from dataclasses import dataclass
from typing import Union

# ============================================================================
# IMP Abstract Syntax Tree
# ============================================================================

@dataclass
class IntConst:
    value: int

@dataclass
class Var:
    name: str

@dataclass
class BinOp:
    """op ∈ {'+', '-', '*'}"""
    op: str
    left: 'AExp'
    right: 'AExp'

AExp = Union[IntConst, Var, BinOp]

@dataclass
class BoolConst:
    value: bool

@dataclass
class Compare:
    """op ∈ {'<', '<=', '>', '>=', '==', '!='}"""
    op: str
    left: AExp
    right: AExp

@dataclass
class ImpNot:
    expr: 'BExp'

@dataclass
class ImpAnd:
    left: 'BExp'
    right: 'BExp'

@dataclass
class ImpOr:
    left: 'BExp'
    right: 'BExp'

BExp = Union[BoolConst, Compare, ImpNot, ImpAnd, ImpOr]

@dataclass
class Assign:
    var: str
    expr: AExp

@dataclass
class Seq:
    s1: 'Stmt'
    s2: 'Stmt'

@dataclass
class If:
    cond: BExp
    then_branch: 'Stmt'
    else_branch: 'Stmt'

@dataclass
class While:
    cond: BExp
    invariant: 'BExp'
    body: 'Stmt'

@dataclass
class Assert:
    cond: BExp

@dataclass
class Assume:
    cond: BExp

Stmt = Union[Assign, Seq, If, While, Assert, Assume]

# ============================================================================
# IMP AST → Z3 Translation
# ============================================================================

_z3_vars: dict[str, ArithRef] = {}

def z3_var(name: str) -> ArithRef:
    if name not in _z3_vars:
        _z3_vars[name] = Int(name)
    return _z3_vars[name]

def aexp_to_z3(e: AExp) -> ArithRef:
    match e:
        case IntConst(v):   return IntVal(v)
        case Var(name):     return z3_var(name)
        case BinOp('+', l, r): return aexp_to_z3(l) + aexp_to_z3(r)
        case BinOp('-', l, r): return aexp_to_z3(l) - aexp_to_z3(r)
        case BinOp('*', l, r): return aexp_to_z3(l) * aexp_to_z3(r)
        case _: raise ValueError(f"Unknown AExp: {e}")

def bexp_to_z3(e: BExp) -> BoolRef:
    match e:
        case BoolConst(v):   return BoolVal(v)
        case Compare(op, l, r):
            lz, rz = aexp_to_z3(l), aexp_to_z3(r)
            return {'<': lz < rz, '<=': lz <= rz, '>': lz > rz,
                    '>=': lz >= rz, '==': lz == rz, '!=': lz != rz}[op]
        case ImpNot(inner):  return z3.Not(bexp_to_z3(inner))
        case ImpAnd(l, r):   return z3.And(bexp_to_z3(l), bexp_to_z3(r))
        case ImpOr(l, r):    return z3.Or(bexp_to_z3(l), bexp_to_z3(r))
        case _: raise ValueError(f"Unknown BExp: {e}")

def z3_substitute_var(formula: ExprRef, var_name: str, replacement: ArithRef) -> ExprRef:
    """Replace every occurrence of z3 variable `var_name` with `replacement`."""
    return substitute(formula, (z3_var(var_name), replacement))


# ============================================================================
# Part (b): Weakest Precondition + VCG — 12 pts
# ============================================================================

side_vcs: list[tuple[str, BoolRef]] = []

def wp(stmt: Stmt, Q: BoolRef) -> BoolRef:
    """
    Compute the weakest precondition of `stmt` w.r.t. postcondition `Q`.
    For while loops, append side VCs (with labels) to the global `side_vcs` list.
    """
    global side_vcs

    match stmt:
        case Assign(var, expr):
            # Substitute every free occurrence of `var` in Q with `expr`.
            # This is the standard assignment axiom: wp(x := e, Q) = Q[x ↦ e]
            return z3_substitute_var(Q, var, aexp_to_z3(expr))

        case Seq(s1, s2):
            # wp(s1; s2, Q) = wp(s1, wp(s2, Q))
            return wp(s1, wp(s2, Q))

        case If(cond, s1, s2):
            # wp(if b then s1 else s2, Q) = (b → wp(s1,Q)) ∧ (¬b → wp(s2,Q))
            b = bexp_to_z3(cond)
            return z3.And(z3.Implies(b, wp(s1, Q)),
                          z3.Implies(z3.Not(b), wp(s2, Q)))

        case While(cond, inv, body):
            # For an annotated loop we trust the provided invariant I and
            # discharge two side VCs:
            #   preservation:  I ∧ b  →  wp(body, I)
            #   postcondition: I ∧ ¬b →  Q
            # The wp of the whole loop (from the perspective of the surrounding
            # code) is simply I — the loop is treated as "assume I holds on entry".
            b = bexp_to_z3(cond)
            I = bexp_to_z3(inv)
            side_vcs.append(("preservation",
                             z3.Implies(z3.And(I, b), wp(body, I))))
            side_vcs.append(("postcondition",
                             z3.Implies(z3.And(I, z3.Not(b)), Q)))
            return I

        case Assert(cond):
            # wp(assert c, Q) = c ∧ Q  (the assertion must hold AND Q must hold)
            return z3.And(bexp_to_z3(cond), Q)

        case Assume(cond):
            # wp(assume c, Q) = c → Q  (only need Q when the assumption fires)
            return z3.Implies(bexp_to_z3(cond), Q)

        case _:
            raise ValueError(f"Unknown statement: {stmt}")


def verify(pre: BExp, stmt: Stmt, post: BExp, label: str = "Program"):
    """
    Verify the Hoare triple {pre} stmt {post}.
    Steps:
      1. Clear side_vcs.
      2. Compute wp(stmt, post).
      3. Check that pre → wp is valid (unsat of negation).
      4. Check each side VC generated by while loops.
      5. Print [PASS]/[FAIL] for every condition, with counterexamples on failure.
    """
    global side_vcs
    side_vcs = []

    pre_z3  = bexp_to_z3(pre)
    post_z3 = bexp_to_z3(post)

    wp_result = wp(stmt, post_z3)

    print(f"=== {label} ===")

    # Collect all VCs: the main entry check plus any loop side conditions.
    all_vcs = [("pre → wp", z3.Implies(pre_z3, wp_result))] + list(side_vcs)

    all_valid = True
    for name, vc in all_vcs:
        s = Solver()
        s.add(z3.Not(vc))
        result = s.check()
        if result == unsat:
            print(f"  [PASS] {name}")
        else:
            all_valid = False
            print(f"  [FAIL] {name}")
            if result == sat:
                print(f"         counterexample: {s.model()}")
            else:
                print(f"         solver returned: {result}")

    print(f"  → {'VERIFIED' if all_valid else 'FAILED'}")
    print()


# ============================================================================
# Test Programs for Part (b) — verify your VCG works on these
# ============================================================================

def test_swap():
    """{ x == a ∧ y == b }  t:=x; x:=y; y:=t  { x == b ∧ y == a }"""
    pre = ImpAnd(Compare('==', Var('x'), Var('a')),
                 Compare('==', Var('y'), Var('b')))
    stmt = Seq(Assign('t', Var('x')),
               Seq(Assign('x', Var('y')), Assign('y', Var('t'))))
    post = ImpAnd(Compare('==', Var('x'), Var('b')),
                  Compare('==', Var('y'), Var('a')))
    verify(pre, stmt, post, "Swap")


def test_abs():
    """{ true }  if x<0 then r:=0-x else r:=x  { r >= 0 ∧ (r==x ∨ r==0-x) }"""
    pre = BoolConst(True)
    stmt = If(Compare('<', Var('x'), IntConst(0)),
              Assign('r', BinOp('-', IntConst(0), Var('x'))),
              Assign('r', Var('x')))
    post = ImpAnd(Compare('>=', Var('r'), IntConst(0)),
                  ImpOr(Compare('==', Var('r'), Var('x')),
                        Compare('==', Var('r'), BinOp('-', IntConst(0), Var('x')))))
    verify(pre, stmt, post, "Absolute Value")


# ============================================================================
# Part (c): Invariant Discovery — 8 pts
# ============================================================================

def test_mult():
    """
    Program C1 — Multiplication by addition:
      { a >= 0 }
      i := 0; r := 0;
      while i < a  invariant ???  do
        r := r + b;  i := i + 1;
      { r == a * b }

    Invariant: 0 <= i <= a  ∧  r == i * b

    How I found it: tracing a few iterations reveals that after k iterations,
    i == k and r == k*b. So r == i*b captures the inductive relationship.
    Bounding i between 0 and a is needed so that when the loop exits (i == a)
    we can conclude r == a*b. Both parts survive init (i=0, r=0), preservation
    (both sides grow by 1 and b respectively), and the postcondition check.
    """
    pre = Compare('>=', Var('a'), IntConst(0))

    inv = ImpAnd(
        ImpAnd(Compare('<=', IntConst(0), Var('i')),
               Compare('<=', Var('i'), Var('a'))),
        Compare('==', Var('r'), BinOp('*', Var('i'), Var('b')))
    )

    body = Seq(Assign('r', BinOp('+', Var('r'), Var('b'))),
               Assign('i', BinOp('+', Var('i'), IntConst(1))))
    stmt = Seq(Assign('i', IntConst(0)),
               Seq(Assign('r', IntConst(0)),
                   While(Compare('<', Var('i'), Var('a')), inv, body)))
    post = Compare('==', Var('r'), BinOp('*', Var('a'), Var('b')))
    verify(pre, stmt, post, "C1: Multiplication by Addition")


def test_add():
    """
    Program C2 — Addition by loop:
      { n >= 0 ∧ m >= 0 }
      i := 0; r := n;
      while i < m  invariant ???  do
        r := r + 1;  i := i + 1;
      { r == n + m }

    Invariant: 0 <= i <= m  ∧  r == n + i

    How I found it: r starts at n and is incremented once per loop iteration,
    so after k iterations r == n + k and i == k. The bound 0 <= i <= m ensures
    that on exit (i == m) we get r == n + m as required.
    """
    pre = ImpAnd(Compare('>=', Var('n'), IntConst(0)),
                 Compare('>=', Var('m'), IntConst(0)))

    inv = ImpAnd(
        ImpAnd(Compare('<=', IntConst(0), Var('i')),
               Compare('<=', Var('i'), Var('m'))),
        Compare('==', Var('r'), BinOp('+', Var('n'), Var('i')))
    )

    body = Seq(Assign('r', BinOp('+', Var('r'), IntConst(1))),
               Assign('i', BinOp('+', Var('i'), IntConst(1))))
    stmt = Seq(Assign('i', IntConst(0)),
               Seq(Assign('r', Var('n')),
                   While(Compare('<', Var('i'), Var('m')), inv, body)))
    post = Compare('==', Var('r'), BinOp('+', Var('n'), Var('m')))
    verify(pre, stmt, post, "C2: Addition by Loop")


def test_sum():
    """
    Program C3 — Sum of 1..n:
      { n >= 1 }
      i := 1; s := 0;
      while i <= n  invariant ???  do
        s := s + i;  i := i + 1;
      { 2 * s == n * (n + 1) }

    Invariant: 1 <= i <= n+1  ∧  2*s == i*(i-1)

    How I found it: after k loop iterations i == k+1 and s == 1+2+...+k == k(k+1)/2,
    i.e. s == (i-1)*i/2. Multiplying through by 2 gives 2*s == (i-1)*i, which
    avoids division and stays in linear-integer arithmetic. The bound 1 <= i <= n+1
    captures that i starts at 1 and can reach n+1 when the loop exits. On exit
    i == n+1, so 2*s == n*(n+1), exactly the postcondition.
    """
    pre = Compare('>=', Var('n'), IntConst(1))

    inv = ImpAnd(
        ImpAnd(Compare('<=', IntConst(1), Var('i')),
               Compare('<=', Var('i'), BinOp('+', Var('n'), IntConst(1)))),
        Compare('==', BinOp('*', IntConst(2), Var('s')),
                BinOp('*', BinOp('-', Var('i'), IntConst(1)), Var('i')))
    )

    body = Seq(Assign('s', BinOp('+', Var('s'), Var('i'))),
               Assign('i', BinOp('+', Var('i'), IntConst(1))))
    stmt = Seq(Assign('i', IntConst(1)),
               Seq(Assign('s', IntConst(0)),
                   While(Compare('<=', Var('i'), Var('n')), inv, body)))
    post = Compare('==', BinOp('*', IntConst(2), Var('s')),
                   BinOp('*', Var('n'), BinOp('+', Var('n'), IntConst(1))))
    verify(pre, stmt, post, "C3: Sum of 1..n")


# ============================================================================
# Part (d): Find the Bug — 4 pts
# ============================================================================

def test_buggy_div():
    """
    Integer division with a BUGGY invariant.
      { x >= 0 ∧ y > 0 }
      q := 0; r := x;
      while r >= y  invariant (q * y + r == x)  do    ← TOO WEAK!
        r := r - y;  q := q + 1;
      { q * y + r == x ∧ 0 <= r ∧ r < y }

    The invariant q * y + r == x is correct but INCOMPLETE.
    It is missing a crucial conjunct. Find it.

    Which VC fails?
      The "postcondition" side VC fails: (inv ∧ ¬guard) → post.
      With only q*y+r==x in the invariant, at loop exit we know r < y (negated
      guard) and q*y+r==x, but nothing forces r >= 0. Z3 finds a counterexample
      such as x=-6, y=-4, r=-6, q=0: the buggy invariant holds (0*(-4)+(-6)==-6)
      and r < y holds (-6 < -4), yet the postcondition requires 0 <= r, which fails.

    Fix: add  r >= 0  to the invariant.
      - Initiation: after q:=0; r:=x, we have r=x >= 0 by precondition. ✓
      - Preservation: the loop guard ensures r >= y > 0 before r := r - y,
        so r_new = r - y >= 0. ✓
      - Postcondition: I ∧ ¬guard now includes r >= 0, satisfying the post. ✓
    """
    pre = ImpAnd(Compare('>=', Var('x'), IntConst(0)),
                 Compare('>', Var('y'), IntConst(0)))

    # BUGGY invariant — intentionally too weak
    inv_buggy = Compare('==',
        BinOp('+', BinOp('*', Var('q'), Var('y')), Var('r')),
        Var('x'))

    body = Seq(Assign('r', BinOp('-', Var('r'), Var('y'))),
               Assign('q', BinOp('+', Var('q'), IntConst(1))))
    stmt = Seq(Assign('q', IntConst(0)),
               Seq(Assign('r', Var('x')),
                   While(Compare('>=', Var('r'), Var('y')),
                         inv_buggy, body)))
    post = ImpAnd(Compare('==',
                       BinOp('+', BinOp('*', Var('q'), Var('y')), Var('r')),
                       Var('x')),
                  ImpAnd(Compare('>=', Var('r'), IntConst(0)),
                         Compare('<', Var('r'), Var('y'))))

    verify(pre, stmt, post, "Buggy Division (should FAIL)")

    # Fixed invariant: add the missing conjunct r >= 0
    inv_fixed = ImpAnd(
        Compare('==',
            BinOp('+', BinOp('*', Var('q'), Var('y')), Var('r')),
            Var('x')),
        Compare('>=', Var('r'), IntConst(0))
    )

    stmt_fixed = Seq(Assign('q', IntConst(0)),
                     Seq(Assign('r', Var('x')),
                         While(Compare('>=', Var('r'), Var('y')),
                               inv_fixed, body)))
    verify(pre, stmt_fixed, post, "Fixed Division (should PASS)")


# ============================================================================
# Part (a): WP Derivation via Z3 — 6 pts
# ============================================================================

def test_wp_derivation():
    """
    Part (a): Use the VCG to compute wp, then check candidate preconditions.

    Program:
      x := x + 1;
      if x > 0 then y := x * 2 else y := 0 - x;
    Postcondition: { y > 0 }

    Manual derivation:
      wp(y := x*2,   y>0) = 2*x > 0             (x > 0, same as guard)
      wp(y := 0-x,   y>0) = 0-x > 0  =>  x < 0
      wp(if x>0 ..., y>0) = (x>0 → 2*x>0) ∧ (x<=0 → x<0)
                           = True ∧ (x<=0 → x<0)
                           = (x<0 ∨ x>0)
                           = x ≠ 0  (over ℤ)
      wp(x := x+1,   x≠0) = (x+1) ≠ 0  =>  x ≠ -1

    So the true weakest precondition is  x ≠ -1.

    Candidates:
      x >= 0:  VALID   — any x >= 0 satisfies x ≠ -1.
      x >= -1: INVALID — x = -1 is allowed by this precondition but violates wp.
      x == -1: INVALID — this forces exactly the failing case.
    """
    print("=== Part (a): WP Derivation ===")

    stmt = Seq(
        Assign('x', BinOp('+', Var('x'), IntConst(1))),
        If(Compare('>', Var('x'), IntConst(0)),
           Assign('y', BinOp('*', Var('x'), IntConst(2))),
           Assign('y', BinOp('-', IntConst(0), Var('x'))))
    )
    post = Compare('>', Var('y'), IntConst(0))

    wp_result = wp(stmt, bexp_to_z3(post))
    print(f"  wp = {wp_result}")
    print(f"  simplified wp = {simplify(wp_result)}")

    candidates = [
        ("x >= 0",  z3_var('x') >= 0),
        ("x >= -1", z3_var('x') >= -1),
        ("x == -1", z3_var('x') == -1),
    ]
    for name, pre in candidates:
        s = Solver()
        s.add(Not(Implies(pre, wp_result)))
        result = s.check()
        valid = (result == unsat)
        if valid:
            print(f"  {name}: VALID")
        else:
            cex = f"   counterexample: {s.model()}" if result == sat else ""
            print(f"  {name}: INVALID{cex}")

    # x >= 0  is VALID:  x >= 0 implies x != -1, so the precondition is strong
    #   enough. After x := x+1, x becomes >= 1 > 0, the then-branch fires, and
    #   y = 2*x >= 2 > 0.
    #
    # x >= -1 is INVALID: x = -1 is in this set. After x := x+1, x = 0, the
    #   condition x > 0 is false, so the else-branch fires and y = 0 - 0 = 0,
    #   violating y > 0.
    #
    # x == -1 is INVALID: same failing trace — this pre pins x to exactly -1.
    print()


# ============================================================================
if __name__ == "__main__":
    print("=" * 60)
    print("Part (b): VCG Correctness Tests")
    print("=" * 60)
    test_swap()
    test_abs()

    print("=" * 60)
    print("Part (a): WP Derivation via Z3")
    print("=" * 60)
    test_wp_derivation()

    print("=" * 60)
    print("Part (c): Invariant Discovery")
    print("=" * 60)
    test_mult()
    test_add()
    test_sum()

    print("=" * 60)
    print("Part (d): Find the Bug")
    print("=" * 60)
    test_buggy_div()
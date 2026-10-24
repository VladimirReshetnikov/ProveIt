# Natural nonnegative masks and smaller exact checker graphs

All visible variables and hidden witnesses in this note are nonnegative
integers. All subtraction is ordinary integer subtraction. The following
are exact local graphs for the existing direct annotated checker, without
changing its numerical coding. They are not a compilation of the full
checker and are not a new small consistency equation by themselves.

## The two useful principles

First, for natural x_1,...,x_k,

    x_1+...+x_k=0 iff every x_i=0.

Thus for any integer polynomial F, the nonnegative polynomial

    (x_1+...+x_k)F^2

vanishes exactly when all x_i vanish or F vanishes. Squaring each x_i is
unnecessary. If F is linear, this replacement lowers degree from four to
three and shortens the literal tree. This uses the natural domain.

Second, the joint predecessor/zero-test graph has the quadratic equation

    Z(n,b,p)=(n+b-p-1)^2+bp=0.

Both summands are nonnegative. A zero forces bp=0 and n+b=p+1. If b=0,
then n=p+1>=1 and p=n-1. If p=0, then n+b=1, so either (n,b)=(1,0)
or (n,b)=(0,1). Conversely these cases all give zero. Therefore

    Z(n,b,p)=0 iff p=pred(n) and b=1 when n=0, otherwise b=0.

This is pointwise equality of relations, not just an existential projection.
Hiding p gives the exact zero-test graph with one natural witness. If both
outputs are already stored, Z uses no additional witness. Hiding b gives
an alternative quadratic predecessor graph with one natural witness.

## Predecessor without a new witness

The single quadratic residual

    R(n,p)=(n+p)(n-p-1)

vanishes iff n=p=0 or n=p+1, exactly p=pred(n). It is not nonnegative,
so it cannot be added unsquared to a nonnegative aggregate. Two safe forms
are R^2 (quartic) and

    C(n,p)=(n+p)(n-p-1)^2,

which is nonnegative, cubic, and has the same zero set. Both need no hidden
witness beyond the visible predecessor output. The cubic is a single
ordinary polynomial, not a degree upper bound obtained after some omitted
conversion.

## Exact conditional graphs

For natural n,a,b,c and a natural slack s, the quartic

    I4=n(c-b)^2+[(c-a)(n-s-1)]^2

vanishes for some s iff c=a when n=0 and c=b when n>0. At n=0, n-s-1
is strictly negative and nonzero, forcing c=a. At n>0, the first term
forces c=b. Completeness uses s=pred(n). Nonnegativity of n allows its
factor to remain unsquared, saving one tree operation relative to the
incoming quartic.

There is also a cubic tradeoff with two witnesses t,p:

    I3=Z(n,t,p)+t(c-a)^2+n(c-b)^2.

All summands are nonnegative. The first determines the exact zero bit t and
predecessor p. At n=0, t=1 forces c=a; at n>0 the n-weighted term forces
c=b. The converse chooses the canonical t,p. This has exact degree three,
with one more hidden coordinate than I4.

## Existing max-square pairing retained

For natural z,a,b,t,s let

    Q(z,a,b;t,s)=t(t-1)
        +[a-b-s+t(2s+1)]^2
        +[4(z-a-b)-(a+b+s)^2+t]^2.

This is the incoming Joint Guards two-witness quartic. Its universal proof
is retained: t(t-1)>=0 for integer t, so a zero forces t=0 or1. At t=0,
a=b+s and z=a^2+a+b. At t=1, b=a+s+1 and z=b^2+a. These are precisely
Mathlib's max-square pairing cases. Completeness uses the corresponding
nonnegative difference slack. Thus Q is nonnegative and represents the
same existing pair code; no Cantor recoding is being substituted.

For either tree projection replace the incoming predecessor term by C:

    Q(p,a,b;t,s)+C(n,p).

Hiding p,b,t,s gives treeLeft; hiding p,a,t,s gives treeRight, also the
actual guarded listTail. At n=0, p=0 and the pair graph forces a=b=0.
Each graph still has four hidden coordinates and degree four.

## Exact list head

The actual function is zero at nil and otherwise is the first component
of unpair(n-1), plus one; the successor marks a found entry. Define

    Head=Q(p,a,b;t,s)
          +(n+p+c)(n-p-1)^2+n(c-a-1)^2.

At a zero of this nonnegative polynomial with n=0, the middle term is
(p+c)(p+1)^2, so p=c=0. Pairing then gives a=b=0. With n>0, the middle
term forces p=n-1, and the last term forces c=a+1. Pairing identifies a
as the actual left component. Conversely, choose the canonical unpair and
pairing witnesses for n>0, or all zeros at nil. This proves the exact
unbounded graph with five hidden coordinates and degree four. In particular,
a nonempty cell with stored head zero yields one, not zero.

## Literal metrics

Every arithmetic operation is a binary addition, subtraction or
multiplication in the supplied expression tree. A square is literal
multiplication with both operand subtrees counted. As in the incoming
comparison, a final addition of zero is counted. Shared-DAG counts are
reported separately and are never substituted for tree counts.

| Local graph | Incoming Joint Guards aux / degree / tree ops | New aux / degree / tree ops |
|---|---:|---:|
| Predecessor, nonnegative aggregate | 0 / 4 / 10 | 0 / 3 / 8 |
| Zero test | 1 / 4 / 14 | 1 / 2 / 10 |
| Tree left/right and list tail | 4 / 4 / 49 | 4 / 4 / 47 |
| Conditional | 1 / 4 / 16 | 1 / 4 / 15 |
| Conditional, cubic tradeoff | no cubic row | 2 / 3 / 20 |
| Actual list head | 5 / 4 / 59 | 5 / 4 / 55 |

The strict square R^2 predecessor form has degree four and ten tree
operations, matching the incoming tree count. Its advantage is a single
quadratic residual rather than two independently squared residuals; it is
not falsely reported as a tree-operation improvement over the already
factored incoming formula.

For comparison, the checked repository baseline before the incoming
improvements reports zero-test 1/4/20, conditional 2/4/32, and actual head
7/4/76. Those baseline counts appear in QUADRATIC_GUARDED_GRAPHS.md at the
pinned repository head c1a102936aca437e9999530a0111e6ddab56dc6d. The new
claims here are mathematical graph identities and exact finite expression
counts, not Lean-checked replacement modules or a final compiler-size bound.

## Reproduction and checks

Run `python3 build_and_verify.py`, also valid with `python3 -O`. It needs
only Python's standard library. The emitted JSON contains every literal
expression and its full expanded integer-coefficient polynomial, degree,
support, tree and DAG operation count. The checker independently compares
AST and sparse evaluations and performs 784,390 finite controls covering
the nil/found-zero cases, conditional soundness/completeness, joint zero
and predecessor graph, and pairing-based heads. Explicit runtime checks
survive optimized Python mode. The universal proofs above establish the
infinite relations; finite controls are supplementary.

The numerical domain restriction is substantive. The new graph Z does not
assert the same relation over arbitrary integer p,b, and the natural sums
used as masks may cancel if signed coordinates are introduced. Any later
integer-domain conversion must preserve these naturalness conditions.

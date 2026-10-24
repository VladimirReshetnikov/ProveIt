# Quadratic constraints on shared natural registers

The new attachment compiler in `QuadraticRegisterSystem.lean` stores a finite
family of supplied quadratic residuals over a natural arithmetic program's
inputs and registers. It squares those rows directly and combines them with
the program's local gate equations. Additional arithmetic gates are unnecessary
for evaluating a logical constraint before it is squared.

`System.representation` proves that the gate witnesses equal the actual
nonnegative program values and that every supplied residual vanishes. Its
witness count is exactly the existing register count. `System.scopedRep` also
hides an explicit block of auxiliary natural inputs, adding exactly that block's
size to the witness count. Both constructions retain degree at most four.
The executable `syntaxDegree` bound certifies that each supplied row is
quadratic without normalizing a multivariate polynomial.

## Exact max-square pairing used by the direct checker

`QuadraticNatPairing.lean` represents Mathlib's `Nat.pair` and `Nat.unpair`,
used by the annotated proof and rename checkers. This is separate from the
older EnumPerm Cantor encoding.

For natural `z,a,b`, introduce natural witnesses `t,s,m` and four residuals:

```
f0 = t*(t-1)
f1 = m-((1-t)*b+t*a)
f2 = b+t*s-a-(1-t)*(s+1)
f3 = z-m*m-a-t*b
```

All subtraction here is integer polynomial subtraction. Then

```
f0*f0+f1*f1+f2*f2+f3*f3 = 0
```

has natural witnesses `t,s,m` exactly when `z=Nat.pair a b`.

The selector equation forces `t=0` or `t=1`. In the first branch, the remaining
equations give `m=b`, `b=a+s+1`, and `z=b*b+a`. In the second they give `m=a`,
`a=b+s`, and `z=a*a+a+b`. Completeness chooses the appropriate branch and the
natural slack `b-a-1` or `a-b`. Soundness and completeness are universal Lean
theorems with no size assumptions; the zero and equal-component cases are
included.

The pairing graph has three auxiliary witnesses. An inverse projection adds
the missing component as a fourth witness and uses the proved inverse-pairing
identities. Thus each local graph uses six natural variables in total and has
degree at most four. The supplied expression recipe has exactly 46 binary
operations, including the sum constructor's final addition of zero. This is
an exact constructor count, not an optimality assertion.

## Guarded quotient and remainder

`QuadraticDivMod.lean` represents the exact predicate

```
b>0 and q=n/b and r=n%b.
```

It introduces just one natural slack `s` and squares the two quadratic rows

```
n-(q*b+r),  b-(r+s+1).
```

The first is Euclidean reconstruction and the second is the remainder bound.
The positive-denominator guard is part of the predicate, so the correctness
theorem needs no external guard hypothesis. A zero denominator has no witness.
The graph uses five natural variables in total, degree at most four, and
exactly 16 expression-tree operations.

## Measured local comparison

The earlier output-equality circuits remain available as checked baselines:

| Local graph | Earlier shared-output compiler | Direct quadratic attachment |
|---|---:|---:|
| `Nat.unpair` projection | 41 witnesses, ≤238 operations | 4 witnesses, 46 operations |
| guarded joint quotient/remainder | 23 witnesses, ≤136 operations | 1 witness, 16 operations |

Both columns have degree at most four. `RegisterNatPairing.lean` contains the
first baseline; `RegisterDivMod.lean` retains the second separately. These
counts concern the local graphs. Composing a whole checker requires its own
shared input scopes, branch/loop compiler, and size certificate.

## Verification and remaining scope

`checks/QuadraticRegisterSystem.lean` proves the complete natural-zero graph
equivalences, explicitly rules out zero-denominator witnesses, and audits
twenty theorem dependencies. All use only `propext`, `Classical.choice`, and
`Quot.sound`. The source modules and checks compile cleanly. Program and row
data are supplied in `Type`; no polynomial coefficient data are extracted
using `Classical.choose`, and no new axiom or admitted lemma is introduced.

The generic attachment layer preserves the supplied program registers; its
local examples use an empty program because their source residuals are already
quadratic. The polynomial semantics use Mathlib's ordinary `MvPolynomial`
interface while the expression recipes and their constructors are executable.

These are concrete arithmetic building blocks for the direct checker. They
introduce no smaller closed consistency equation and do not establish the
internal object-ZFC unsolvability/consistency biconditional. That interpretation
and the complete checker compiler remain separate obligations.

The subsequent [composable tree/list graphs](QUADRATIC_TREE_CODE_GRAPHS.md)
attach these schemes to existing register slots and cover the actual numeric
checker's tree projections and list tail with5 witnesses/62 operations each.
The comparison retains the previous witness/operation/degree tradeoff.

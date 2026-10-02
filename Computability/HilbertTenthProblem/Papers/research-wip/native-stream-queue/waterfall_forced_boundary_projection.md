# Forced-boundary projection for the Waterfall quadratic

The complete seven-step certificate drops from **245 to 107 natural witnesses**,
**39 to 20 squared affine residuals**, and **14 to 6 unsquared nonnegative
products**. A fully emitted arithmetic schedule drops from **1558 operations
(430M+1128A) to 720 (203M+517A)**. Both complete polynomials have exact degree
two. The parameters remain `(L0,R0,C,tau)`; this is an externally fixed-horizon
family, not a new universal fixed-arity equation or an improvement to the
87-operation universal bound.

The [compiler](waterfall_forced_boundary_projection.py) emits all retained
coordinates, affine rows, product factors, restoration formulas, expanded
polynomial coefficients and binary arithmetic gates. The [receipt](waterfall_forced_boundary_projection.json)
contains the complete seven-step output and its zero at `(6,0,189,428)`,
plus ledgers and checks for other horizons. This transforms the report's
actual source; it does not replace a claimed compiler with a smaller toy.

## Pinned parent and input contract

The parent is `waterfall-diophantine/replay/grouped_quadratic.py` in
`Waterfall_Diophantine_Certificates.zip`, delivered at `24a743255`.
Archive SHA-256 is `b5d3ee90f9631695afc3c6f34f765b617eb9c631c65ab32705cf3d0e8811a9fc`;
source SHA-256 is `506c7d8505e2076628b351a016104a3ad851a4178fa664709ae87774a645dc7f`.
The compiler authenticates both before loading, and recovers the archive
from its arrival commit if an intake later removes the working copy.

The source machine starts in `(A,0)` with natural half tapes `L0,R0`.
Its unique missing instruction is `(J,1)`. At each of the externally fixed
`k` steps the parent has 29 natural selectors and two direction triples
`(QL,rL,YL),(QR,rR,YR)`. Five affine equations enforce one-hot selection,
source state/head and input tapes; two nonnegative products kill the inactive
triple. Four terminal equations require the halt control, exact Waterfall
firing count `C` and timestamp `tau=1+2C+7k`.

The parent theorem's uniqueness is for **natural** complete witnesses. Natural
one-hot selectors choose one actual instruction, and the next source-head
equation (or final halt-head equation) forces the active remainder to be a
bit. No signed or fractional selector interpretation is used here. The
report's macrostep theorem supplies the Waterfall event interpretation;
this projection only changes its complete bounded polynomial.

## Forced first step

The initial state/head equations and natural one-hot row force the unique
instruction `A0 -> (write 0, right, B)`. Replace all first selectors by its
unit vector, set `QL0=rL0=YL0=0`, and set `YR0=L0`. These are exactly the
values forced by the inactive-direction product and left-input equation.
All restored values are nonnegative affine expressions on every natural
retained assignment, including assignments that are not zeros.

This removes 33 witnesses, four identically zero affine residuals and both
first-step products. If `k>=2`, additionally restore `rR0=S1`, where `S1`
is the next step's source-head selector sum. Delete its now-identically-zero
head-link equation. The sum has nonnegative coefficients, so this removes
one more natural witness without needing to assume that the next selectors
are already one-hot. On a parent zero, the retained next selector row also
forces `S1` to be the correct bit.

Thus prefix-only mode has

| Horizon | Witnesses | Affine squares | Products |
|---|---:|---:|---:|
| `k=1` | `35k-33` | `5k` | `2k-2` |
| `k>=2` | `35k-34` | `5k-1` | `2k-2` |

No assertion that a one-, two- or three-step halt exists is made. The terminal
conditions remain in those prefix-only polynomials.

## Three forced instructions before halt

Reading the actual 29-instruction table, the only instruction entering J is
I1, the only instruction entering I is H0, and the only one entering H is G0.
Consequently every parent natural zero with at least three preceding steps
ends in

```text
G0 -> (write 0, left, H), popped bit 0;
H0 -> (write 1, left, I), popped bit 1;
I1 -> (write 1, left, J), popped bit 1.
```

The first two popped bits are forced by the next instruction's source bit;
the last is forced by the terminal halt-head row. Fix all three selector
banks, kill their right-direction triples, and restore each active `YL` as
the preceding right-output expression. That expression uses only nonnegative
coefficients, so these replacements are natural on the full retained orthant.

Write `QG,QH,QI` for the three left quotients. The two internal left-input
equations force

```text
QH = 2QI+1;
QG = 2QH+1 = 4QI+3.
```

Erase `QG,QH` and these two equations. Only `QI` remains as a suffix witness.
If the half tapes entering G0 are `(X,Y)`, the remaining boundary equations
require `X=8QI+6` and produce final half tapes `(QI,8Y+3)`. State and head
links at the suffix entrance remain; they are essential to connect the
forced suffix to the arbitrary intervening computation.

For disjoint boundaries, `k>=4`, the complete result is

```text
witnesses:       35k-138;
affine squares:   5k-15;
products:         2k-8;
exact degree:         2.
```

There are 34 erased prefix coordinates and 104 erased suffix coordinates;
five prefix and fourteen suffix affine rows vanish. Both sides remove their
two products per fixed step. At `k=4`, the suffix-entrance state equation is
the nonzero constant `6-1=5`; it is retained. The resulting five-square,
two-witness polynomial therefore has no zero. The compiler rejects `ends`
mode for `k<4` instead of combining overlapping substitutions.

## Exact identity and complete witness correspondence

Let `rho` be the printed affine restoration of erased coordinates, and let
`P_k` be the original polynomial. Every deleted affine residual becomes the
zero polynomial under `rho`. Every deleted product has a factor that becomes
identically zero. All other rows and factors are obtained by literal affine
substitution. Therefore, as an identity over the integer polynomial ring,

`P_k(rho(v)) = P_reduced(v)`.

This holds even on signed assignments away from the zero set. No cross-term
or conditional correction has been dropped. All coefficients in every
restoration form are nonnegative, so `rho` maps every retained natural
assignment to a complete natural parent assignment.

Conversely, every parent natural zero has the forced initial selector,
forced suffix selectors and all the coordinate values derived above.
Deleting those coordinates and restoring them is the identity on parent
zeros. The polynomial identity makes every reduced natural zero lift to a
parent zero. Projection and restoration are thus inverse bijections of
the complete natural zero sets for each supplied parameter tuple. First
halting, `C`, `tau`, and uniqueness all transfer. This proof does not assert
that arbitrary real or signed parent zeros obey the forced selectors.

The affine substitutions preserve affine residuals and nonnegative product
factors, so the result remains a quadratic nonnegative on the entire real
nonnegative orthant. The coefficient of `tau²` is still 1, proving exact
degree two rather than only an upper bound.

## Arithmetic ledger and replay

The same deterministic evaluator is used for parent and projected forms.
It evaluates canonical affine rows with common-subexpression sharing, then
squares residuals, evaluates the retained products and sums the results.
Every binary addition, subtraction and multiplication costs one operation,
including multiplication by an integer coefficient other than 0 or 1.
Integer constants and copies are free. There is no division, variable power,
comparison oracle or unit-cost linear-form instruction. All emitted gates
are used by the output. These are achieved literal schedules, not optimized
lower bounds or counts of only the changed fragment.

| Horizon and mode | Witnesses | Squares/products | M | A | Total |
|---|---:|---:|---:|---:|---:|
| 7, parent | 245 | 39/14 | 430 | 1128 | 1558 |
| 7, prefix | 211 | 34/12 | 373 | 984 | 1357 |
| 7, both ends | 107 | 20/6 | 203 | 517 | 720 |
| 10, parent | 350 | 54/20 | 613 | 1617 | 2230 |
| 10, both ends | 212 | 35/12 | 386 | 1006 | 1392 |

The seven-step gain is 838 operations, including 227 multiplications and
611 additions/subtractions. Expanded monomials drop from 9,484 to 3,997.
These figures apply to the whole `k=7` relation for arbitrary natural
`L0,R0,C,tau`, not merely the displayed zero.

Run the script without `--write` to compare a fresh replay with the saved
receipt, or use `--write` to regenerate it. Public `build`, `checked`,
`evaluate`, `restore_assignment`, `project_assignment` and
`canonical_assignment` validate exact types and complete coordinate sets;
exports are defensive copies of privately cached canonical data. Formal
signed graph evaluation is explicitly requested with `signed=True`.
Low-level affine arithmetic helpers are not untrusted-data entry points.

The supplied replay includes 252 signed graph/expanded-polynomial checks,
168 full natural lifts, 16 actual first-halt witness bijections, 109 changed
witness/count/time rejections and 352 malformed public calls. The all-tuples
identity and zero-bijection proof above establish the transformation; the
finite checks exercise its implementation. The horizon still controls arity,
and the ordinary-program-to-half-tapes loader is not charged by this family.

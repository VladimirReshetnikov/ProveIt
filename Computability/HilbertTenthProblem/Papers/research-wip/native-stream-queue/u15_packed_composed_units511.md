# Complete direct U15 in 511 operations, with a 523-operation degree alternative

The [composed compiler](u15_packed_composed_units511.py) and
[full-source receipt](u15_packed_composed_units511.json) reduce the direct U15
ordinary-input equation to **511=211M+300A operations**, with **87 positive
witnesses,25 comparisons and exact degree4881**. The raw natural half-tape
interface costs **323=118M+205A**, with51 positive witnesses,10 comparisons
and exact degree3464.

An optional ungrouped source costs **523=211M+312A** ordinary or
**325=118M+207A** raw and retains exact degree1936. It is the identical
polynomial to the532 and536 ancestors. The cheaper grouped sources preserve
the full integer zero sets; their polynomial values away from zeros change.
The separate universal87-operation benchmark is unchanged.

| Interface and mode | Certificate | Complete polynomial | Comparisons | Exact degree |
|---|---:|---:|---:|---:|
| Raw, ungrouped SOS |293=107M+186A|325=118M+207A|11|1936|
| Raw, grouped SOS |294=108M+186A|323=118M+205A|10|3464|
| Ordinary, ungrouped SOS |431=180M+251A|523=211M+312A|31|1936|
| Ordinary, grouped anchor |437=186M+251A|511=211M+300A|25|4881|

Every emitted binary addition, subtraction or multiplication is charged,
including fixed-coefficient multiplication and the complete finalizer.
Constants and copies are free. All emitted gates reach the final output.

## Three composable reductions

The [factored-index532 parent](u15_packed_factored_index532.md) already saves
four additions from536 through the exact identity

```
F0+q*(F1+q*(F2+q*Z))
  = (q-1)*(A+1+(q+1)*(B+(q-1)*Z)),
```

where `F1=A-Z`, `F2=B-Z` and `F0=q-A-F2-1` are computed fields. Its
shift from `A=scaled_A+12` to `A+1=scaled_A+13` costs no extra gate.

The [binary affine transformer](u15_joint_binary_affine_rewrite.md) replaces
the99-gate controller block by90 gates. Shared signed magnitude-bit sums and
two Horner chains preserve all seven exact affine forms in the29 edge hats.
The eight-multiplication and one-addition saving gives the complete523/325
ungrouped sources, with unchanged residuals and complete SOS polynomial.

Finally, the [unit-product transformer](u15_packed_unit_product524.md) saves
twelve ordinary or two raw operations. It combines the main and auxiliary
norm equations of each native kernel and, for ordinary input, the one
remaining loader checksum. Both transformations are applied to the actual
complete parent packet under their checked source contracts.

Thus the ordinary route is `536 -> 532 -> 523 -> 511`; the raw route is
`338 -> 334 -> 325 -> 323`. Relative to the earlier611 construction,
the full ordinary saving is100 operations.

## Why the unit equations may be combined

For each native kernel let

```
Delta = a*a+4*a+3 = (a+2)^2-1,
N = d*d-Delta*c*c,
H = T*T*(V*V-y*y)+y*y.
```

These are the actual main and auxiliary norm factors, with
`T=i*c*c`, `V=H17` and the paid native registers for a,c,d,y. The original
two comparisons are exactly `N=1` and `H=1`.

On every integer tuple, `Delta mod4` is0 or3. Consequently
`N mod4` is never3: it is a square when Delta is0, and a sum of two
squares when Delta is3. Also `H mod4` is `y*y` when T is even and
`V*V` when T is odd. Neither N nor H can equal−1. These conclusions
do not use native typing, a power assertion, positivity or any other equation.

The raw interface has two such factors. Ordinary input has six, from the
geometry loader, input AND loader and history AND kernel. Define the loader
checksum factor

```
C = input__and__q - input__and__bs_Q.
```

Its original comparison is `C=1`. This is the only factor that has no
independent negative-unit exclusion. Let U be the product of the protected
norm factors and, in ordinary mode, C. If `U=1`, every integer factor is
either1 or−1. The protected factors must all be1; therefore C is also1.
Conversely, all original unit equations imply U=1. This proves equivalence
on the entire supplied integer domain, before the positive-domain theorem
is invoked.

The source reuses each private `Ac2+1` gate as the subtraction `d*d-Ac2`,
and each private `1-y*y` gate as the addition `L17+y*y`. The loader checksum
similarly repurposes its private offset gate. None of the replaced private offset
registers has another live source consumer. Combining seven ordinary factors needs
six products, then six fewer comparison finalizers; six multiplications
move from squares to the product, while twelve additions disappear. Raw
mode combines two factors and saves two additions.

## Complete finalizers and zero-set proof

Let S be the sum of squares of every retained residual, excluding the new
single comparison `U=1`. The compiler emits

```
raw grouped:       S+(U-1)^2,
ordinary grouped:  U*(1+S)-1.
```

For raw mode, zero forces S=0 and U=1 by nonnegativity. For the ordinary
anchor, `1+S` is a positive integer. Its product with U is1 only when both
are1, again forcing S=0 and U=1. The original unit comparisons then follow
from the integer argument above. The converse is immediate. Every other
parent residual is unchanged, so the correspondence is the identity on
the complete supplied coordinates, in both directions.

The ordinary output need not be nonnegative away from its integer zeros.
No identity between its off-zero values and the original SOS is asserted.
The grouped equivalence is an integer statement, not a real-zero theorem.

The complete positive ordinary input relation and its four fixed positive
program parameters retain the inherited effective valid-program-slice
qualification. Raw `L0,R0` remain natural; all other supplied coordinates
are positive. There is no external time horizon, discarded input loader,
or unpaid history decoder. The earlier fifteen-field positive restoration
to611 continues to apply on the preserved zero set.

## Exact degree and the retained tradeoff

The ungrouped identity transfers exact degree1936. A separate leading-term
check on each actual523/325 source also proves a nonzero degree1936 part
independent of the fixed program numerals.

The grouped product changes degree. Its main norm has a known cancellation:
with `L=X+ga*(4*a+3)` and the actual `d=a*c+L`,

```
d*d-(a*a+4*a+3)*c*c
  = 2*a*c*L+L*L-(4*a+3)*c*c.
```

The source guard authenticates every row used in this identity before the
degree audit substitutes it. Formal degree propagation through this equal
expression bounds the true degree; nonzero evaluated leading coefficients
modulo two primes attain that bound. Their dependency sets exclude all fixed
program numerals. The actual grouped sources therefore have exact degrees
3464 raw and4881 ordinary on every valid fixed-program slice.

The literal gates alone give looser upper bounds3604 and5019. The ledger
records those bounds and conservatively keeps `exact_degree_claimed=False`;
the attached refined certificates prove the exact degrees. The unit helper
also emits the alternate finalizers: raw anchor degree3668 and ordinary
grouped SOS degree5890, at the same operation counts. The defaults select
the lower-degree form in each interface. The523/1936 source remains available
when the lower degree matters more than twelve operations.

## Canonical interfaces and replay

`build(ordinary=False, grouped=True)` returns the canonical raw grouped
packet. `ordinary=True` selects the ordinary input; `grouped=False` selects
the unchanged SOS polynomial. Both flags require exact Booleans.
`canonical_parent()` returns532. `checked`, `polynomial_source`, `evaluate`
and `identity` enforce complete canonical metadata, copied public results
and exact integer assignments. `signed=True` permits algebraic integer
evaluation. In grouped mode, `identity` checks the displayed complete-output
formula and every parent residual map, rather than claiming equal off-zero
outputs.

The three source dependencies and inherited lineage are authenticated before
construction and on warm-cache access. The exact affine helper updates all
outgoing cut names, including metadata. The unit helper archives the earlier
ancestor comparison map as `pre_unit_ancestor_comparison_map` and provides
current `unit_factors` and `unit_retained_comparison_map` covering every
original comparison. Historical truth reconstruction remains proof-only.

From the maintained directory:

```sh
python u15_packed_composed_units511.py
```

An isolated copy may use `--root` for the dependency directory. Default replay
compares the complete saved receipt with exact types; `--write` explicitly
regenerates it. The author replay checks96 complete output identities,
48 signed cases,2,016 original residuals,382 malformed calls and eight
defensive-copy boundaries. Exact algebra and integer-unit proofs establish
the universal claims; these finite checks only corroborate them. No
astronomical Pell witness or complete imported universal zero is materialized.

The [independent review](review_u15_composed511.md), [portable checker](review_u15_composed511.py) and [receipt](review_u15_composed511.json) check all four complete modes, current residual maps, exact degrees, strict APIs and warm dependency authentication. Eight full modular coefficient evaluations independently attain the four degree claims. A second bounded proofread checked the unit argument, domains and degree statements. No unresolved finding remains.

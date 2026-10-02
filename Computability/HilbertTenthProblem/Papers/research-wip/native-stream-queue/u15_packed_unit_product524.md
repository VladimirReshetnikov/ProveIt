# Complete native-unit finalization: 524 ordinary / 336 raw operations

Grouping the actual native norm comparisons and the ordinary loader's sole checksum lowers the complete [536-operation U15 compiler](u15_packed_joint_affine536.md) to **524=219M+305A operations**. Its87 positive witnesses and ordinary-input interface are unchanged. The raw natural half-tape form becomes **336=126M+210A**, retaining51 positive witnesses. Both transformations preserve the **entire supplied integer zero set**, and hence the declared positive/natural zero set, on exactly the same coordinates.

This is a paid transfer of the integer-unit method already used in [the projective norm/checksum construction](group_projective_unit_product.md). It supplies the actual complete U15 sources, guarded local rewrite, exact off-zero formulas and source-specific degree certificates. It does not improve the separate87-operation universal polynomial benchmark.

| Interface | Certificate source | Equations | Witnesses | Complete polynomial |
|---|---:|---:|---:|---:|
| Raw natural half tapes |307=116M+191A|10|51 positive|336=126M+210A|
| Ordinary positive input |450=194M+256A|25|87 positive|524=219M+305A|

All additions, subtractions and multiplications, including fixed coefficients, are paid. Constants and copies are free. Every emitted gate reaches the complete output. No ordinary input, acceptance, synchronization, native typing or unbounded-duration component has been removed.

## 1. The two unconditional negative-unit exclusions

For each of the actual native units, let

```
Delta=(a+2)^2−1,
T=i*c^2,
V=the actual H17 source expression,
N=d^2−Delta*c^2,
H=T^2*(V^2−y^2)+y^2.
```

The source computes Delta as a²+4a+3 and uses the actual square T², not a value substituted from the strong auxiliary equation. The old comparisons are exactly N=1 and H=1.

For arbitrary integers, Delta is0 or3 modulo4. Consequently N is congruent either to d² or to d²+c² modulo4, giving only0,1,2. It cannot equal−1. For H, T² is0 or1 modulo4; H is therefore congruent respectively to y² or V². It too cannot equal−1. These arguments require neither positive coordinates nor a native equation, dyadic radix, Pell classification, witness normalization or valid computation.

The raw source has one native history unit, hence two protected factors. The ordinary source has geometry, loader-AND and history-AND units, hence six protected factors. It also retains the checksum comparison

```
F0+F1+F2+F3+1=q_native.
```

Use the integer factor

```
C=q_native−(F0+F1+F2+F3).
```

This factor has no independent sign exclusion. None is needed: it is the **only unrestricted factor**. If the product of the six protected factors and C equals1, every factor is an integer unit±1. All six protected factors must be+1 by the modulo-four argument, and then C=+1 as well. For raw, both protected factors are forced+1. The converse is immediate.

Thus the product restores every replaced comparison on the identical integer tuple **before** using any imported U15/native theorem. It follows that the complete positive first-halt relation, fixed valid-program slices, four program numerals, ordinary positive input and existing witnesses are unchanged. Arbitrary positive program tuples are still not asserted to encode valid programs.

The integer hypothesis is essential. The abstract two-factor statement fails over arbitrary real coordinates: N=4 and H=1/4 have product1 without either factor being1. For instance a=0,c=0,d=2 and T=0,y=1/2 realize these norm values. This is a counterexample to a real-domain factor lemma, not a claimed complete U15 false zero. The public arithmetic API continues to require exact integer assignments.

## 2. Exact source transfer and gate charge

For every native prefix, replace the old private offset rows at equal cost:

| Old source row | Replacement |
|---|---|
| `R15=Ac2+1` | `unit_main=L15−Ac2=N` |
| `P17=1−aux_y2` | `unit_auxiliary=L17+aux_y2=H` |

The squares/products on the right already occur in the complete incoming source. The rewrite validates the literal defining rows for Delta, c², T², V² and y² and rejects any additional source or active metadata consumer of the removed offsets. It also validates the actual d=ac+X+ga(4a+3) source, used by the degree proof below. A stable topological sort moves a norm definition after its square if necessary; sorting is a compilation operation, not an uncharged arithmetic gate.

For ordinary input additionally replace the private `bs_q=sumF+1` row by `unit_loader_checksum=q_native−sumF`. This is again one existing addition replaced by one subtraction. No source gate is added for these local replacements.

Combine the two raw factors with one multiplication, or the seven ordinary factors with six multiplications. Let U denote this product. Replace their former comparisons by U=1; every other comparison remains.

For raw, certificate cost306→307 and equation count11→10, giving338→336 total. For ordinary, certificate cost444→450 and equation count31→25, giving536→524 total. The added product multiplications are exactly offset by fewer residual squares. Thus the savings are **2 additions for raw and12 additions for ordinary**, with no change in the total multiplication count.

The prior individual ancestor map is moved to the explicitly historical `pre_unit_ancestor_comparison_map`. It is not a current residual map. The current `unit_factors` gives every merged old index, its factor, and its sign; `unit_retained_comparison_map` gives every remaining old index and its current comparison index. The retained ordinary-loader comparison count becomes15; the final product is a joint native equation, not assigned to the loader alone. Coordinates, current computed loader aliases and all unmodified arithmetic remain intact.

## 3. Complete finalizers and off-zero identities

Write R_i for the literal old comparison residuals and let I be the retained indices. For each merged norm row, its factor is1+R_i. The checksum row has the opposite orientation, giving factor1−R_checksum. Therefore the product U is an explicitly checked polynomial in the original residuals. Put

```
S=sum_(i in I) R_i^2.
```

Both complete finalizers have the same charged operation count:

```
F_SOS    = S + (U−1)^2,
F_anchor = U*(1+S)−1.
```

The first has zero exactly when all retained residuals vanish and U=1. For the second, 1+S is a positive integer. A zero gives U(1+S)=1, forcing U=1 and1+S=1. Hence S=0. Applying Section1 then restores every old residual. Conversely any old zero makes both new finalizers zero. This proves full same-coordinate integer-zero equality, and restricts immediately to the declared supplied domain.

On arbitrary integer, rational or real assignments, the displayed formulas are literal polynomial identities. If F_parent is the old complete SOS, then

```
F_SOS = F_parent − sum_(merged i) R_i^2 + (U−1)^2,
F_anchor = U*(1+F_parent−sum_(merged i) R_i^2)−1.
```

They are not equality to the old polynomial. The anchored output can change sign away from its zeros. No off-zero nonnegativity claim is used for it.

With e retained comparisons including U=1, either finalizer costs exactly3e−1 gates. The ordinary form has25 equations and74 finalizer gates; raw has10 equations and29 finalizer gates. All these gates are present in the exported schedules.

## 4. Actual degrees and the main-norm cancellation

It would be incorrect to inherit degree1936 after multiplying the norm factors. The literal source contains a main-norm cancellation. Write

```
H0=4a+3,
V0=X+ga*H0,
d=ac+V0,
Delta=a^2+H0.
```

The guarded actual rows prove the identity

```
d^2−Delta*c^2 = 2ac*V0+V0^2−H0*c^2.
```

This expanded expression is used only in the degree proof; it is not an uncharged replacement of the emitted norm schedule. Propagating homogeneous degrees and coefficients through this exact identity gives the following factor degrees:

| Factor | Geometry | Loader AND | History AND |
|---|---:|---:|---:|
| Main norm N |12|332|898|
| Auxiliary norm H |78|726|834|

The ordinary checksum has degree65. Hence the raw product has degree1732 and the ordinary product has degree2945. In both interfaces the largest retained residual degree is968, attained by the first native history norm. Its retained SOS therefore has exact degree1936.

The receipt independently propagates the complete highest homogeneous coefficient after the guarded cancellation, evaluates it at two prime moduli, and finds it nonzero in every form. Its dependency sets are empty for all fixed program numerals, so the result holds for every fixed valid program slice, not merely a chosen numerical program instance.

| Interface / finalizer | Literal propagated upper bound | Proven exact degree |
|---|---:|---:|
| Raw SOS |3604|**3464**|
| Raw anchor |3738|3668|
| Ordinary SOS |6166|5890|
| Ordinary anchor |5019|**4881**|

The default `auto` selects the lower-degree choice: raw SOS and ordinary anchor. Both options are maintained. The untouched536 compiler remains a larger operation schedule at exact degree1936, so this improvement is an operation/degree tradeoff. The canonical ledger retains its conservative propagated bound and `exact_degree_claimed=False`; the separate checked leading certificate records the exact degree.

The public `degree_audit` does not trust a stored claimed identity. It validates the entire typed supplied source, actual unit-factor rows, actual main-norm cancellation rows, factor roles, complete finalizer and ledger before substituting the proof identity. Altering the main norm, the computed d row or the finalizer is rejected.

## 5. Generic composition and public interfaces

The standalone parent is pinned at `u15_packed_joint_affine536.py`, SHA256 `eaaf3d99e74efeec26b7ad50842ac95fc89273f5ba37a52d45e9cca0e8fde330`. Both actual complete parent descriptors have type-sensitive pins in addition to the generator pin. Warm public access rechecks the parent and inherited source lineage. Public canonical packets and source exports are defensive copies.

`rewrite(packet, finalizer='auto')` is a narrowly scoped generic source transfer. It validates the complete incoming ordinary SOS, free-coordinate schema, exact scalar types, operation ledger and literal local native blocks; other arithmetic is copied unchanged. The caller must authenticate the incoming compiler's U15 semantics. This permits composition after independently proved affine or packed-index rewrites without claiming that an arbitrary user-supplied program description is universal. Applying a later generic SOS-only finalizer after the unit rewrite would be invalid; compose those rewrites first.

The maintained wrapper exposes `build`, `canonical_parent`, `checked`, `polynomial_source`, `evaluate` and `identity`; `degree_audit` verifies the degree claim on the actual full unit packet. Finalizer choices are exactly `auto`, `sos` and `anchor`, and Boolean switches require exact Booleans. Assignment keys must match the complete interface; Boolean/float coefficient aliases and invalid domains are rejected. `signed=True` permits exact integer algebraic evaluation; default raw L0,R0 are natural and every other supplied coordinate is strictly positive.

The broader positive graph correspondence to611 remains inherited through536 and561. This unit stage itself removes no witness, changes no native scale and requires no witness normalization or fresh Pell extension. It makes no claim to materialize the enormous native witnesses or to improve the separate87-operation universal benchmark.

## 6. Reproduction

```sh
python u15_packed_unit_product524.py
# Explicitly regenerate the receipt:
python u15_packed_unit_product524.py --write
```

A standalone copy may pass `--root /path/to/native-stream-queue`. The default compares the entire saved receipt with exact types. The generic helper has no permanent scratch dependency. Parent-family assertion requirements remain enabled.

The writer passes128 complete output identities,64 signed cases and2,688 individual original residual maps over all four finalizer/interface forms. The two unconditional modulo-four exclusions are checked across64 residue triples each. It rejects954 malformed calls/packets and checks eight defensive-copy boundaries. These finite cases supplement the all-integer argument; no finite search is presented as the universality proof. The receipt contains all four complete emitted circuits, current residual/factor maps, exact ledgers, literal source guards and eight nonzero leading certificates.

The [independent review](review_u15_unit524.md), [checker](review_u15_unit524.py) and [receipt](review_u15_unit524.json) verify the integer proof, complete finalizers and all four exact degrees. Full modular univariate evaluation of the emitted polynomials independently attains the claimed degrees without the author's leading-term substitution. The review found and repaired a public degree-audit guard gap before freezing the source; no unresolved finding remains.

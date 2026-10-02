# Independent review of the U15 unit-product transfer

Source audit PASS on `u15_packed_unit_product524.py`, SHA256 `667de9e6648af91c2fa1fe22801786fb78fd82156bce3132be05e9f10e513611`. The bounded review covers the complete source, the actual536 parent's four emitted successors, integer sign/domain proof, full finalizer algebra, costs, degree certificates and public/generic API validation. It does not repeat the inherited native Pell, history, fixed-program encoding or universality proofs. No complete universal zero was materialized.

## Integer zero-set equivalence

The literal native guards establish, in each of the three ordinary native cores, two factors

```
N=d²-Delta*c², Delta=a²+4a+3=(a+2)²-1,
H=T²*(V²-y²)+y², T=i*c².
```

Every symbol is integer-valued on arbitrary signed integer supplied tuples. Modulo4, Delta is0 or3, so N has residues0,1 or2 and cannot equal−1. Since T² is0 or1 modulo4, H is congruent to y² or V² and cannot equal−1 either. These exclusions require neither positive coordinates, native typing, a valid program nor any remaining equation. The source protects the actual squares and coefficient definitions, rather than merely trusting their names.

The ordinary product contains six such protected factors and one arbitrary integer factor `q_native-bs_Q`. The latter equals one minus the old loader checksum residual. If the product is1, every integer factor is±1; the six sign exclusions force each protected factor to1, and the last factor is then1. Conversely, all seven original residuals zero give product1. The raw form has two protected factors and no arbitrary checksum, so the same argument applies. Absorbing two arbitrary sign factors would require a further argument and is not done here.

The retained comparison residuals agree literally. With S their squared sum and U the product, the two finalizers are

```
S+(U-1)²,
U*(1+S)-1.
```

The first vanishes iff S=0 and U=1. For the second, S is a nonnegative integer, and U(1+S)=1 forces S=0 and U=1. This proves exactly the same full supplied integer zero set, and hence exactly the same original natural/positive mixed domain. The polynomial values away from zero need not agree. Integer integrality is essential to the unit and anchor arguments; no arbitrary-real zero-set equivalence follows.

The unit factors are precisely `1+r` for each merged native residual r, and `1-r` for the checksum residual. The original offsets are private: source consumers are forbidden and extra metadata consumers rejected except the expressly historical comparison map. Retained comparisons and the complete incoming literal SOS are validated. Thus there is no lost comparison or hidden unpaid finalizer.

## Complete cost and scope

| Interface | Parent | Child, either finalizer | Child comparisons | Positive witnesses |
|---|---:|---:|---:|---:|
| Raw natural tapes |338|336=126M+210A|10|51|
| Positive ordinary input |536|524=219M+305A|25|87|

Replacing seven old residuals by one unit comparison adds six product multiplications and removes six residual squares, twelve residual/sum additions, for a net saving of12 additions. The raw two-factor merge analogously saves two additions. Both finalizers have the same complete count; no unit comparison is free. Parent536 already contains the paid input and history compiler, and all supplied coordinates and fixed program numerals are unchanged. A generic incoming packet must carry a valid authenticated upstream compiler theorem supplied by its caller; the local source validation proves this unit transfer, not that any structurally valid arithmetic source is universal.

## Degree verification independent of the leading-term shortcut

The author's degree audit uses the actual source identity

```
(ac+X+ga*H)²-(a²+H)c²
 =2ac*(X+ga*H)+(X+ga*H)²-Hc².
```

The coefficient and root definitions needed for that identity are explicitly guarded. Propagation after this exact cancellation gives a degree upper bound. A nonzero evaluated highest homogeneous coefficient gives the matching lower bound, and conservative dependency sets exclude dependence of that coefficient on fixed program numerals. The retained ledger separately reports its original, larger, formal bound; it does not falsely label naive propagation as exact.

As an independent check, the review evaluates **every coefficient** of each complete emitted polynomial along two affine univariate lines modulo1009 and1013. Multiplication uses exact nonnegative coefficient convolution encoded into64-bit integer digits. Before each product it checks that the largest possible coefficient sum is below2^64, so no digit carry can corrupt convolution. All coefficients are reduced modulo the prime after each gate. This evaluates the literal polynomial source, without the author's main-norm cancellation override.

| Interface/finalizer | Exact degree attained | Leading coefficients modulo1009/1013 |
|---|---:|---:|
| Raw SOS |3464|361 /525|
| Raw anchor |3668|211 /784|
| Ordinary SOS |5890|209 /232|
| Ordinary anchor |4881|257 /187|

The two specializations use different fixed-program values and constant offsets, while retaining positive slopes for all nonfixed coordinates. They corroborate the exact source proof; uniformity across every valid fixed slice comes from the author's conservative no-fixed-dependency certificate, not these two examples. The ordinary default chooses the anchor, the raw default the SOS, by the stated comparison of formal upper bounds; these choices also have the smaller proved exact degrees here.

## Repaired API finding and replay coverage

One draft public API flaw was found: `degree_audit(packet)` initially substituted the norm identity without validating the supplied rows. A caller could change the actual unit norm or main root and still receive the old substituted degree certificate. The frozen source repairs this by validating typed source closure, the exact norm/cancellation rows, factor roles, native prefixes, guard metadata, complete literal finalizer and ledger before degree propagation. Independent regressions altering the norm, root and discriminant rows now reject. The canonical maintained output had not been affected by this caller-boundary bug.

The independent helper/receipt passed:

- 192 complete source/manual-finalizer identities, including96 signed cases;
- 864 unit-factor identities and4,032 parent comparison residuals;
- 64 complete modulo4 cases for each of the two sign lemmas;
- 78,125 supplemental integer-unit census cases;
- 194 malformed packet/degree-call rejections and eight defensive-copy checks;
- eight complete modular univariate polynomial evaluations, with all degrees attained.

The census is supplementary; the proof that integer factors of1 are units is unbounded. The source/manual replays do not materialize any full native witness. The helper pins the compiler before import, inherits its authenticated parent construction, accepts caller source/root paths, restores imported local namespaces/path state, and compares saved receipts with exact types.

```
python review_u15_unit524.py --source /path/to/u15_packed_unit_product524.py --root /path/to/native-stream-queue --expect review_u15_unit524.json
```

The complete six-section companion author note was independently proofread at SHA256 `c3acba47897ac2e82deef786d90b472836b680a395cb45c28a95d6f3fd8f76fe`. The source-specific norm guards, integer versus real scope, current/historical maps, all ledgers, exact-degree tradeoff and generic-caller authentication boundary agree with the frozen implementation. Both intended sibling links resolve. No correction requested. The independent writer and fresh exact receipt replay both passed.

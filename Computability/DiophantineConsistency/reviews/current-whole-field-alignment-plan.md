# Current2011 whole-field alignment: Lean implementation plan

This is a read-only mathematical/API planning note, not a new formal proof.
No frozen Lean or ordinary-proof source was changed. Proposed theorem names
and signatures below are not claimed to exist.

## Reviewed sources and existing boundary

I read the complete whole-field argument in section7 of
`research/padding-staircase-independent/PROOF.md`, together with its count,
support, tested-field identities and subsequent occupation argument. Its
SHA-256 is `69ce844ef80894251f4bd9510d9f60468585b4a004f4a624d3b347ce3e144fb8`.
I also read the actual-direction amendment
`reviews/padding-staircase2011-directional-terminology-amendment.md`
(`978accdfd82602fbdaaa0fffc84919b8c0cd8dbc727ff755e76b366e78a8c7a8`).
The offset19/20 argument uses South, whose packed calibration is unchanged
by that amendment; no horizontal-coordinate premise is needed here.

The relevant existing Lean interfaces are:

| Existing namespace/API | Available fact and remaining boundary |
| --- | --- |
| `CurrentSparseDigits2011.Reconstruction`, `decode_low_mask` | Actual Boolean `c`, periodic `CurrentMasks2011.lowSupport`, and `c 0=1`. This alone does not decode Start's labels. |
| `CurrentKernel2011.position`, `weight`, `convolution_eq` | Actual selector and34 label coefficients, including all reflected collisions. South positions are942+j with doubled weight `2^(36+j)`, j<9. |
| `CurrentClause2011.clause_convolution`, `selectorCount_eq_prefix`, `normalized_clause_residue`, `normalized_clause_mask` | Literal sole clause and low residue/mask. The complete physical34-bit decoding binding is still needed. |
| `CurrentReflectedGeometry2011.reflected_even`, `incoming_carry_zero`, `copy_marker_incoming_zero` | Even reflected terms and low carry resets, conditional on the physical at-most-one count. |
| `CurrentPhaseParity2011.marker_convolution`, `marker_digit_parity`, `fractional_phase_zero` | Literal marker and fractional phase0, without decoded labels or occupation. Main source hash `3abd1bc07fe430892871e13b0b066a689ef74854a45bc725ee73bfe349325eb7`. |
| `NativeBooleanRotation.rotation_zero_phase` | Once `W%47=0`, the actual temporal digit is `c(k-↑(W/47))`. |
| `CurrentHighDigits2011.cellDigit_copy_south`, `maskDigits_nonzero` | Mask1 at all nine target fields960..968; their nonzero cell residues exclude the origin borrow. |
| `WangTiles942.tile`, `start_zero`, `selectorWeight`, `physicalPosition`; `WangTiles942.physicalEquiv` | Full literal tile calibration and the proved actual floor-rank permutation. Start is physical0. No supplied sorting cache is needed. |

I read the current `DoubledClause2011` draft as well. Its generic `raw`,
`digit`, `decode_empty`, `decode_occupied`, and `decode` recover the unsigned
34-bit copied word with incoming carry and both Boolean summands retained.
They do not yet identify that word with the literal current control fields.
The legacy `NativeClauseBits54.binaryValue` is a generic bit-sum definition,
but its other clause/label semantics belong to a different tuple and must
not be substituted for current942 calibration.

## Smallest decoded information needed

Whole-field alignment needs only the **South projection** of full decoding.
For each cell origin b define the literal nine-bit value

`S(b) = sum(j<9, c(b+942+j)*2^j)`.

Boolean digits give `S(b)<512`. The physical clause binding should supply:

1. `S(0)=510`: from `c 0=1`, physical at-most-one, the actual Start tile,
   and the recovered complementary word. In particular current fields943
   and944 are1. Their values cannot be assumed from the origin mask alone.
2. If the physical selector941 is1 in cell b, then
   `S(b)=sstar`, where the fixed value is
   `sstar = 511 - (tile (physicalEquiv.symm 941)).south`.
   No computation of that inverse or its actual value511 is required for
   the uniform offset19 lemma.
3. The physical selector count is at most1 in every cell. In particular
   selector940 and941 cannot both be1.

Empty cells are allowed: their decoded South value is0. Neither all-cell
occupation nor a selected tile in every cell belongs in this interface.
All other label projections may remain in the complete decoding theorem
but are unnecessary for this alignment step.

## Literal parity and source-cell geometry still to bind

First prove the exact nine copy identities from `convolution_eq`. At target
`b+960+j`, j<9, the bare18 source is `b+942+j`; the bare1004 source wraps
to absent residue1967+j, and bare2020 has absent residue951+j. Retain the
full even reflection. With zero incoming carry, even radix, and actual
mask1, Boolean digits yield

`c(b+942+j) = c(b+960+j-t)`, where `t=W/47`.

This is valid **before** whole-field alignment. Do not replace the right
side by a temporal North label until its source position is known. The
same existing marker parity gives `c(1004-t)=c 0=1`.

Use `Cell := {b : ZMod (N*2011) // b.val%2011=0}` as the finite cell type;
this avoids introducing a separate coordinate equivalence with `ZMod N`.
Put `r=t%2011`. Translation

`theta(b) = b - ↑(t-r)`

is a permutation of `Cell`, with explicit inverse addition by `↑(t-r)`.
Prove closure using divisibility of `t-r` by2011. For `r≤e<2011`, prove
the exact equality `b+e-↑t = theta(b)+(e-r)`. For `e<r`, only the residue
formula2011+e-r is initially needed. These proofs must use the complete
cyclic modulus `N*2011`, not truncated natural subtraction at field level.
`CurrentClause2011.addition_residue` and `subtraction_residue` provide the
existing modular arithmetic helpers.

From `c(1004-t)=1`, sparse support gives `r≤1004` and either `r=0` or
`19≤r`: every supported position other than1004 is at most985. If r>961,
the temporal source for forced-one target961 wraps to2011+961-r>1004,
contradicting support. If21≤r≤961, forced-one targets961 and962 have the
distinct physical selector preimages961-r and962-r in the **same** cell
theta(0), contradicting its count bound. Thus only0,19,20 remain.

## Two small generic exclusion lemmas

**Offset19: one exceptional doubling branch on a finite permutation.**
A sufficient standalone signature has a finite type A, `sigma : A ≃ A`,
`S : A → Nat`, `epsilon : A → Nat`, and one fixed `sstar : Nat`, with

```
S i < 512
epsilon i ≤ 1
S (sigma i) = (2*S i + epsilon i) % 512
epsilon i = 1 → S i = sstar
```

and concludes `S i ≠ 510` for every i. No occupation, tile data or
restriction on the particular fixed terminal color is needed. In the
literal application, first aggregate all nine copy-bit equalities to

`S(b) = (2*S(theta b))%512 + c(theta b+941)`.

Then take `sigma=theta.symm` and `epsilon(b)=c(b+941)`. The sum cannot
overflow512, because its first term is even and at most510.

For the generic proof, a cycle containing510 forces the two epsilon values
at the third and second predecessors to be1 by reduction modulo8. Their
two source values are both sstar, so the intervening recurrence forces
`sstar=(2*sstar+1)%512`, hence sstar=511. The forward orbit from510 is
then510,508,504,496,480,448,384,256,0; every epsilon there is0 and zero
is absorbing. This contradicts periodicity. Mathlib already provides
`Function.Injective.mem_periodicPts` and `Function.mem_periodicPts` in
`Mathlib/Dynamics/PeriodicPts/Lemmas.lean`/`Defs.lean`; these avoid an
explicit cycle-list API. The graph's511 self-loop is real, so a theorem
asserting every cycle is zero would be false.

**Offset20: a residue contradiction, with no finite-cycle API.**
The smaller generic signature uses an arbitrary type A, any function
`theta : A → A`, functions S and e into Nat, and only

```
e i ≤ 2
S i = (4*S (theta i)) % 512 + e i
```

to conclude `S i ≠ 510`. Every output has residue0,1 or2 modulo4. An
output510 forces e=2 and `S(theta i)%128=127`, hence that source has
residue3 modulo4, contradicting the same universal output restriction.
No finiteness, bijectivity, color bound or terminal-tile calibration is
needed in this generic lemma. In the actual application, aggregate the
nine bits to `e(b)=c(theta b+940)+2*c(theta b+941)`; one-hotness gives
e≤2. The remaining seven source bits are exactly South bits0..6, which
produce the truncated factor4.

Both aggregations need only two elementary nine-bit reconstruction lemmas:
prepending one Boolean bit gives `(2*S)%512+bit`, and prepending two gives
`(4*S)%512+bit0+2*bit1`. They should use literal bit sums or bounded
`Nat.testBit` reconstruction, not an assumed equality of decoded colors.

## Dependency and circularity audit

The intended order is: actual low-mask reconstruction and carry witnesses;
preliminary physical count in every cell; fractional phase0; actual full
clause-to-label decoding; actual copy/marker parity; coarse residue split;
offset19/20 exclusions; finally `(W/47)%2011=0`. Existing code supplies
several of these steps, but the complete current label binding, nine
literal copy identities, cell-translation geometry and two generic
exclusions remain separate obligations.

Do not assume a temporally clean clause or zero incoming clause carry to
obtain labels: the unaligned temporal clause bit must remain present in
`DoubledClause2011`. Do not assume `marker=selectorCount`, that all markers
are1, unique Start, all cells occupied, or a nonzero temporal stride. The
marker relation after alignment is a shifted Start indicator. Occupation
propagation through actual East/West equalities and the nonzero-stride
argument using StartNorth76 versus StartSouth510 come **after** alignment.
Neither directed Wang adjacency nor machine/refutation calibration is an
input to these purely arithmetic phase exclusions.

# Lean equivalence proofs for the constructed size frontier

The owner resumed Lean formalization on 25 October 2026. The objective is
to prove that the simplest equations constructed under the different
metrics have no solutions exactly when the repository's syntactic
`ConZFC`. This supersedes the earlier pause. Decimal notation and distinct
unsubscripted scalar names remain requirements for the maintained page.

## Required endpoints and evidence

`DiophantineConsistency.Bridge.ConZFC` is
`¬ BProv ZFCax_s [] Form.fBot`, for the actual repository axiom predicate.
`NativeZFC.noPositiveZero_iff_conZFC`, `ExplicitZFC` and `DirectQuarticZFC`
already prove external Lean equivalences for their own generic compiled
equations. `BusyBeaver.ZFC.KEndpoint215.blank_halts_iff_zfc_refutation`
is the checked literal 215-state-machine endpoint. None identifies the
recent short equations merely by having the same variable count.

For each selected frontier equation, completion requires:

1. Literal Lean expression/polynomial data, exact fixed coefficient recipe,
   and evaluation identities for the constructed equation.
2. The stated witness domain, with checked forward and inverse witness
   transformations and every positivity and integrality obligation.
3. Soundness and completeness of its arithmetic and native encoding,
   without a supplied premise asserting the desired equivalence.
4. Composition with the actual syntactic refutation endpoint, yielding a
   closed Lean theorem for that particular equation.
5. Kernel-checked builds and audits of the theorem axioms. Python finite
   certificates and ordinary proofs guide this work but do not replace it.
6. For the original assertion of provability *in ZFC*, the internal
   interpretation and object-language derivation, including nonstandard
   internal codes. The older external Lean endpoints alone do not supply it.

The target collection includes the maintained 14-positive/65-operation/
degree-150 page; the accepted 13-positive 69/174, 70/140 and 71/128
arithmetic alternatives; and the lower-variable, lower-degree, sparse and
coefficient-height alternatives recorded in `SIZE_REDUCTION.md` and the
manuscript catalogue. These must be assessed by their actual metrics and
bindings, rather than replacing the goal with one convenient equation.
No global optimality theorem is requested or inferred from that ledger.

## Current gaps and implementation order

The live local native modules treat the older 457-mode, 89-bit compact54
construction. Their strongest local-mask endpoint is
`NativeLocalMask54.source_local_masks`. The literal decimal decoder and complete length2011 masks now have the
bindings and proofs recorded below. The remaining current942-tile,
47-bit encoding work includes the exact K recipe, sorting permutation,
carry/phase recovery, helical tiling interpretation and canonical controller
converse. The 1997 proposal
remains a separate candidate; its page is not promoted by this plan.

The first new modules address necessary reusable pieces of that chain:

- `Carrier65`: the actual fourteen-coordinate arithmetic front, its
  polynomial/evaluation identity, cancellation and sign recovery.
- `CarrierRankBounds`: positive free carrier and the strict rank window
  derived from the printed transport factor and fixed-port inequalities.
- `FirstPellCarrier`: integrality and positivity of the omitted quotient,
  positive converse carrier, and uniqueness of both restored witnesses.
- `NativeCyclicCarry`: bounded cyclic carries and local resets, needed
  where a global carry-free estimate is insufficient for radix47.

These are work items, not completion claims. After their checked composition,
the complete literal P66/native arithmetic bridge and the current finite
machine/coefficient calibration remain required. The 13-variable signed
auxiliary-Pell residue and fresh-seed maps require their own proofs. The
old `ShortCircuit` module describes a different 15-variable 69-operation
graph and cannot serve as the new 13-variable binding.

## Verified arithmetic checkpoint

The first four modules above now compile, together with their focused
checks. `Carrier65.eval_polynomial_zero_iff_norms` binds the actual
fourteen-variable polynomial to its five unit equations on every positive
assignment, without a rank or first-root sign premise.
`Carrier65Witness.polynomial_zero_restores_index` derives the rank window,
positivity of the first root, and the unique positive omitted quotient
directly from an actual zero and the fixed-port box. `FirstPellCarrier`
also proves the converse positive carrier map and uniqueness. The
[root review](reviews/carrier65-lean-arithmetic-root.md) and separate
[front](reviews/carrier65-front-lean-peer.md) and
[rank/witness](reviews/carrier65-rank-witness-lean-peer.md) reviews record
the exact scope and reproduction commands. These theorems require the
scalar port inequalities; the current entire native recipe still must be
bound and calibrated. The final consistency equivalence remains open.

The bounded cyclic carry and word-identification modules also now compile.
`NativeCyclicCarryWord.exists_convolution_normalization` derives bounded
actual carries, normalized digits, their exact local decomposition and
equality with the positive strict transport representative.
`transport_mask_digits` transfers the packed mask test to those digits.
The [root review](reviews/native-cyclic-carry-lean-root.md) records the
necessary numeric budget and range assumptions. Their discharge from the
literal current native recipe, followed by staircase and phase recovery,
remains required.

`Carrier66.exists_positive_polynomial_zero_iff_canonical_parent_zero` now
checks both full coordinate maps and zero-existence equivalence between
the actual fourteen-variable polynomial and its canonical positive
fifteen-variable parent. The parent's canonical conditions are explicit;
they are not a supplied classification of all parent zeros.
`Carrier66Source` now restores all31 positive literal source coordinates,
proves all22 source equations, and identifies the exact rank, q and C.
Its `canonical_window` exposes the complete native arithmetic window under
the finite coefficient interface; `positive_carrier_zero_source` starts at
the actual Carrier65 zero. See the [independent root review](reviews/carrier66-source31-lean-root.md)
and full row ledger. The current full coefficient binding and native
computation equivalence are still required.
`ThirteenCarrier.positive_polynomial_zero_sets` binds all three literal
thirteen-coordinate formulas and proves their entire positive zero sets
agree. The signed derived y is allowed to be negative. Their fresh-seed
and native equivalences are still required. See the
[frontier arithmetic review](reviews/carrier-frontier-lean-root.md).

`DecimalMachine215` now binds the actual complete715-digit page decoder,
including signed subtraction at the halt target, to the checked dense215
machine through an explicit state equivalence. Its430 transitions and
blank-halting equivalence are checked. `PaddingStaircase` proves the
actual bit-three prefix argument and the full low-clause mask consequence:
483 tested prefixes plus459 Boolean selectors force total at most462,
then the derived2006 low bound forces total at mostone. See the
[decoder/staircase review](reviews/decimal-staircase-lean-root.md).
The current physical prefix residues, resets and full942-tile language
remain to be connected. The current machine-to-ZFC dependency run has completed168/168, with104
exact-source cached modules and64 fresh compilations, plus the separately
recorded KZip verification. `DecimalMachineZFC.blank_nonhalting_iff_conZFC`
now gives a closed equivalence for the actual decoded machine and the
existing consistency predicate. See the [root review](reviews/decimal-machine-zfc-lean-root.md)
and [completed build record](reviews/machine215-current-closure-build.md).
The current Diophantine/tableau link and internal-ZFC proof remain open.

The signed auxiliary-Pell residue needed by the thirteen-variable soundness
map is now checked in `SignedPellResidue.four_square_dvd_sub_one`. From
S>=2, the exact auxiliary norm and y congruent to1 modulo4 it derives
`4*S^2 | y-1`, without sign or size assumptions on V,y. The
[root review](reviews/signed-pell-residue-lean-root.md) includes signed
examples and the necessary modulo-four premise.

`ThirteenCarrierSoundness.polynomial_zero_restores` now proves the complete
forward map for all three literal thirteen-variable polynomials. Every
positive zero restores a positive actual Carrier65 zero, with unchanged
ports. Transport nonnegativity and divisibility are derived; the signed
ordinate is replaced by its absolute value, and the restored z is positive.
See the [root review](reviews/thirteen-carrier-soundness-lean-root.md) for the
fresh replay and exact scope.

`ThirteenFreshSeed` now constructs the private positive f,i,T,m from the
fixed outer Pell data, rather than assuming compatibility with a parent
seed. `ThirteenCarrierComplete.polynomial_zero_completes` derives those
outer data from every actual positive Carrier65 zero, PortBounds, the
finite mask Interface and MC%4=2, and produces positive zeros of all three
literal13 polynomials while preserving all nine outer slots. The
[full root review](reviews/thirteen-fresh-complete-lean-root.md) records
fresh checks and the necessary extra finite residue. The full native and internal-ZFC links remain required.

`CurrentMasks2011` and `CurrentMaskRecipes2011` now bind the complete two
length2011 masks and beta, including their exact printed geometric-series
recipes, strict bounds, positivity, population sum94517, low residue2
modulo4 and native-high residue4 modulo8. Every finite Interface field is
proved for K>=0, with the source high mask shifted by beta exactly once.
The [independent whole-mask review](reviews/current-masks2011-lean-peer.md)
includes fresh builds, standard axiom audits and full coefficient-byte
comparisons against the maintained page. K remains a parameter; its exact
942-tile recipe and native interpretation still need composition.

`CurrentCarrierArithmetic2011.positive_zero_existence_chain` now composes
both complete arithmetic witness maps at those exact masks, discharging
PortBounds, Interface and MC%4 internally. It proves65↔69↔70↔71 for the
literal positive-zero existence statements under only K>0; `completes`
additionally preserves all nine outer coordinates. The [root integration
review](reviews/current-carrier-arithmetic2011-lean-root.md) and [independent
peer replay](reviews/current-carrier-arithmetic2011-lean-peer.md) record
whole-source reviews, fresh builds/checks and standard-only axiom audits.
K remains a parameter, so the current native consistency theorem is still
an outstanding objective.

`CurrentSparseDigits2011.polynomial_zero_reconstructs` now starts from an
actual positive current65 zero and recovers N>0, exact q/J and the full
Boolean selector word C on the repeated current support. Its global origin
bit is1; selector1, dummy977 and marker1004 each have exactly one available
bit. The full MC*repunit+1 identity is proved. See the [root review](reviews/current-sparse-digits2011-lean-root.md)
for the exact source/check replay and cache scope. This fixes the Start bit;
at-most-one selector occupation and native interpretation are still required.

`NativeBooleanRotation` now proves the exact scaled permutation at every
binary phase of a Boolean word, including the last fractional phase. Its
half-radix bound and origin anchor require no prior temporal alignment.
`NativeWindowCarry.source_convolution_carries` derives the transport
congruence from the actual positive31-row source solution and constructs
bounded cyclic carries, the exact F digit word, and all local mask tests
under an explicit coefficient-mass budget and word bindings. See the
[root review](reviews/native-window-carry-lean-root.md) and [independent
peer replay](reviews/native-window-carry-lean-peer.md). The current coefficient
recipe and budget still need specialization; phase and native semantics
remain separate obligations.

`CurrentHighDigits2011` now proves every high-mask field and gap, all
digit bounds, and the full repeated MF*J−1 word. Its origin subtraction
changes4 to3 only at the global origin. `polynomial_zero_mask_test`
derives that complete mask test from every actual positive current65
zero and K>0, with no supplied F word or native premise. See the
[root whole-source review and replay](reviews/current-high-digits2011-lean-root.md).
The exact coefficient recipe, physical count and phase recovery remain
to be composed with the mask and carry results.

`WangTiles942Data`, `WangTiles942Core` and `WangTiles942` now bind all430
actual decimal machine actions, both complete target sets and every rail
to all942 printed indexed tiles. They prove the full index coverage,
printed-order permutation, color bounds, exact physical floor formula
and initializer position504 with its actual first target1. See the
[root review](reviews/wang-tiles942-lean-root.md) and [independent replay
and numeric reconstruction](reviews/wang-tiles942-lean-peer.md). This is
index uniqueness; tuple/weight distinctness, the physical-rank bijection,
and native machine semantics still require proofs.

`NativePreliminaryCount2011.total_le_one_all_phases` now completes the
arithmetic preliminary-count argument across all temporal phases. Only
phases7..10 request the483 staircase bindings; other phases use the low
clause bits directly. The [root review](reviews/native-preliminary-count2011-lean-root.md)
and [independent replay](reviews/native-preliminary-count2011-lean-peer.md)
include the full-mask phase10 counterexample showing why those middle
premises matter. Literal physical clause/padding residues and carry
bindings remain to be discharged from the current native recipe.

Independent agents own distinct new Lean modules. The coordinator owns
integration, documentation and commits. Each verified checkpoint is
committed with its exact scope, then `origin/main` is fetched and merged
before a normal, non-force push of the branch to `origin/main`.

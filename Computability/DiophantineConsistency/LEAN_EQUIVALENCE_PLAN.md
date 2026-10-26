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
`NativeLocalMask54.source_local_masks`. The current 942-tile, 47-bit,
length-2011 coefficient recipe, decimal decoder, sorting permutation,
carry/phase recovery, helical tiling interpretation and canonical controller
converse still need literal Lean bindings and proofs. The 1997 proposal
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

Independent agents own distinct new Lean modules. The coordinator owns
integration, documentation and commits. Each verified checkpoint is
committed with its exact scope, then `origin/main` is fetched and merged
before a normal, non-force push of the branch to `origin/main`.

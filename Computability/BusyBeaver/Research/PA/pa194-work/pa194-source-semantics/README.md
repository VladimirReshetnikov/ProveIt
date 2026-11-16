# Facts about the source theory, proved in its models

The guarded compiler of [`pa194-guarded-compiler`](../pa194-guarded-compiler/README.md)
needs a fixed list of facts about the adjunctive source theory with full separation
(`adjunctiveFullSepTheory`): `SourceFacts` and the statements of `PA194SuccessorLaws`. Each
is the typed quote of a standard sentence of the relational source language. By
`source_supply` (`PA194SemanticSupply`), such a fact is internally provable in every model of
`IΣ₁` once the sentence is true in every structure with equality that satisfies weak
adjunction and all separation instances. This directory proves facts that way: the
mathematics is done in an arbitrary structure, about its membership relation, and no
derivation is written. The structures are not assumed extensional.

## Modules

| Module | Content |
| --- | --- |
| `PA194SourceModelBase` | `Mem x a` and the statements `SZero`, `SSucc`, `SDom`, `SKur`, `SEdge`, `SGraphDom`, `SFun`, `SRange`, `SAddPrefix`, `SAdd`, `SMulPrefix`, `SMul`, … about it; `se_*`: truth of each source formula at arbitrary terms is the corresponding statement; `mD_iff`, `mE_iff`, `mZ_iff`, `mS_iff`, `mA_iff`, `mMu_iff`: the letters of `sourceLetters`; `kur_inj`: the components of a Kuratowski pair are determined; `sep_spec`: a separation instance as the existence of the subset defined by a formula with parameters. |
| `PA194SourcePredecessor` | `restrict_graph`: the entries of a graph with first component in `t ∪ {t}`; `add_predecessor`, `mul_predecessor`: the predecessor laws in a structure; `sAP_supply`, `sMP_supply`: `adjunctiveFullSepTheory.internalize V ⊢ tHyp sAP` and `⊢ tHyp sMP` in every model `V` of `IΣ₁`. |
| `PA194SourceModelIso` | `SIso` and the parts of an order bijection, with their `se_*` lemmas and `mI_iff`; `iso_right_empty`, `iso_left_empty`; `restrict_left`; `iso_cancel`: cancellation of a successor on both sides of an isomorphism of ordinal representatives. |
| `PA194SourceInduction` | `dom_mem`: members of ordinal representatives are ordinal representatives; `dom_zero_or_succ`; `dom_induction`: induction over ordinal representatives for a property whose complement is defined by a formula with parameters; `letter_induction`: the same for a formula over the letters. |
| `PA194SourceKnown` | `sWith10`, `MTheta10`, `ev_sWith10`: a sentence under the ten source facts other than `sA2`, `sM2`; `TenFacts T` and `with_ten`: internal provability of the ten, and their discharge; `Known N`, `known_of`: their consequences as statements about a structure. |
| `PA194SourceAddCoherence` | `add_zero_left`: a sum of an empty representative and `b` is `b`; `sem_a2`: coherence of addition in a structure, by `letter_induction`; `a2_supply`: `adjunctiveFullSepTheory.internalize V ⊢ tHyp sA2` from `TenFacts`. |
| `PA194SourceMulCoherence` | `mul_zero_left`: a product with an empty first factor is that factor; `sem_m2`: coherence of multiplication in a structure, from coherence of addition; `m2_supply`: `⊢ tHyp sM2` from `TenFacts` and `⊢ tHyp sA2`. |
| `PA194SourceAddComm` | `sem_r0` (a sum of `b` and an empty representative is isomorphic to `b`), `sem_rs` (the sum with a successor as second summand, up to isomorphism), `sem_ac` (commutativity), each by `letter_induction`; `ac_supply`: `⊢ tHyp sAC` from `TenFacts`. |
| `PA194SourceCalibration` | `sourceFacts_of_ten`, `sourceFacts_full`: `SourceFacts` from `TenFacts`; `calibration_of_ten`: internal proofs of `sA2`, `sM2`, `sA3`, `sM3` in `adjunctiveFullSepTheory` from `TenFacts`. These four are the conjuncts of `ArithmeticCalibration` of `pa194-guarded-compiler`. |
| `PA194SourceSets` | `wa_spec` (weak adjunction about membership), `exists_empty`, `exists_adjoin`, `exists_singleton`, `exists_pair`, `exists_kur`, `exists_extend` (a graph with one more entry), `dom_irrefl`, `empty_dom`, `succ_exists` (every ordinal representative has a successor that is one). |
| `PA194SourceIsoFacts` | `iso_of_empty`, `iso_succ` (successors of isomorphic representatives are isomorphic), `iso_refl`, `iso_symm`, `iso_trans`; the last three by `letter_induction` with `iso_cancel` and `iso_succ`, with no inverse or composite graph. |
| `PA194SourceTotality` | `succ_pred_unique`, `point_graph`, `extend_prefix`, `add_total`, `mul_total`: sums and products of ordinal representatives exist. |
| `PA194SourceArithmetic` | `known_full`, `theta10`, `valid_ten`: the ten facts in a structure; `tenFacts_semantic : TenFacts adjunctiveFullSepTheory`; `sourceFacts_semantic`: all twelve `SourceFacts`; `calibration`: internal proofs of `sA2`, `sM2`, `sA3`, `sM3`. No hypothesis. |

## Status

Proved here for the actual source theory, in every model `V` of `IΣ₁`, with no hypothesis
and using no internal proof from another directory: all twelve members of `SourceFacts`
(`sourceFacts_semantic`), and `sA2`, `sM2`, `sA3`, `sM3` (`calibration`), which are the four
conjuncts of `ArithmeticCalibration` of `pa194-guarded-compiler`. Every fact about the
source theory in this chain is proved in structures and transferred by `source_supply`.
The ten members of `SourceFacts` other than `sA2`, `sM2` also have internal proofs by
derivations in `pa194-model-axioms`; they are not used here.

Used by: `ArithmeticCalibration` of `pa194-guarded-compiler` is a statement about all models
of the candidate PRA presentation with an `IΣ₁` reduct. It is stated from `calibration` in
`PA194ArithmeticCalibrationSemantic` of
[`pa194/ipra/native-endpoint`](../../pa194/ipra/native-endpoint/README.md), and
`PA194ModeledSchedulerSemanticIFF` there uses `sourceFacts_semantic` and `calibration` for
the equivalence between a halt of the modeled scheduler and an internal refutation of
arithmetic. The equivalence in iPRA between the consistency sentence and non-halting of the
literal 194-state machine, `PA194NativeLiteralFinal.consistency_iff_literal_nonhalt`, is
proved in that directory; no module of this directory states it.

## Checking

The modules were compiled directly with `lean`, one process at a time, against locally
compiled objects of their imports (`PA194SemanticSupply`, `PA194SuccessorLaws` and their
closure). All axiom reports are `[propext, Classical.choice, Quot.sound]`: five in
`PA194SourceModelBase`, four in `PA194SourcePredecessor`, two in `PA194SourceModelIso`, four
in `PA194SourceInduction`, two in `PA194SourceKnown`, three in `PA194SourceAddCoherence`,
three in `PA194SourceMulCoherence`, four in `PA194SourceAddComm`, three in
`PA194SourceCalibration`, four in `PA194SourceSets`, five in `PA194SourceIsoFacts`, four in
`PA194SourceTotality`, five in `PA194SourceArithmetic`.

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-source-semantics/check.sh
```

runs [`check_bridge.py`](../pa194-model-fairness/check_bridge.py) once, with
`PA194SourceArithmetic` as the top module (it imports the other twelve), and checks these
report counts from the logs of the thirteen modules. On 2026-11-16 it was run with
`--out DIR` on a directory that already held the compiled objects of the imports: it
recompiled the thirteen modules of this directory and passed. A run in a fresh directory,
which compiles the whole closure of about 620 standalone modules, has not been done.

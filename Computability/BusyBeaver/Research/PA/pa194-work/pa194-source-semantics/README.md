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

## Status

Proved here for the actual source theory: `sAP` and `sMP` outright, and `sA2` from
`TenFacts` (the ten members of `SourceFacts` other than `sA2` and `sM2`; this directory
does not import their internal proofs from `pa194-model-axioms`).

Not proved here: `sM2` (products of isomorphic members of the domain are isomorphic) and
`sAC` (sums in the two orders are isomorphic).

## Checking

The modules were compiled directly with `lean`, one process at a time, against locally
compiled objects of their imports (`PA194SemanticSupply`, `PA194SuccessorLaws` and their
closure). All axiom reports are `[propext, Classical.choice, Quot.sound]`: five in
`PA194SourceModelBase`, four in `PA194SourcePredecessor`, two in `PA194SourceModelIso`, four
in `PA194SourceInduction`, two in `PA194SourceKnown`, three in `PA194SourceAddCoherence`.
There is no check script in this directory yet.

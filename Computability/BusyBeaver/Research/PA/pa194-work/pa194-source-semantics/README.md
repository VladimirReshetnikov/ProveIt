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

## Status

Proved here for the actual source theory: `sAP` and `sMP`.

Not proved here: `sA2`, `sM2` (sums and products of isomorphic members of the domain are
isomorphic) and `sAC` (sums in the two orders are isomorphic). The letter for order
isomorphism has no `se_*` lemma yet.

## Checking

Both modules were compiled directly with `lean`, one process at a time, against locally
compiled objects of their imports (`PA194SemanticSupply`, `PA194SuccessorLaws` and their
closure). Their axiom reports are `[propext, Classical.choice, Quot.sound]`: five reports in
`PA194SourceModelBase`, four in `PA194SourcePredecessor`. There is no check script in this
directory yet.

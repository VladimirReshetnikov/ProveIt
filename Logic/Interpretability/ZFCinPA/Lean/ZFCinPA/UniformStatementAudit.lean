import ZFCinPA.UniformStatement

/-!
# Audit for the literal uniform sentence `PA ⊢ ∀ n, Prov_ZFC(⌜Conₙ(ZFC)⌝)`

This audit keeps the logically distinct layers visible in their types:

* the `𝚺₁`-represented code builder — its graph, totality, single-valuedness,
  and quotation agreement at standard points;
* the single arithmetic sentence with an internal quantifier, and its
  arbitrary-model semantics;
* the metatheoretic standard-point family obtained from
  `zfc_proves_conZFCSet` by derivability condition D1;
* the selector `Prop` and the exact soundness/completeness equivalence with
  the requested PA derivation.

In particular, the standard-point family is not silently presented as a
proof of the sentence: the remaining obligation is precisely
`ZFCProofSelectorInAllModels`.
-/

namespace LeanProofs.ZFCinPA.UniformStatementAudit

open LeanProofs.ZFCinPA

/-! ## Form-level analysis and depth-independence -/

#check @restForm
#check @conZFCBodyF_eq
#check @free_fNumF
#check @toNat_toSet_congr
#check @quote_toSet_congr
#check @quote_toSet_fImp

/-! ## The sealing count and the quotation of the sealed sentence -/

#check @sealCount
#check @sealCount_zero
#check @sealCount_succ
#check @quote_toSet_fAllIter
#check @quote_conZFCSet

/-! ## The internal code builder -/

#check @numChainCode
#check @numChainCode_natCast
#check @conNumCode
#check @conNumCode_natCast
#check @sealCountV
#check @sealCountV_natCast
#check @allClosure
#check @allClosure_natCast
#check @conZFCBodyCode
#check @conZFCBodyCode_natCast
#check @conZFCSetCodeFun
#check @conZFCSetCodeGraph
#check @conZFCSetCodeFun.defined

/-! ## The functional relation and its standard points -/

#check @ConZFCSetCode
#check @eval_conZFCSetCodeGraph_iff
#check @conZFCSetCode_total
#check @conZFCSetCode_functional
#check @conZFCSetCode_existsUnique
#check @conZFCSetCodeFun_natCast
#check @conZFCSetCode_quote_numeral

/-! ## The literal sentence, its semantics, and standard points -/

#check @paUniformZFCProvabilitySentence
#check @eval_paUniformZFCProvabilitySentence_iff
#check @eval_paUniformZFCProvabilitySentence_iff_fun
#check @provable_conZFCSet_standard_point
#check @paUniformZFCProvability_standard_instance

/-! ## The selector and the equivalence -/

#check @ZFCProofSelectorIn
#check @ZFCProofSelectorInAllModels
#check @eval_paUniformZFCProvabilitySentence_iff_selector
#check @peano_proves_uniformZFCProvability_of_selectorInAllModels
#check @peano_proves_uniformZFCProvability_iff_selectorInAllModels

/-! ## Assumption audit

Foundation's arithmetic and the repository's semantic core are classical, so
`Classical.choice`, `propext` and `Quot.sound` are expected; nothing beyond
Lean's three standard axioms should appear, and in particular no `sorry` and
no theory-specific axiom. -/

#print axioms toNat_toSet_congr
#print axioms quote_conZFCSet
#print axioms conZFCSetCodeFun_natCast
#print axioms conZFCSetCode_quote_numeral
#print axioms eval_paUniformZFCProvabilitySentence_iff
#print axioms provable_conZFCSet_standard_point
#print axioms paUniformZFCProvability_standard_instance
#print axioms eval_paUniformZFCProvabilitySentence_iff_selector
#print axioms peano_proves_uniformZFCProvability_of_selectorInAllModels
#print axioms peano_proves_uniformZFCProvability_iff_selectorInAllModels

end LeanProofs.ZFCinPA.UniformStatementAudit

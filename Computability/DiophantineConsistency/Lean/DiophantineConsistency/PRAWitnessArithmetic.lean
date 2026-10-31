import DiophantineConsistency.PRAWitnessCalculus
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Basic
/-! # Witness bounds for Foundation's arithmetic and syntax-code graphs

Every definition here is bounded throughout (all of its quantifiers carry a
`<`, `≤` or `∈'` guard), so `PRAWitnessCalculus` derives a monotone witness
bound for it, in both polarities, from the bounds of the definitions it embeds:
each proof unfolds one definition and runs `wb_auto`. No explicit majorant is
written. This covers pairing (`pairDef`, `pair₃Def` … `pair₆Def`, `pi₁Def`,
`pi₂Def`), division and roots, the exponential stack (`expDef`,
`exponentialDef`, `extDef`, `pow2Def`, `ppow2Def`, `sppow2Def`, `lenbitDef`,
`Seqₛ.def`), bits and sets (`bitDef`, `insertDef`, `bitSubsetDef`), the
HFS sequence graphs (`underDef`, `memRel`, `memRel₃`, `domainDef`,
`isMappingDef`, `seqDef`, `lhDef`, `seqConsDef`), the derivation-code index
graphs (`fstIdxDef`, `sndIdxDef`), the formula constructors (`qq*Def`) and
the ten rule graphs of `Derivation.blueprint` (`axLGraph` … `axmGraph`).

Only `𝗣𝗔⁻` is assumed, so every lemma holds in the arithmetic reduct of each
candidate-PRA model. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace DiophantineConsistency.PRAWitnessArithmetic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAWitnessCalculus
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]

theorem wb_subDef : WB M (subDef).val := by
  simp only [subDef, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_neg_subDef : WB M (∼(subDef).val) := by
  simp only [subDef, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_pairDef : WB M (pairDef).val := by
  simp only [pairDef, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_neg_pairDef : WB M (∼(pairDef).val) := by
  simp only [pairDef, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_divDef : WB M (divDef).val := by
  simp only [divDef, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_neg_divDef : WB M (∼(divDef).val) := by
  simp only [divDef, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_dvd : WB M (dvd).val := by
  simp only [dvd, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_neg_dvd : WB M (∼(dvd).val) := by
  simp only [dvd, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_sqrtDef : WB M (sqrtDef).val := by
  simp only [sqrtDef, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_neg_sqrtDef : WB M (∼(sqrtDef).val) := by
  simp only [sqrtDef, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_pair₃Def : WB M (pair₃Def).val := by
  have := wb_pairDef (M := M)
  simp only [pair₃Def, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_neg_pair₃Def : WB M (∼(pair₃Def).val) := by
  have := wb_neg_pairDef (M := M)
  simp only [pair₃Def, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_pair₄Def : WB M (pair₄Def).val := by
  have := wb_pairDef (M := M)
  simp only [pair₄Def, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_neg_pair₄Def : WB M (∼(pair₄Def).val) := by
  have := wb_neg_pairDef (M := M)
  simp only [pair₄Def, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_pair₅Def : WB M (pair₅Def).val := by
  have := wb_pairDef (M := M)
  simp only [pair₅Def, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_neg_pair₅Def : WB M (∼(pair₅Def).val) := by
  have := wb_neg_pairDef (M := M)
  simp only [pair₅Def, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_remDef : WB M (remDef).val := by
  have := wb_divDef (M := M)
  have := wb_subDef (M := M)
  simp only [remDef, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_neg_remDef : WB M (∼(remDef).val) := by
  have := wb_neg_divDef (M := M)
  have := wb_neg_subDef (M := M)
  simp only [remDef, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_pow2Def : WB M (pow2Def).val := by
  have := wb_neg_dvd (M := M)
  have := wb_dvd (M := M)
  simp only [pow2Def, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_neg_pow2Def : WB M (∼(pow2Def).val) := by
  have := wb_dvd (M := M)
  have := wb_neg_dvd (M := M)
  simp only [pow2Def, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_lenbitDef : WB M (lenbitDef).val := by
  have := wb_divDef (M := M)
  have := wb_neg_dvd (M := M)
  simp only [lenbitDef, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_neg_lenbitDef : WB M (∼(lenbitDef).val) := by
  have := wb_neg_divDef (M := M)
  have := wb_dvd (M := M)
  simp only [lenbitDef, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_pi₁Def : WB M (pi₁Def).val := by
  have := wb_pairDef (M := M)
  simp only [pi₁Def, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_neg_pi₁Def : WB M (∼(pi₁Def).val) := by
  have := wb_neg_pairDef (M := M)
  simp only [pi₁Def, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_pi₂Def : WB M (pi₂Def).val := by
  have := wb_pairDef (M := M)
  simp only [pi₂Def, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_neg_pi₂Def : WB M (∼(pi₂Def).val) := by
  have := wb_neg_pairDef (M := M)
  simp only [pi₂Def, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_qqVerumDef : WB M (qqVerumDef).val := by
  have := wb_pairDef (M := M)
  simp only [qqVerumDef, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_neg_qqVerumDef : WB M (∼(qqVerumDef).val) := by
  have := wb_neg_pairDef (M := M)
  simp only [qqVerumDef, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_qqAllDef : WB M (qqAllDef).val := by
  have := wb_pairDef (M := M)
  simp only [qqAllDef, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_neg_qqAllDef : WB M (∼(qqAllDef).val) := by
  have := wb_neg_pairDef (M := M)
  simp only [qqAllDef, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_qqExsDef : WB M (qqExsDef).val := by
  have := wb_pairDef (M := M)
  simp only [qqExsDef, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_neg_qqExsDef : WB M (∼(qqExsDef).val) := by
  have := wb_neg_pairDef (M := M)
  simp only [qqExsDef, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_pair₆Def : WB M (pair₆Def).val := by
  have := wb_pair₅Def (M := M)
  have := wb_pairDef (M := M)
  simp only [pair₆Def, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_neg_pair₆Def : WB M (∼(pair₆Def).val) := by
  have := wb_neg_pair₅Def (M := M)
  have := wb_neg_pairDef (M := M)
  simp only [pair₆Def, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_extDef : WB M (extDef).val := by
  have := wb_divDef (M := M)
  have := wb_neg_divDef (M := M)
  have := wb_remDef (M := M)
  have := wb_neg_remDef (M := M)
  simp only [extDef, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_neg_extDef : WB M (∼(extDef).val) := by
  have := wb_divDef (M := M)
  have := wb_neg_divDef (M := M)
  have := wb_remDef (M := M)
  have := wb_neg_remDef (M := M)
  simp only [extDef, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_sppow2Def : WB M (sppow2Def).val := by
  have := wb_neg_lenbitDef (M := M)
  have := wb_lenbitDef (M := M)
  have := wb_neg_pow2Def (M := M)
  have := wb_sqrtDef (M := M)
  have := wb_neg_sqrtDef (M := M)
  simp only [sppow2Def, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_neg_sppow2Def : WB M (∼(sppow2Def).val) := by
  have := wb_lenbitDef (M := M)
  have := wb_neg_lenbitDef (M := M)
  have := wb_pow2Def (M := M)
  have := wb_neg_sqrtDef (M := M)
  have := wb_sqrtDef (M := M)
  simp only [sppow2Def, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_fstIdxDef : WB M (fstIdxDef).val := by
  have := wb_subDef (M := M)
  have := wb_pi₁Def (M := M)
  simp only [fstIdxDef, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_neg_fstIdxDef : WB M (∼(fstIdxDef).val) := by
  have := wb_neg_subDef (M := M)
  have := wb_neg_pi₁Def (M := M)
  simp only [fstIdxDef, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_sndIdxDef : WB M (sndIdxDef).val := by
  have := wb_subDef (M := M)
  have := wb_pi₂Def (M := M)
  simp only [sndIdxDef, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_neg_sndIdxDef : WB M (∼(sndIdxDef).val) := by
  have := wb_neg_subDef (M := M)
  have := wb_neg_pi₂Def (M := M)
  simp only [sndIdxDef, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_qqAndDef : WB M (qqAndDef).val := by
  have := wb_pair₃Def (M := M)
  simp only [qqAndDef, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_neg_qqAndDef : WB M (∼(qqAndDef).val) := by
  have := wb_neg_pair₃Def (M := M)
  simp only [qqAndDef, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_qqOrDef : WB M (qqOrDef).val := by
  have := wb_pair₃Def (M := M)
  simp only [qqOrDef, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_neg_qqOrDef : WB M (∼(qqOrDef).val) := by
  have := wb_neg_pair₃Def (M := M)
  simp only [qqOrDef, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_axLGraph : WB M (axLGraph).val := by
  have := wb_pair₃Def (M := M)
  have := wb_neg_pair₃Def (M := M)
  simp only [axLGraph, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_neg_axLGraph : WB M (∼(axLGraph).val) := by
  have := wb_pair₃Def (M := M)
  have := wb_neg_pair₃Def (M := M)
  simp only [axLGraph, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_verumIntroGraph : WB M (verumIntroGraph).val := by
  have := wb_pair₃Def (M := M)
  have := wb_neg_pair₃Def (M := M)
  simp only [verumIntroGraph, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_neg_verumIntroGraph : WB M (∼(verumIntroGraph).val) := by
  have := wb_pair₃Def (M := M)
  have := wb_neg_pair₃Def (M := M)
  simp only [verumIntroGraph, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_orIntroGraph : WB M (orIntroGraph).val := by
  have := wb_pair₅Def (M := M)
  have := wb_neg_pair₅Def (M := M)
  simp only [orIntroGraph, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_neg_orIntroGraph : WB M (∼(orIntroGraph).val) := by
  have := wb_pair₅Def (M := M)
  have := wb_neg_pair₅Def (M := M)
  simp only [orIntroGraph, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_allIntroGraph : WB M (allIntroGraph).val := by
  have := wb_pair₄Def (M := M)
  have := wb_neg_pair₄Def (M := M)
  simp only [allIntroGraph, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_neg_allIntroGraph : WB M (∼(allIntroGraph).val) := by
  have := wb_pair₄Def (M := M)
  have := wb_neg_pair₄Def (M := M)
  simp only [allIntroGraph, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_exsIntroGraph : WB M (exsIntroGraph).val := by
  have := wb_pair₅Def (M := M)
  have := wb_neg_pair₅Def (M := M)
  simp only [exsIntroGraph, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_neg_exsIntroGraph : WB M (∼(exsIntroGraph).val) := by
  have := wb_pair₅Def (M := M)
  have := wb_neg_pair₅Def (M := M)
  simp only [exsIntroGraph, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_wkRuleGraph : WB M (wkRuleGraph).val := by
  have := wb_pair₃Def (M := M)
  have := wb_neg_pair₃Def (M := M)
  simp only [wkRuleGraph, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_neg_wkRuleGraph : WB M (∼(wkRuleGraph).val) := by
  have := wb_pair₃Def (M := M)
  have := wb_neg_pair₃Def (M := M)
  simp only [wkRuleGraph, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_shiftRuleGraph : WB M (shiftRuleGraph).val := by
  have := wb_pair₃Def (M := M)
  have := wb_neg_pair₃Def (M := M)
  simp only [shiftRuleGraph, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_neg_shiftRuleGraph : WB M (∼(shiftRuleGraph).val) := by
  have := wb_pair₃Def (M := M)
  have := wb_neg_pair₃Def (M := M)
  simp only [shiftRuleGraph, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_cutRuleGraph : WB M (cutRuleGraph).val := by
  have := wb_pair₅Def (M := M)
  have := wb_neg_pair₅Def (M := M)
  simp only [cutRuleGraph, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_neg_cutRuleGraph : WB M (∼(cutRuleGraph).val) := by
  have := wb_pair₅Def (M := M)
  have := wb_neg_pair₅Def (M := M)
  simp only [cutRuleGraph, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_axmGraph : WB M (axmGraph).val := by
  have := wb_pair₃Def (M := M)
  have := wb_neg_pair₃Def (M := M)
  simp only [axmGraph, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_neg_axmGraph : WB M (∼(axmGraph).val) := by
  have := wb_pair₃Def (M := M)
  have := wb_neg_pair₃Def (M := M)
  simp only [axmGraph, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_ppow2Def : WB M (ppow2Def).val := by
  have := wb_pow2Def (M := M)
  have := wb_sppow2Def (M := M)
  have := wb_lenbitDef (M := M)
  simp only [ppow2Def, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_neg_ppow2Def : WB M (∼(ppow2Def).val) := by
  have := wb_neg_pow2Def (M := M)
  have := wb_neg_sppow2Def (M := M)
  have := wb_neg_lenbitDef (M := M)
  simp only [ppow2Def, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_andIntroGraph : WB M (andIntroGraph).val := by
  have := wb_pair₆Def (M := M)
  have := wb_neg_pair₆Def (M := M)
  simp only [andIntroGraph, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_neg_andIntroGraph : WB M (∼(andIntroGraph).val) := by
  have := wb_pair₆Def (M := M)
  have := wb_neg_pair₆Def (M := M)
  simp only [andIntroGraph, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_Exponential_Seqₛ_def : WB M (Exponential.Seqₛ.def).val := by
  have := wb_neg_ppow2Def (M := M)
  have := wb_extDef (M := M)
  simp only [Exponential.Seqₛ.def, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_neg_Exponential_Seqₛ_def : WB M (∼(Exponential.Seqₛ.def).val) := by
  have := wb_ppow2Def (M := M)
  have := wb_neg_extDef (M := M)
  simp only [Exponential.Seqₛ.def, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_exponentialDef : WB M (exponentialDef).val := by
  have := wb_extDef (M := M)
  have := wb_Exponential_Seqₛ_def (M := M)
  have := wb_ppow2Def (M := M)
  simp only [exponentialDef, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_neg_exponentialDef : WB M (∼(exponentialDef).val) := by
  have := wb_neg_extDef (M := M)
  have := wb_neg_Exponential_Seqₛ_def (M := M)
  have := wb_neg_ppow2Def (M := M)
  simp only [exponentialDef, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_expDef : WB M (expDef).val := by
  have := wb_exponentialDef (M := M)
  simp only [expDef, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_neg_expDef : WB M (∼(expDef).val) := by
  have := wb_neg_exponentialDef (M := M)
  simp only [expDef, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_bitDef : WB M (bitDef).val := by
  have := wb_expDef (M := M)
  have := wb_lenbitDef (M := M)
  simp only [bitDef, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_neg_bitDef : WB M (∼(bitDef).val) := by
  have := wb_neg_expDef (M := M)
  have := wb_neg_lenbitDef (M := M)
  simp only [bitDef, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_underDef : WB M (underDef).val := by
  have := wb_expDef (M := M)
  simp only [underDef, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_neg_underDef : WB M (∼(underDef).val) := by
  have := wb_neg_expDef (M := M)
  simp only [underDef, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_insertDef : WB M (insertDef).val := by
  have := wb_bitDef (M := M)
  have := wb_neg_bitDef (M := M)
  have := wb_expDef (M := M)
  simp only [insertDef, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_neg_insertDef : WB M (∼(insertDef).val) := by
  have := wb_neg_bitDef (M := M)
  have := wb_bitDef (M := M)
  have := wb_neg_expDef (M := M)
  simp only [insertDef, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_bitSubsetDef : WB M (bitSubsetDef).val := by
  have := wb_neg_bitDef (M := M)
  have := wb_bitDef (M := M)
  simp only [bitSubsetDef, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_neg_bitSubsetDef : WB M (∼(bitSubsetDef).val) := by
  have := wb_bitDef (M := M)
  have := wb_neg_bitDef (M := M)
  simp only [bitSubsetDef, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_memRel : WB M (memRel).val := by
  have := wb_pairDef (M := M)
  have := wb_neg_pairDef (M := M)
  have := wb_bitDef (M := M)
  have := wb_neg_bitDef (M := M)
  simp only [memRel, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_neg_memRel : WB M (∼(memRel).val) := by
  have := wb_pairDef (M := M)
  have := wb_neg_pairDef (M := M)
  have := wb_bitDef (M := M)
  have := wb_neg_bitDef (M := M)
  simp only [memRel, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_memRel₃ : WB M (memRel₃).val := by
  have := wb_pairDef (M := M)
  have := wb_neg_pairDef (M := M)
  have := wb_bitDef (M := M)
  have := wb_neg_bitDef (M := M)
  simp only [memRel₃, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_neg_memRel₃ : WB M (∼(memRel₃).val) := by
  have := wb_pairDef (M := M)
  have := wb_neg_pairDef (M := M)
  have := wb_bitDef (M := M)
  have := wb_neg_bitDef (M := M)
  simp only [memRel₃, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_domainDef : WB M (domainDef).val := by
  have := wb_neg_bitDef (M := M)
  have := wb_bitDef (M := M)
  have := wb_pairDef (M := M)
  have := wb_neg_pairDef (M := M)
  simp only [domainDef, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_neg_domainDef : WB M (∼(domainDef).val) := by
  have := wb_bitDef (M := M)
  have := wb_neg_bitDef (M := M)
  have := wb_neg_pairDef (M := M)
  have := wb_pairDef (M := M)
  simp only [domainDef, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_isMappingDef : WB M (isMappingDef).val := by
  have := wb_domainDef (M := M)
  have := wb_neg_bitDef (M := M)
  have := wb_memRel (M := M)
  have : WB M memRelOpr.sentence := wb_memRel (M := M)
  have := wb_neg_memRel (M := M)
  have : WB M (∼memRelOpr.sentence) := wb_neg_memRel (M := M)
  simp only [isMappingDef, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_neg_isMappingDef : WB M (∼(isMappingDef).val) := by
  have := wb_neg_domainDef (M := M)
  have := wb_bitDef (M := M)
  have := wb_neg_memRel (M := M)
  have : WB M (∼memRelOpr.sentence) := wb_neg_memRel (M := M)
  have := wb_memRel (M := M)
  have : WB M memRelOpr.sentence := wb_memRel (M := M)
  simp only [isMappingDef, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_seqDef : WB M (seqDef).val := by
  have := wb_isMappingDef (M := M)
  have := wb_domainDef (M := M)
  have := wb_underDef (M := M)
  simp only [seqDef, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_neg_seqDef : WB M (∼(seqDef).val) := by
  have := wb_neg_isMappingDef (M := M)
  have := wb_neg_domainDef (M := M)
  have := wb_neg_underDef (M := M)
  simp only [seqDef, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_lhDef : WB M (lhDef).val := by
  have := wb_neg_seqDef (M := M)
  have := wb_domainDef (M := M)
  have := wb_underDef (M := M)
  have := wb_seqDef (M := M)
  simp only [lhDef, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_neg_lhDef : WB M (∼(lhDef).val) := by
  have := wb_seqDef (M := M)
  have := wb_neg_domainDef (M := M)
  have := wb_neg_underDef (M := M)
  have := wb_neg_seqDef (M := M)
  simp only [lhDef, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_seqConsDef : WB M (seqConsDef).val := by
  have := wb_lhDef (M := M)
  have := wb_pairDef (M := M)
  have := wb_insertDef (M := M)
  simp only [seqConsDef, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_neg_seqConsDef : WB M (∼(seqConsDef).val) := by
  have := wb_neg_lhDef (M := M)
  have := wb_neg_pairDef (M := M)
  have := wb_neg_insertDef (M := M)
  simp only [seqConsDef, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

end DiophantineConsistency.PRAWitnessArithmetic

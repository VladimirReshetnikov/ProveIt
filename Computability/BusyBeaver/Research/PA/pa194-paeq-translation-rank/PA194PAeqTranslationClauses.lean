import PA194PAeqTranslationRank
import PA196PATermRecBound
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
namespace PA194PAeqTranslationClauses
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAWitnessCalculus PRAWitnessArithmetic PRAWitnessVectors
open PA194PAeqTermBlueprint PRAWitnessTransfer PRAWitnessTermRec PRAWitnessTermFunctions
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem positive_clauses : WB M termBlueprint.bvar.val ∧ WB M termBlueprint.fvar.val ∧
    WB M termBlueprint.func.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_qqBvarDef (M := M); have := wb_qqFvarDef (M := M)
  have := wb_qqFuncDef (M := M); have := wb_adjoinDef (M := M)
  refine ⟨?_,?_,?_⟩ <;>
    simp only [termBlueprint, functionCodeGraph, HierarchySymbol.Semiformula.val_mkSigma] <;> wb_auto
  refine wb_exs_poly _ (by simp) ‘4096’ ?_ ?_
  · intro V _ _ e u h
    refine ⟨u,?_,h⟩
    have h' := h
    simp at h'
    rw [h'.1]
    norm_num [qqFunc, pair, numeral_eq_natCast]
  · refine wb_exs_poly _ (by simp) ‘4096’ ?_ (by wb_auto)
    intro V _ _ e u h
    refine ⟨u,?_,h⟩
    have h' := h
    simp at h'
    rw [h'.2.1, h'.1]
    norm_num [qqFunc, pair, adjoin_def, numeral_eq_natCast]

theorem bvar_negative : WB M (∼termBlueprint.bvar.graphDelta.pi.val) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  obtain ⟨hb,_,_⟩ := positive_clauses (M := M)
  refine wb_neg_graphDelta_pi _ hb ‘(#0 + 1) * (#0 + 1) + 1’ ?_
  intro V _ _ e y h
  simp [termBlueprint] at h
  simpa [h] using qqBvar_le (e 0)

theorem fvar_negative : WB M (∼termBlueprint.fvar.graphDelta.pi.val) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  obtain ⟨_,hf,_⟩ := positive_clauses (M := M)
  refine wb_neg_graphDelta_pi _ hf ‘(1 + #0 + 1) * (1 + #0 + 1) + 1’ ?_
  intro V _ _ e y h
  simp [termBlueprint] at h
  simpa [h] using qqFvar_le (e 0)

noncomputable def functionBound : ArithmeticSemiterm Empty 4 :=
  ‘(2 + ((2 + ((3 + #3 + 1) * (3 + #3 + 1)) + 1) * (2 + ((3 + #3 + 1) * (3 + #3 + 1)) + 1)) + 1) *
   (2 + ((2 + ((3 + #3 + 1) * (3 + #3 + 1)) + 1) * (2 + ((3 + #3 + 1) * (3 + #3 + 1)) + 1)) + 1) + 1 + (((1000 * 1000) * (1000 * 1000)) * (1000 * 1000))’

theorem func_negative : WB M (∼termBlueprint.func.graphDelta.pi.val) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  obtain ⟨_,_,hf⟩ := positive_clauses (M := M)
  refine wb_neg_graphDelta_pi _ hf functionBound ?_
  intro V _ _ e y h
  have hy : y = functionCode (e 0) (e 1) (e 3) := by
    have hh := (termConstruction (V := V)).func_defined.defined (y :> e)
    simpa [termConstruction, Matrix.comp_vecCons''] using hh.mp h
  rw [hy]
  simp [functionBound, numeral_eq_natCast]
  change functionCode (e 0) (e 1) (e 3) ≤
    (2 + ((2 + ((3 + e 3 + 1) * (3 + e 3 + 1)) + 1) * (2 + ((3 + e 3 + 1) * (3 + e 3 + 1)) + 1)) + 1) *
    (2 + ((2 + ((3 + e 3 + 1) * (3 + e 3 + 1)) + 1) * (2 + ((3 + e 3 + 1) * (3 + e 3 + 1)) + 1)) + 1) + 1 + (((1000 * 1000) * (1000 * 1000)) * (1000 * 1000))
  by_cases hk : e 0 = 0
  · by_cases hf : e 1 = 0
    · simp only [functionCode, hk, hf, if_pos]
      apply le_trans (show (zeroCode : V) ≤ (((1000 * 1000) * (1000 * 1000)) * (1000 * 1000)) by norm_num [zeroCode,qqFunc,pair])
      exact le_add_self
    · simp only [functionCode, hk, hf, if_pos, if_false]
      apply le_trans (show (oneCode : V) ≤ (((1000 * 1000) * (1000 * 1000)) * (1000 * 1000)) by norm_num [PA194PAeqTermBlueprint.oneCode, PA194PAeqTermBlueprint.zeroCode,qqFunc,pair,adjoin_def])
      exact le_add_self
  · by_cases hf : e 1 = 0
    · simp only [functionCode, hk, hf, if_false, if_pos]
      apply le_trans (qqFunc_le (2 : V) 2 (e 3))
      have h1 : 2 + e 3 + 1 ≤ 3 + e 3 + 1 := by
        exact add_le_add (add_le_add (by norm_num : (2 : V) ≤ 3) le_rfl) le_rfl
      have h2 := mul_le_mul' h1 h1
      have h3 := add_le_add (add_le_add (le_refl (2 : V)) h2) (le_refl 1)
      have h4 := add_le_add (add_le_add (le_refl (2 : V)) (mul_le_mul' h3 h3)) (le_refl 1)
      have h5 := add_le_add (mul_le_mul' h4 h4) (le_refl 1)
      exact le_trans h5 le_self_add
    · simp only [functionCode, hk, hf, if_false]
      apply le_trans (qqFunc_le (2 : V) 3 (e 3))
      exact le_self_add

#print axioms func_negative
#print axioms bvar_negative
#print axioms fvar_negative
#print axioms positive_clauses
end PA194PAeqTranslationClauses

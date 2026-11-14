import PA196PASemitermBound
import PA196PASubstitutionOne
import PA196PRAWitnessTower
import DiophantineConsistency.PRAWitnessTermFunctions

/-! Both exact arithmetic existential-introduction rule branches have
candidate-PRA witness bounds. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA196PAExistentialRuleBounds
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAWitnessCalculus PRAWitnessArithmetic
  PRAWitnessTermFunctions PRAWitnessFormulaFunctions PRAWitnessTransfer PA196PRAWitnessTower PA196PASubstitutionOne

noncomputable def positiveBranch : ArithmeticSemisentence 2 :=
  “D C. ∃ s < D, ∃ p < D, ∃ t < D, ∃ d < D, !exsIntroGraph D s p t d ∧
    (∃ ep, !qqExsDef ep p ∧ ep ∈ s) ∧
    !((isSemiterm ℒₒᵣ).sigma) 0 t ∧
    ∃ c, !fstIdxDef c d ∧ ∃ pt, !(substs1Graph ℒₒᵣ) pt t p ∧ !insertDef c pt s ∧ d ∈ C”
noncomputable def negativeBranch : ArithmeticSemisentence 2 :=
  “D C. ∃ s < D, ∃ p < D, ∃ t < D, ∃ dp < D,
    !exsIntroGraph D s p t dp ∧ (∀ ex, !qqExsDef ex p → ex ∈ s) ∧
    !(isSemiterm ℒₒᵣ).pi 0 t ∧
    ∀ c, !fstIdxDef c dp → ∀ pt, !(substs1Graph ℒₒᵣ) pt t p → !insertDef c pt s ∧ dp ∈ C”
noncomputable def actualPositive : ArithmeticSemisentence 2 :=
  match (Derivation.blueprint (𝗣𝗔 : ArithmeticTheory)).core.sigma.val with
  | .and _ (.or _ (.or _ (.or _ (.or _ (.or _ (.or a _)))))) => a
  | _ => ⊥
noncomputable def actualNegative : ArithmeticSemisentence 2 :=
  match (Derivation.blueprint (𝗣𝗔 : ArithmeticTheory)).core.pi.val with
  | .and _ (.or _ (.or _ (.or _ (.or _ (.or _ (.or a _)))))) => a
  | _ => ⊥
theorem positive_exact : actualPositive = positiveBranch := by rfl
theorem negative_exact : actualNegative = negativeBranch := by rfl

variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem wb_positive : WB M actualPositive := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  rw [positive_exact]
  have := wb_exsIntroGraph (M := M); have := wb_qqExsDef (M := M); have := wb_bitDef (M := M)
  have := PA196PASemitermBound.wb_positive (M := M); have := wb_fstIdxDef (M := M)
  have := wb_substs1Graph (M := M); have := wb_insertDef (M := M)
  simp only [positiveBranch]
  wb_auto
  · refine wb_exs_poly _ (by simp) ‘#3’ (fun V _ _ e x h => ⟨x, ?_, h⟩) (by wb_auto)
    have h' := h; simp at h'
    exact le_of_lt (lt_of_mem h'.2)
  · refine wb_exs_poly _ (by simp) ‘#0’ (fun V _ _ e c h => ⟨c, ?_, h⟩) ?_
    · have h' := h; simp at h'; simp [h'.1]
    · wb_auto
      refine wb_exs_towerPoly _ (by simp) ‘#3 + ((#2 + 1) * (#2 + 1) + 1)’ ?_ (by wb_auto)
      intro V _ _ e x h
      refine ⟨x, ?_, h⟩
      have h' := h; simp at h'
      rw [h'.1]
      simpa [Semiterm.val_func, numeral_eq_natCast] using substs1_le_tower (e 2) (e 3)

theorem wb_negative : WB M (∼actualNegative) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  rw [negative_exact]
  have := wb_neg_exsIntroGraph (M := M); have := wb_qqExsDef (M := M)
  have := PA196PASemitermBound.wb_negative (M := M); have := wb_fstIdxDef (M := M)
  have := wb_substs1Graph (M := M); have := wb_neg_insertDef (M := M); have := wb_neg_bitDef (M := M)
  simp only [negativeBranch]
  wb_auto
  · refine wb_exs_poly _ (by simp) ‘(7+#2+1)*(7+#2+1)+1’
      (fun V _ _ e x h => ⟨x, ?_, h⟩) (by wb_auto)
    have h' := h; simp at h'
    rw [h'.1]
    simpa [qqExs, Semiterm.val_func, numeral_eq_natCast] using code2_le (7 : V) (e 2)
  · refine wb_exs_poly _ (by simp) ‘#0’ (fun V _ _ e c h => ⟨c, ?_, h⟩) ?_
    · have h' := h; simp at h'; simp [h'.1]
    · wb_auto
      refine wb_exs_towerPoly _ (by simp) ‘#3 + ((#2 + 1) * (#2 + 1) + 1)’ ?_ (by wb_auto)
      intro V _ _ e x h
      refine ⟨x, ?_, h⟩
      have h' := h; simp at h'
      rw [h'.1]
      simpa [Semiterm.val_func, numeral_eq_natCast] using substs1_le_tower (e 2) (e 3)

#print axioms wb_positive
#print axioms wb_negative
end PA196PAExistentialRuleBounds

import PA196PASetShiftExistential

/-! Both exact arithmetic derivation shift-rule branches have candidate-PRA
witness bounds. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA196PAShiftRuleBounds
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAWitnessCalculus PRAWitnessArithmetic
  PRAWitnessTransfer PA196PASetShiftExistential

noncomputable def positiveBranch : ArithmeticSemisentence 2 :=
  “D C. ∃ s < D, ∃ d < D, !shiftRuleGraph D s d ∧
    ∃ c, !fstIdxDef c d ∧ !(setShiftGraph ℒₒᵣ) s c ∧ d ∈ C”
noncomputable def negativeBranch : ArithmeticSemisentence 2 :=
  “D C. ∃ s < D, ∃ d < D, !shiftRuleGraph D s d ∧
    ∀ c, !fstIdxDef c d → ∀ ss, !(setShiftGraph ℒₒᵣ) ss c → s = ss ∧ d ∈ C”
noncomputable def actualPositive : ArithmeticSemisentence 2 :=
  match (Derivation.blueprint (𝗣𝗔 : ArithmeticTheory)).core.sigma.val with
  | .and _ (.or _ (.or _ (.or _ (.or _ (.or _ (.or _ (.or _ (.or sh _)))))))) => sh
  | _ => ⊥
noncomputable def actualNegative : ArithmeticSemisentence 2 :=
  match (Derivation.blueprint (𝗣𝗔 : ArithmeticTheory)).core.pi.val with
  | .and _ (.or _ (.or _ (.or _ (.or _ (.or _ (.or _ (.or _ (.or sh _)))))))) => sh
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
  have := wb_shiftRuleGraph (M := M); have := wb_fstIdxDef (M := M)
  have := PA196PASetShift.wb_setShiftGraph (M := M); have := wb_bitDef (M := M)
  simp only [positiveBranch]
  wb_auto
  refine wb_exs_poly _ (by simp) ‘#0’ (fun V _ _ e x h => ⟨x, ?_, h⟩) (by wb_auto)
  have h' := h; simp at h'; simp [h'.1]

theorem wb_negative : WB M (∼actualNegative) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  rw [negative_exact]
  have := wb_neg_shiftRuleGraph (M := M); have := wb_fstIdxDef (M := M)
  have := PA196PASetShift.wb_setShiftGraph (M := M); have := wb_neg_bitDef (M := M)
  simp only [negativeBranch]
  wb_auto
  refine wb_exs_poly _ (by simp) ‘#0’ (fun V _ _ e c h => ⟨c, ?_, h⟩) ?_
  · have h' := h; simp at h'; simp [h'.1]
  · wb_auto
    refine wb_exs_setShift (0 : Fin 5) _ (by simp) (by wb_auto) ?_
    intro V _ _ e y h
    have h' := h; simp at h' ⊢
    exact h'.1

#print axioms wb_positive
#print axioms wb_negative
end PA196PAShiftRuleBounds

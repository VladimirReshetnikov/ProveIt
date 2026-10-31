import DiophantineConsistency.PRAWitnessSetShiftCandidate
import DiophantineConsistency.PRAWitnessTransfer
/-! Bounds for the identity, verum, weakening and shift sigma rule branches. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace DiophantineConsistency.PRAWitnessPositiveSimpleRules
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAWitnessCalculus PRAWitnessArithmetic
  PRAWitnessTransfer PRAWitnessFormulaFunctions PRAWitnessSetShiftCandidate
noncomputable def identityBranch : ArithmeticSemisentence 2 :=
  “D C. ∃ s < D, ∃ p < D, !axLGraph D s p ∧ p ∈ s ∧
    ∃ np, !(negGraph ℒₛₑₜ) np p ∧ np ∈ s”
noncomputable def verumBranch : ArithmeticSemisentence 2 :=
  “D C. ∃ s < D, !verumIntroGraph D s ∧ ∃ p, !qqVerumDef p ∧ p ∈ s”
noncomputable def weakeningBranch : ArithmeticSemisentence 2 :=
  “D C. ∃ s < D, ∃ d < D, !wkRuleGraph D s d ∧
    ∃ c, !fstIdxDef c d ∧ !bitSubsetDef c s ∧ d ∈ C”
noncomputable def shiftBranch : ArithmeticSemisentence 2 :=
  “D C. ∃ s < D, ∃ d < D, !shiftRuleGraph D s d ∧
    ∃ c, !fstIdxDef c d ∧ !(setShiftGraph ℒₛₑₜ) s c ∧ d ∈ C”
noncomputable def actualIdentity (T : SetTheory) [T.Δ₁] : ArithmeticSemisentence 2 :=
  match (Derivation.blueprint T).core.sigma.val with | .and _ (.or a _) => a | _ => ⊥
noncomputable def actualVerum (T : SetTheory) [T.Δ₁] : ArithmeticSemisentence 2 :=
  match (Derivation.blueprint T).core.sigma.val with | .and _ (.or _ (.or a _)) => a | _ => ⊥
noncomputable def actualWeakening (T : SetTheory) [T.Δ₁] : ArithmeticSemisentence 2 :=
  match (Derivation.blueprint T).core.sigma.val with | .and _ (.or _ (.or _ (.or _ (.or _ (.or _ (.or _ (.or a _))))))) => a | _ => ⊥
noncomputable def actualShift (T : SetTheory) [T.Δ₁] : ArithmeticSemisentence 2 :=
  match (Derivation.blueprint T).core.sigma.val with | .and _ (.or _ (.or _ (.or _ (.or _ (.or _ (.or _ (.or _ (.or a _)))))))) => a | _ => ⊥
theorem actualIdentity_eq (T : SetTheory) [T.Δ₁] : actualIdentity T = identityBranch := by rfl
theorem actualVerum_eq (T : SetTheory) [T.Δ₁] : actualVerum T = verumBranch := by rfl
theorem actualWeakening_eq (T : SetTheory) [T.Δ₁] : actualWeakening T = weakeningBranch := by rfl
theorem actualShift_eq (T : SetTheory) [T.Δ₁] : actualShift T = shiftBranch := by rfl
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
theorem wb_identity : WB M identityBranch := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  have := wb_axLGraph (M := M); have := wb_bitDef (M := M); have := wb_negGraph (M := M)
  simp only [identityBranch]
  wb_auto
  refine wb_exs_poly _ (by simp) ‘#1’ (fun V _ _ e x h => ⟨x, ?_, h⟩) (by wb_auto)
  have h' := h
  simp at h'
  exact le_of_lt (lt_of_mem h'.2)

theorem wb_verum : WB M verumBranch := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  have := wb_verumIntroGraph (M := M); have := wb_qqVerumDef (M := M); have := wb_bitDef (M := M)
  simp only [verumBranch]
  wb_auto
  refine wb_exs_poly _ (by simp) ‘#0’ (fun V _ _ e x h => ⟨x, ?_, h⟩) (by wb_auto)
  have h' := h
  simp at h'
  exact le_of_lt (lt_of_mem h'.2)

theorem wb_weakening : WB M weakeningBranch := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  have := wb_wkRuleGraph (M := M); have := wb_fstIdxDef (M := M)
  have := wb_bitSubsetDef (M := M); have := wb_bitDef (M := M)
  simp only [weakeningBranch]
  wb_auto
  refine wb_exs_poly _ (by simp) ‘#0’ (fun V _ _ e x h => ⟨x, ?_, h⟩) (by wb_auto)
  have h' := h
  simp at h'
  simp [h'.1]

theorem wb_shift : WB M shiftBranch := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  have := wb_shiftRuleGraph (M := M); have := wb_fstIdxDef (M := M)
  have := wb_setShiftGraph (M := M); have := wb_bitDef (M := M)
  simp only [shiftBranch]
  wb_auto
  refine wb_exs_poly _ (by simp) ‘#0’ (fun V _ _ e x h => ⟨x, ?_, h⟩) (by wb_auto)
  have h' := h
  simp at h'
  simp [h'.1]
theorem wb_actualIdentity (T : SetTheory) [T.Δ₁] : WB M (actualIdentity T) := by
  rw [actualIdentity_eq]
  exact wb_identity

theorem wb_actualVerum (T : SetTheory) [T.Δ₁] : WB M (actualVerum T) := by
  rw [actualVerum_eq]
  exact wb_verum

theorem wb_actualWeakening (T : SetTheory) [T.Δ₁] : WB M (actualWeakening T) := by
  rw [actualWeakening_eq]
  exact wb_weakening

theorem wb_actualShift (T : SetTheory) [T.Δ₁] : WB M (actualShift T) := by
  rw [actualShift_eq]
  exact wb_shift
end DiophantineConsistency.PRAWitnessPositiveSimpleRules

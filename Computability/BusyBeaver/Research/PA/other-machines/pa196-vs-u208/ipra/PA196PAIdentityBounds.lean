import PA196PANegBoundTerms

/-! Unconditional witness bounds for both exact identity-rule branches of the
Foundation PA derivation core. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA196PAIdentityBounds
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAWitnessCalculus PRAWitnessArithmetic
open PRAWitnessTransfer PRAWitnessNegExistential

noncomputable def positiveBranch : ArithmeticSemisentence 2 :=
  “D C. ∃ s < D, ∃ p < D, !axLGraph D s p ∧ p ∈ s ∧
    ∃ np, !(negGraph ℒₒᵣ) np p ∧ np ∈ s”
noncomputable def negativeBranch : ArithmeticSemisentence 2 :=
  “D C. ∃ s < D, ∃ p < D, !axLGraph D s p ∧ p ∈ s ∧
    ∀ np, !(negGraph ℒₒᵣ) np p → np ∈ s”
noncomputable def actualPositive : ArithmeticSemisentence 2 :=
  match (Derivation.blueprint (𝗣𝗔 : ArithmeticTheory)).core.sigma.val with
  | .and _ (.or a _) => a
  | _ => ⊥
noncomputable def actualNegative : ArithmeticSemisentence 2 :=
  match (Derivation.blueprint (𝗣𝗔 : ArithmeticTheory)).core.pi.val with
  | .and _ (.or a _) => a
  | _ => ⊥
theorem actualPositive_eq : actualPositive = positiveBranch := by rfl
theorem actualNegative_eq : actualNegative = negativeBranch := by rfl

variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem wb_positiveIdentity : WB M actualPositive := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  rw [actualPositive_eq]
  have := wb_axLGraph (M := M); have := wb_bitDef (M := M); have := PA196PANegationBound.wb_negGraph (M := M)
  simp only [positiveBranch]
  wb_auto
  refine wb_exs_poly _ (by simp) ‘#1’ (fun V _ _ e x h => ⟨x, ?_, h⟩) (by wb_auto)
  have h' := h
  simp at h'
  exact le_of_lt (lt_of_mem h'.2)

theorem wb_negativeIdentity : WB M (∼actualNegative) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  rw [actualNegative_eq]
  have := wb_neg_axLGraph (M := M); have := wb_neg_bitDef (M := M)
  have := PA196PANegationBound.wb_negGraph (M := M)
  simp only [negativeBranch]
  wb_auto
  refine PA196PANegBoundTerms.wb_exs_neg (0 : Fin 4) _ (by simp) (by wb_auto) ?_
  intro V _ _ e y h
  have h' := h
  simp at h' ⊢
  exact h'.1

#print axioms wb_positiveIdentity
#print axioms wb_negativeIdentity
end PA196PAIdentityBounds

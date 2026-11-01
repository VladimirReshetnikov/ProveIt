import DiophantineConsistency.AdaptiveGap85Exists

/-! A sufficient existential normal-form interface for the reverse 85-to-86
zero transfer. This does not establish that such representatives exist. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85ExistentialNormalization
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 AdaptiveGap85Literal AdaptiveGap85Exists
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A zero need only have some positive-coordinate representative satisfying
    the reverse gap, rather than satisfy that bound itself. -/
def HasBoundedRepresentative (p : Fin 4 → ℕ) : Prop :=
  ∀ u : Fin 13 → V,
    InternalZero (positiveShift (expressionAt85 (fun j => (p j : ℤ)))) u →
    ∃ v : Fin 13 → V,
      InternalZero (positiveShift (expressionAt85 (fun j => (p j : ℤ)))) v ∧
      (v 1 + 1) + (v 2 + 1) < 1 + (v 0 + 1) * (p 0 : V)

/-- The existential normal form suffices for the reverse zero transfer. -/
theorem new_zero_to_old_of_representative (p : Fin 4 → ℕ)
    (hnorm : HasBoundedRepresentative (V := V) p) (u : Fin 13 → V)
    (hz : InternalZero (positiveShift (expressionAt85 (fun j => (p j : ℤ)))) u) :
    ∃ w : Fin 13 → V,
      InternalZero (positiveShift (AdaptiveDirectOrdinate86Literal.expressionAt86
        (fun j => (p j : ℤ)))) w := by
  obtain ⟨v, hv, hb⟩ := hnorm u hz
  exact new_natural_zero_to_old_of_bound p v hb hv

/-- Full no-zero equivalence, conditional only on the existential normal form. -/
theorem no_zero_iff_of_representative (p : Fin 4 → ℕ) (hb : 0 < (p 0 : V))
    (hnorm : HasBoundedRepresentative (V := V) p) :
    (∀ u : Fin 13 → V, ¬InternalZero (positiveShift (expressionAt85 (fun j => (p j : ℤ)))) u) ↔
    (∀ u : Fin 13 → V, ¬InternalZero
      (positiveShift (AdaptiveDirectOrdinate86Literal.expressionAt86 (fun j => (p j : ℤ)))) u) := by
  constructor
  · exact new_no_zero_implies_old p hb
  · intro hold u hz
    obtain ⟨w, hw⟩ := new_zero_to_old_of_representative p hnorm u hz
    exact hold w hw
end DiophantineConsistency.AdaptiveGap85ExistentialNormalization

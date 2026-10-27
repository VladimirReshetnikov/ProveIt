import ZFCinPA.ValidatorEnvironmentStreams222

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace LeanProofs.ZFCinPA.ValidatorEnvironmentStreams222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open ValidatorProvability222 ValidatorFormulaEncoder222
open ValidatorEnvironmentVacuity222 ValidatorEnvironmentAlpha222
open ValidatorEnvironmentStreams222
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem zero_seed (bound : V) :
    alternateStart bound 0 = 2*(bound+2)+1 := by simp [alternateStart]

theorem one_seed (bound : V) :
    alternateStart bound 1 = 2*(bound+2) := by simp [alternateStart]

/-- The successor streams overlap; alpha cannot be applied directly. -/
theorem not_apart_next (s : V) : ¬Apart s (s+2) := by
  intro h
  exact h 1 0 (by simp)

/-- Stored zero and repeated labels impose no distinctness condition. -/
theorem repeated_zero_labels (seed : V) :
    StreamFree (alternateStart ((0 : V)∷0∷0) seed) (0∷0∷0) :=
  alternateStart_free _ _ _ (le_refl _)

theorem fallback_one_avoided (bound seed F k : V) (hF : F≤bound) :
    alternateStart bound seed+2*k≠1 :=
  (alternateStart_free bound seed F hF k).1

theorem same_seed_relabel [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2] {p : V}
    (hp : IsFormula ℒₛₑₜ p) (F s : V) (hs : StreamFree s F) :
    CProv (wim (encode F 0 s p) (encode F 0 s p)) :=
  (encode_formula_relabel hp F s s hs hs).1

/-- Both overlapping-stream directions have actual internal checker witnesses. -/
theorem next_actual_witnesses [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2] {p : V}
    (hp : IsFormula ℒₛₑₜ p) (F s : V) (hs : StreamFree s F) :
    (∃ code : V, ArithmeticHistory222.value code =
      wim (encode F 0 s p) (encode F 0 (s+2) p)+1) ∧
    (∃ code : V, ArithmeticHistory222.value code =
      wim (encode F 0 (s+2) p) (encode F 0 s p)+1) :=
  encode_formula_next hp F s hs

#print axioms alternateStart_defined
#print axioms alternateStart_sigma1
#print axioms streamEnv_of_lt
#print axioms streamFree_of_bounds
#print axioms apart_of_mod_ne
#print axioms alternateStart_resources
#print axioms encode_formula_relabel
#print axioms encode_formula_next
#print axioms zero_seed
#print axioms one_seed
#print axioms not_apart_next
#print axioms repeated_zero_labels
#print axioms fallback_one_avoided
#print axioms same_seed_relabel
#print axioms next_actual_witnesses
end LeanProofs.ZFCinPA.ValidatorEnvironmentStreams222Checks

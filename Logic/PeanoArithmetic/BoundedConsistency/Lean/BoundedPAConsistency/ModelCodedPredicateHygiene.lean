import BoundedPAConsistency.ModelCodedPredicateTemplate

/-!
# Heterogeneous hygiene for model-coded predicate specialization

The inserted arithmetic matrix may have an arbitrary internal code and free
parameters. Shifting the matrix together with the standard source formula
commutes with translation, as does opening a universal-premise variable.
No FVFree hypothesis is needed.

These are syntax identities. This module supplies no proof-template compiler,
arbitrary internally coded source-proof translation, or PA consistency theorem.
-/
namespace LeanProofs.BoundedPAConsistency.ModelCodedPredicateHygiene

open LeanProofs.BoundedPAConsistency.ModelCodedPredicateTemplate
open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]
variable {arity n : ℕ}

/-- Shift the inserted matrix along with the source free-variable shift. -/
theorem translateFormula_shift_heterogeneous
    (S : Bootstrapping.Semiformula V ℒₒᵣ arity)
    (p : Semiproposition (templateLanguage arity) n) :
    translateFormula S.shift (Rewriting.shift p) =
      (translateFormula S p).shift := by
  induction p using FirstOrder.Semiformula.rec' with
  | hverum => simp [translateFormula]
  | hfalsum => simp [translateFormula]
  | @hrel n k r v =>
      rcases r with r | r
      · simp [translateFormula, translateTerm_shift, Matrix.map,
          Function.comp_def]
      · cases r
        simp [translateFormula, Semiformula.shift_substs,
          Matrix.map, Function.comp_def]
  | @hnrel n k r v =>
      rcases r with r | r
      · simp [translateFormula, translateTerm_shift, Matrix.map,
          Function.comp_def]
      · cases r
        simp [translateFormula, Semiformula.shift_substs,
          Matrix.map, Function.comp_def]
  | hand p q hp hq => simp [translateFormula, hp, hq]
  | hor p q hp hq => simp [translateFormula, hp, hq]
  | hall p hp => simp [translateFormula, hp]
  | hexs p hp => simp [translateFormula, hp]

/-- The corresponding identity at a fresh universal-premise variable. -/
theorem translateFormula_free_heterogeneous
    (S : Bootstrapping.Semiformula V ℒₒᵣ arity)
    (p : Semiproposition (templateLanguage arity) 1) :
    translateFormula S.shift (Rewriting.free p) =
      (translateFormula S p).free := by
  rw [← LawfulSyntacticRewriting.app_subst_fbar_zero_comp_shift_eq_free]
  rw [translateFormula_subst, translateFormula_shift_heterogeneous]
  unfold Bootstrapping.Semiformula.free
  congr 1
  funext i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  rfl

end LeanProofs.BoundedPAConsistency.ModelCodedPredicateHygiene

import Mathlib.MeasureTheory.Constructions.Pi
import OAI.Combinatorics.Progressions.Estimates.SelectedCoefficientEvaluation

namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {I J : Type*} [Fintype I] (s : I ↪ J)
variable (X : J → Type*) [∀ j, MeasurableSpace (X j)]

noncomputable def selectedDependentEquiv :
    ((∀ j : UnselectedColumn s, X j.val) × (∀ i, X (s i))) ≃ᵐ (∀ j, X j) :=
  (MeasurableEquiv.sumPiEquivProdPi
    (fun j : UnselectedColumn s ⊕ I => X (selectedFreeFirstEquiv s j))).symm.trans
      (MeasurableEquiv.piCongrLeft X (selectedFreeFirstEquiv s))

theorem selectedDependentEquiv_symm_unselected (f : ∀ j, X j)
    (j : UnselectedColumn s) :
    ((selectedDependentEquiv s X).symm f).1 j = f j.val := rfl

theorem selectedDependentEquiv_symm_selected (f : ∀ j, X j) (i : I) :
    ((selectedDependentEquiv s X).symm f).2 i = f (s i) := rfl

theorem selectedDependentEquiv_eq_of_coordinates (f : ∀ j, X j)
    (p : (∀ j : UnselectedColumn s, X j.val) × (∀ i, X (s i)))
    (hfree : ∀ j : UnselectedColumn s, f j.val = p.1 j)
    (hselected : ∀ i, f (s i) = p.2 i) :
    f = selectedDependentEquiv s X p := by
  apply (selectedDependentEquiv s X).symm.injective
  rw [MeasurableEquiv.symm_apply_apply]
  exact Prod.ext (funext hfree) (funext hselected)

theorem selectedDependentEquiv_measurePreserving [Fintype J]
    (μ : ∀ j, Measure (X j)) [∀ j, SigmaFinite (μ j)] :
    MeasurePreserving (selectedDependentEquiv s X)
      ((Measure.pi (fun j : UnselectedColumn s => μ j.val)).prod
        (Measure.pi (fun i => μ (s i)))) (Measure.pi μ) :=
  (measurePreserving_piCongrLeft μ (selectedFreeFirstEquiv s)).comp
    (measurePreserving_sumPiEquivProdPi_symm
      (fun j : UnselectedColumn s ⊕ I => μ (selectedFreeFirstEquiv s j)))

end Erdos3

end

end OAI

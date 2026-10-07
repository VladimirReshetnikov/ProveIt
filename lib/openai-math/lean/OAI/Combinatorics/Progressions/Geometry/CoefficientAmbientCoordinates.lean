import OAI.Combinatorics.Progressions.Fourier.CanonicalDensityFourier

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

variable {K : Type*} {m : ℕ} {J : Fin m → Type*}

abbrev CoefficientAmbientIndex (K : Type*) {m : ℕ} (J : Fin m → Type*) :=
  Σ s : CoefficientSlot K m, J s.1

def coefficientAmbientSlice (s : CoefficientSlot K m)
    (v : CoefficientAmbientIndex K J → UnitAddCircle) : J s.1 → UnitAddCircle :=
  fun i => v ⟨s, i⟩

noncomputable def coefficientAmbientTorus (U : ∀ j, Submodule ℝ (J j → ℝ))
    (x : CoefficientTorus (K := K) U) : CoefficientAmbientIndex K J → UnitAddCircle :=
  fun t => subspaceAmbientTorus (U t.1.1) (coefficientCoordinateTorus U x t.1) t.2

theorem coefficientAmbientTorus_mk (U : ∀ j, Submodule ℝ (J j → ℝ))
    (x : CoefficientArray (K := K) U) (t : CoefficientAmbientIndex K J) :
    coefficientAmbientTorus U (QuotientAddGroup.mk' (coefficientIntegerLattice U) x) t =
      ((x t.1).val t.2 : UnitAddCircle) := rfl

variable [Fintype K] [∀ j, Fintype (J j)]

theorem coefficientAmbientSlice_lipschitz (s : CoefficientSlot K m) :
    LipschitzWith 1 (coefficientAmbientSlice (J := J) s) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro i
  exact dist_le_pi_dist x y ⟨s, i⟩

theorem coefficientAmbientTorus_character (U : ∀ j, Submodule ℝ (J j → ℝ))
    (frequency : CoefficientAmbientIndex K J → ℤ) (x : CoefficientTorus (K := K) U) :
    (∏ t, CircleFourier.character (frequency t • coefficientAmbientTorus U x t)) =
      coefficientTorusCharacter U (coefficientSlotFrequency (fun s i => frequency ⟨s, i⟩)) x := by
  rw [coefficientTorusCharacter_slot_product, Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro s _
  exact subspaceAmbientTorus_character (U s.1) (fun i => frequency ⟨s, i⟩)
    (coefficientCoordinateTorus U x s)

end Erdos3.VectorPolynomial

end

end OAI

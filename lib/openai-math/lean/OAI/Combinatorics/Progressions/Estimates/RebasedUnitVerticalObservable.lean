import OAI.Combinatorics.Progressions.Nilpotent.RankAdaptedNiltest

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

open Module
open scoped TensorProduct NNReal

variable {L I : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {T : Subgroup D.RealGroup} {p q : ℝ}

noncomputable def rebase (V : D.UnitVerticalObservable T I p) (F : D.AdaptedModelData) (H : ℕ)
    (hH : ∀ i j, RationalHeightLE (D.basis.repr (F.basis i) j) H)
    (hLip : (V.lipBound * coordinateLipschitzBound d (finrank ℚ L) H : ℝ) ≤ Real.exp q)
    (hFreq : ∀ i, rationalLogHeight (V.frequency (F.basis i)) ≤ q) :
    F.model.UnitVerticalObservable T I q where
  observable := V.observable
  unit := V.unit
  norm := V.norm
  lipBound := V.lipBound * coordinateLipschitzBound d (finrank ℚ L) H
  lip_bound := hLip
  lipschitz := by
    let := F.model.metricSpace
    intro i
    let U : D.Niltest (fun _ : Unit => 1) := {
      orbit := 1
      observable := V.observable i
      normBound := 1
      lipBound := V.lipBound
      norm_le := V.norm i
      lipschitz := V.lipschitz i
    }
    exact (F.rebaseNiltest H hH U).lipschitz
  frequency := V.frequency
  height := hFreq
  vertical := V.vertical
  integral := V.integral

theorem rebase_observable (V : D.UnitVerticalObservable T I p) (F : D.AdaptedModelData) (H : ℕ)
    (hH : ∀ i j, RationalHeightLE (D.basis.repr (F.basis i) j) H)
    (hLip : (V.lipBound * coordinateLipschitzBound d (finrank ℚ L) H : ℝ) ≤ Real.exp q)
    (hFreq : ∀ i, rationalLogHeight (V.frequency (F.basis i)) ≤ q) :
    (V.rebase F H hH hLip hFreq).observable = V.observable := rfl

end Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

end

end OAI

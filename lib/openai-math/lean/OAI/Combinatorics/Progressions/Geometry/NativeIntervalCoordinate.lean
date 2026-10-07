import OAI.Combinatorics.Progressions.Fourier.BohrNiltestBudget

namespace OAI

section

namespace Erdos3.RationalTorus

open scoped TensorProduct NNReal

noncomputable def intervalOrbit (N : ℕ) :
    (nilmanifold 1).filtration.realification.PolynomialOrbit (fun _ : Unit => 1) :=
  affineOrbit 1 (fun _ => 0) (fun _ : Unit => fun _ => 1 / (N : ℝ))

theorem intervalOrbit_phase (N : ℕ) [NeZero N] (x : ZMod N) :
    phaseProjection 1 ((nilmanifold 1).cyclicOrbitPoint (intervalOrbit N) N (fun _ : Unit => x)) 0 =
      ZMod.toAddCircle x := by
  unfold RationalFilteredNilmanifold.cyclicOrbitPoint intervalOrbit
  rw [phaseProjection_mk, affineOrbit_phases]
  simp [ZMod.toAddCircle_apply, div_eq_mul_inv]

theorem intervalCoordinate_lipschitz :
    letI := (nilmanifold 1).metricSpace
    LipschitzWith 1 (fun z => phaseProjection 1 z 0) := by
  let := (nilmanifold 1).metricSpace
  apply LipschitzWith.of_dist_le_mul
  intro x y
  exact (dist_le_pi_dist (phaseProjection 1 x) (phaseProjection 1 y) 0).trans
    ((phaseProjection_lipschitz 1).dist_le_mul x y)

end Erdos3.RationalTorus

end

end OAI

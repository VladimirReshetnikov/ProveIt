import OAI.Combinatorics.Progressions.Estimates.PreparedModularGeneralDetectorLateCoarseConsumer

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

structure PreparedCenteredMarginalProjectionBounds (nX : ℕ) (Pmaster Plate Pproj : ℝ) : Prop where
  Pproj_nonneg : 0 ≤ Pproj
  master_projection : Pmaster ≤ Pproj
  late_projection : Plate ≤ Pproj
  m_projection : (m : ℝ) ≤ Pproj
  variables_projection : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pproj
  X_projection : (Fintype.card (Fin nX) : ℝ) ≤ Pproj
  frame_projection : (Fintype.card (Option (LayerSamplerVariables G I n B) × Fin nX) : ℝ) ≤ Pproj
  coefficient_projection : ∀ j : Fin m,
    (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Pproj
  I_projection : ∀ j, (Fintype.card (I j) : ℝ) ≤ Pproj
  n_projection : ∀ j, (n j : ℝ) ≤ Pproj
  J_projection : ∀ j, (Fintype.card (J j) : ℝ) ≤ Pproj
  Rinv_projection : ∀ j, (R j)⁻¹ ≤ Real.exp Pproj
  σinv_projection : ∀ j, (σ j)⁻¹ ≤ Real.exp Pproj
  S_projection : (S.value : ℝ) ≤ Real.exp Pproj
  root_projection : allocatedPhysicalRootBudget B U basis S (fun _ => 0) ≤ Real.exp Pproj
  profile_projection : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Pproj

theorem preparedCenteredMarginalProjectionBounds
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {s : ℕ} {Pmaster Plate D : ℝ} (hMaster : 0 ≤ Pmaster) (hLate : Pmaster ≤ Plate)
    (hd : AllocatedComparisonDimensions (G := G) B (Fin (s + 1))
      (fun j : Fin m => (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1) : Type)) D)
    (hD : D ≤ Pmaster) {nX : ℕ} (hnX : (nX : ℝ) ≤ Pmaster)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp Pmaster)
    (hσLate : ∀ j, (σ j)⁻¹ ≤ Real.exp Plate)
    (hLLate : (S.value : ℝ) ≤ Real.exp Plate) :
    let r := preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m s)
      (s + 1) Pmaster Plate
    PreparedCenteredMarginalProjectionBounds B U basis S nX Pmaster Plate r.Pproj := by
  intro r
  have hproj : r.Pproj = 4 * (Plate + 8) ^ 2 := rfl
  have hPlate : 0 ≤ Plate := hMaster.trans hLate
  have hLproj : Plate ≤ r.Pproj := by
    nlinarith only [hproj, hPlate, sq_nonneg Plate]
  have hExpLate := Real.exp_le_exp.mpr hLproj
  have hPproj : Pmaster ≤ r.Pproj := hLate.trans hLproj
  have h2Pproj : 2 * Pmaster ≤ r.Pproj := by
    nlinarith only [hproj, hPlate, hLate, sq_nonneg Plate]
  have hframeProj : (2 * Pmaster + 1) * Pmaster ≤ r.Pproj := by
    have hsq : Pmaster^2 ≤ Plate^2 := pow_le_pow_left₀ hMaster hLate 2
    nlinarith only [hproj, hPlate, hLate, hsq, sq_nonneg Plate]
  have hExp := Real.exp_le_exp.mpr hPproj
  have hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ 2 * Pmaster :=
    (preparedModularGeneralDetector_variable_count B
      (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)) hd).trans
        (by linarith only [hD])
  have hframe : (Fintype.card (Option (LayerSamplerVariables G I n B) × Fin nX) : ℝ) ≤ r.Pproj := by
    rw [Fintype.card_prod, Fintype.card_option, Fintype.card_fin, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    exact (mul_le_mul (add_le_add_left hvars 1) hnX (Nat.cast_nonneg _) (by positivity)).trans
      (by simpa only [add_comm] using hframeProj)
  obtain ⟨hI, hn⟩ := preparedModularGeneralDetector_layer_axes B
    (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)) hd
  have hJ (j : Fin m) : (Fintype.card (J j) : ℝ) ≤ r.Pproj :=
    (Nat.cast_le.mpr (allocatedAmbientDimension_le_axes U basis o j)).trans
      (hd.axes.trans (hD.trans hPproj))
  have hWproj : allocatedPhysicalRootBudget B U basis S (fun _ => 0) ≤ Real.exp r.Pproj :=
    (preparedModularGeneralDetector_physical_root B
      (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)) U basis S hd
        (hD.trans hLate) hLLate).trans
      (Real.exp_le_exp.mpr (by nlinarith only [hproj, hPlate, hLate, sq_nonneg Plate]))
  exact {
    Pproj_nonneg := hMaster.trans hPproj
    master_projection := hPproj
    late_projection := hLproj
    m_projection := hd.degree.trans (hD.trans hPproj)
    variables_projection := hvars.trans h2Pproj
    X_projection := by simpa only [Fintype.card_fin] using hnX.trans hPproj
    frame_projection := hframe
    coefficient_projection := fun j => (hd.coefficients j).trans (hD.trans hPproj)
    I_projection := fun j => (hI j).trans (hD.trans hPproj)
    n_projection := fun j => (hn j).trans (hD.trans hPproj)
    J_projection := hJ
    Rinv_projection := fun j => (hRP j).trans hExp
    σinv_projection := fun j => (hσLate j).trans hExpLate
    S_projection := hLLate.trans hExpLate
    root_projection := hWproj
    profile_projection := ((hd.profile.trans (hD.trans hPproj)).trans
      (by linarith [Real.add_one_le_exp r.Pproj])) }

end Erdos3.VectorPolynomial

end

end OAI

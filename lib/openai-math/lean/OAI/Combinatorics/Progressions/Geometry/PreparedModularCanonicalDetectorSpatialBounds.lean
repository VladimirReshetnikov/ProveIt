import OAI.Combinatorics.Progressions.Estimates.NormalizedTupleParameterBounds

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ b, Fintype (B b)]

theorem preparedModularDetector_narrow_width {q Mk nX : ℕ} (selection : Fin q ↪ G)
    {Pphysical coarseTarget : ℝ} (hp : 0 ≤ Pphysical) (htarget : 0 ≤ coarseTarget)
    (hMk : (Mk : ℝ) ≤ Real.exp Pphysical) (hq : ((q + 1 : ℕ) : ℝ) ≤ Pphysical)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pphysical)
    (hnX : (nX : ℝ) ≤ Pphysical) :
    let R := spatialPrimitiveEnvelope Pphysical coarseTarget 0
    let ξLog := 2 * (R + spatialTupleToleranceLog R) + 4
    0 ≤ ξLog ∧
      (normalizedTupleNarrowWidth (Fin nX) (PrincipalTupleIndex B (layerSamplerDegree I n))
        selection Mk Pphysical coarseTarget)⁻¹ ≤ Real.exp ξLog := by
  intro R ξLog
  have hG := (Nat.cast_le.mpr (allocatedKernelVariables_card_le_variables (G := G) B)).trans hvars
  have hN := (Nat.cast_le.mpr (allocatedPrincipalIndex_card_le_variables (G := G) B)).trans hvars
  have hX : (Fintype.card (Fin nX) : ℝ) ≤ Pphysical := by simpa only [Fintype.card_fin] using hnX
  have hR : 0 ≤ R := (spatialPrimitiveEnvelope_bounds hp htarget (le_refl 0)).1
  have ht := spatialTupleToleranceLog_nonneg hR
  refine ⟨by dsimp only [ξLog]; positivity, ?_⟩
  exact (normalizedTupleEarlyParameters_bound
    (N := PrincipalTupleIndex B (layerSamplerDegree I n)) (X := Fin nX)
    selection hp htarget (le_refl 0) hMk hq hG hN hX).2

theorem preparedModularDetector_physical_root_of_variables
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    {P : ℝ} (_hP : 0 ≤ P)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (hS : (S.value : ℝ) ≤ Real.exp P) :
    allocatedPhysicalRootBudget B U basis S (fun _ => 0) ≤ Real.exp (2 * P + 8) := by
  have hvarsExp : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp P :=
    hvars.trans (by linarith [Real.add_one_le_exp P])
  rw [allocatedPhysicalRootBudget_zero]
  calc
    _ ≤ Real.exp P * Real.exp P :=
      mul_le_mul hvarsExp hS (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp (2 * P) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem preparedModularDetector_projection_budget
    {K : Type*} [Fintype K] {nX : ℕ} {P Pphysical ξLog W : ℝ}
    (hP : 0 ≤ P) (hphysical : Pphysical ≤ P) (hξLog : ξLog ≤ P)
    (hvars : (Fintype.card K : ℝ) ≤ P) (hnX : (nX : ℝ) ≤ P)
    (hroot : W ≤ Real.exp (2 * P + 8)) :
    let Pproj := 4 * (P + 8) ^ 2
    0 ≤ Pproj ∧ P ≤ Pproj ∧ Pphysical ≤ Pproj ∧ ξLog ≤ Pproj ∧
      2 * P + 8 ≤ Pproj ∧ (Fintype.card (Option K × Fin nX) : ℝ) ≤ Pproj ∧
      W ≤ Real.exp Pproj := by
  intro Pproj
  have hPQ : P ≤ Pproj := by dsimp only [Pproj]; nlinarith [sq_nonneg P]
  have hrootQ : 2 * P + 8 ≤ Pproj := by dsimp only [Pproj]; nlinarith [sq_nonneg P]
  have hcard : (Fintype.card (Option K × Fin nX) : ℝ) ≤ (P + 1) * P := by
    simp only [Fintype.card_prod, Fintype.card_option, Fintype.card_fin,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    exact mul_le_mul (add_le_add hvars (le_refl 1)) hnX (Nat.cast_nonneg _) (by linarith)
  have hprod : (P + 1) * P ≤ Pproj := by dsimp only [Pproj]; nlinarith [sq_nonneg P]
  exact ⟨hP.trans hPQ, hPQ, hphysical.trans hPQ, hξLog.trans hPQ,
    hrootQ, hcard.trans hprod, hroot.trans (Real.exp_le_exp.mpr hrootQ)⟩

end Erdos3.VectorPolynomial

end

end OAI

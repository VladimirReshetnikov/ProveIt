import OAI.Combinatorics.Progressions.Estimates.LowerStepSquare

namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι κ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

variable (e : Basis ι ℚ L) (b : Basis κ ℚ L)
  (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
  (l : ℕ) (hl : 0 < l) (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
  (N : ℕ) (hinner : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ)

noncomputable def realifiedCentralBasisAction (j : κ) (hj : ∀ w : L, ⁅b j, w⁆ = 0) :
    letI := realificationQuotientMetricSpace e Γ l hl houter
    CircleFourier.IsometricCircleAction
      (NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil) ⧸
        Γ.map realificationHom) :=
  centralBCHCircleAction (e.baseChange ℝ) (Γ.map realificationHom)
    (realification_subgroup_closed_discrete e Γ l hl houter).1
    ((N : ℝ) • (b.baseChange ℝ) j) (scaled_real_basis_central b j hj N)
    (scaled_real_basis_mem_realification b Γ N hinner j)

theorem realifiedCentralBasisAction_act_coe (j : κ) (hj : ∀ w : L, ⁅b j, w⁆ = 0)
    (r : ℝ) (x : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s
      (realification_lowerCentralSeries_eq_bot hnil) ⧸ Γ.map realificationHom) :
    letI := realificationQuotientMetricSpace e Γ l hl houter
    (realifiedCentralBasisAction e b Γ l hl houter N hinner j hj).act (r : CircleFourier.Circle) x =
      realBCHLine (hnil := realification_lowerCentralSeries_eq_bot hnil)
        ((N : ℝ) • (b.baseChange ℝ) j) r • x := by
  let := realificationQuotientMetricSpace e Γ l hl houter
  exact centralBCHCircleAction_act_coe _ _ _ _ _ _ r x

theorem realifiedCentralBasisAction_displacement (j : κ) (hj : ∀ w : L, ⁅b j, w⁆ = 0)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ i, |(e.repr (b j) i : ℝ)| ≤ B)
    (t : CircleFourier.Circle) (x : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s
      (realification_lowerCentralSeries_eq_bot hnil) ⧸ Γ.map realificationHom) :
    letI := realificationQuotientMetricSpace e Γ l hl houter
    dist ((realifiedCentralBasisAction e b Γ l hl houter N hinner j hj).act t x) x ≤
      ((Fintype.card ι : ℝ) + 1) * ((N : ℝ) * B) * ‖t‖ := by
  let := realificationQuotientMetricSpace e Γ l hl houter
  apply (centralBCHCircleAction_displacement _ _ _ _ _ _ t x).trans
  exact mul_le_mul_of_nonneg_right (scaled_real_basis_coordinate_bound e b N j hB hb) (norm_nonneg t)

theorem realifiedCentralBasisAction_commutes (i j : κ)
    (hi : ∀ w : L, ⁅b i, w⁆ = 0) (hj : ∀ w : L, ⁅b j, w⁆ = 0) :
    letI := realificationQuotientMetricSpace e Γ l hl houter
    (realifiedCentralBasisAction e b Γ l hl houter N hinner i hi).Commutes
      (realifiedCentralBasisAction e b Γ l hl houter N hinner j hj) := by
  let := realificationQuotientMetricSpace e Γ l hl houter
  exact centralBCHCircleAction_commutes _ _ _ _ _ _ _ _ _

end Erdos3

end

end OAI

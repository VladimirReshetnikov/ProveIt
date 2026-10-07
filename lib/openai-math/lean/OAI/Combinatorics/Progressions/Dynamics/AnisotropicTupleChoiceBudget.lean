import OAI.Combinatorics.Progressions.Estimates.AnisotropicTupleErrorChoice
import OAI.Combinatorics.Progressions.Geometry.CoefficientSquareSpatialBudget

namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped NNReal

noncomputable def anisotropicTupleEarlyBudget {I G : Type*} [Fintype I] [Fintype G]
    (N : Type*) [Fintype N] (s : I ↪ G) (p E : ℝ) : ℝ :=
  p + (p ^ 3 + anisotropicSpatialCapLog p) + (coefficientErrorVolumeLog p + 4) +
    spatialDisplacementLog (Fintype.card (Unit ⊕ I)) (Fintype.card (UnselectedColumn s ⊕ N))
      (Fintype.card (UnselectedColumn s)) (Fintype.card N) p + E

theorem anisotropicTupleEarlyBudget_bounds {I G : Type*} [Fintype I] [Fintype G]
    (N : Type*) [Fintype N] (s : I ↪ G) {p E : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E) :
    let Q := anisotropicTupleEarlyBudget N s p E
    0 ≤ Q ∧ p ≤ Q ∧ p ^ 3 + anisotropicSpatialCapLog p ≤ Q ∧
      coefficientErrorVolumeLog p + 4 ≤ Q ∧
      spatialDisplacementLog (Fintype.card (Unit ⊕ I)) (Fintype.card (UnselectedColumn s ⊕ N))
        (Fintype.card (UnselectedColumn s)) (Fintype.card N) p ≤ Q ∧ E ≤ Q := by
  have hcap : 0 ≤ p ^ 3 + anisotropicSpatialCapLog p := by
    have := anisotropicSpatialCapLog_nonneg hp
    positivity
  have hvol : 0 ≤ coefficientErrorVolumeLog p + 4 := by
    unfold coefficientErrorVolumeLog
    positivity
  have hdis : 0 ≤ spatialDisplacementLog (Fintype.card (Unit ⊕ I))
      (Fintype.card (UnselectedColumn s ⊕ N)) (Fintype.card (UnselectedColumn s))
      (Fintype.card N) p := by
    unfold spatialDisplacementLog spatialProfileLog
    positivity
  dsimp only [anisotropicTupleEarlyBudget]
  constructor
  · positivity
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem anisotropicTupleEarlyWidth_inv_bound {G N X : Type*}
    [Fintype G] [Fintype N] [Fintype X] (q : ℕ) (s : Fin q ↪ G)
    {M : ℕ} {p E ε : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E)
    (hMp : (M : ℝ) ≤ Real.exp p) (hX : (Fintype.card X : ℝ) ≤ p)
    (hε : 0 < ε) (hεE : ε⁻¹ ≤ Real.exp E) :
    let t := spatialTupleTolerance (Fintype.card X)
      (Real.exp (p ^ 3 + anisotropicSpatialCapLog p)) (Real.exp (coefficientErrorVolumeLog p + 4)) ε
    let ξ := twoTermErrorWidth (smoothSpatialDisplacementCost N s M) t
    let Q := anisotropicTupleEarlyBudget N s p E
    ξ⁻¹ ≤ Real.exp (2 * (Q + spatialTupleToleranceLog Q) + 4) := by
  have h := anisotropicTupleEarlyBudget_bounds N s hp hE
  exact spatialTupleEarlyWidth_inv_bound (Fintype.card X) (Real.exp_nonneg _) (Real.exp_nonneg _)
    (smoothSpatialDisplacementCost_nonneg N s M) hε h.1 (hX.trans h.2.1)
    (Real.exp_le_exp.mpr h.2.2.1) (Real.exp_le_exp.mpr h.2.2.2.1)
    ((smoothSpatialDisplacementCost_le_exp N s hp hMp).trans (Real.exp_le_exp.mpr h.2.2.2.2.1))
    (hεE.trans (Real.exp_le_exp.mpr h.2.2.2.2.2))

theorem spatialPeriodDensityCap_le_exp {G : Type*} [Fintype G] (q : ℕ) (s : Fin q ↪ G)
    {m M period : ℕ} {p : ℝ} (hp : 0 ≤ p) (hM : 0 < M)
    (hm : ((m + 1 : ℕ) : ℝ) ≤ p) (hq : ((q + 1 : ℕ) : ℝ) ≤ p)
    (hG : (Fintype.card G : ℝ) ≤ p) (hMp : (M : ℝ) ≤ Real.exp p)
    (hperiod : period ≤ M ^ (m + 1)) :
    (period : ℝ) ^ Fintype.card (Unit ⊕ Fin q) *
      anisotropicSpatialDensityCap s (1 / (M : ℝ)) ≤
        Real.exp (p ^ 3 + anisotropicSpatialCapLog p) := by
  have hj : (Fintype.card (Unit ⊕ Fin q) : ℝ) ≤ p := by
    simpa only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin, Nat.add_comm 1] using hq
  have hper := coefficientErrorPeriod_exp_sq hp hm hMp hperiod
  have hΓ : (period : ℝ) ^ Fintype.card (Unit ⊕ Fin q) ≤ Real.exp (p ^ 3) := by
    have h := pow_le_exp_mul_of_le_exp (Nat.cast_nonneg period) hper (sq_nonneg p) _ hj
    exact h.trans_eq (congrArg Real.exp (by ring))
  have hcap := anisotropicSpatialDensityCap_exp_bound s hp hM hMp hj hG
  have hcap0 := anisotropicSpatialDensityCap_nonneg s (by positivity : 0 ≤ 1 / (M : ℝ))
  calc
    _ ≤ Real.exp (p ^ 3) * Real.exp (anisotropicSpatialCapLog p) := by gcongr
    _ = _ := (Real.exp_add _ _).symm

end Erdos3

end

end OAI

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import OAI.Combinatorics.Progressions.Estimates.ScalarBadSublevelRamp
import OAI.Combinatorics.Progressions.Estimates.UnitBoundProductDifference
import OAI.Combinatorics.Progressions.Linear.SpatialMatrixBlockWideProbability

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem unitTestClip_lipschitz : LipschitzWith 1 unitTestClip :=
  (LipschitzWith.id.const_min 1).const_max (-1)

theorem unitTestClip_eq_self {x : ℝ} (hx : |x| ≤ 1) : unitTestClip x = x := by
  rcases abs_le.mp hx with ⟨hl, hu⟩
  simp only [unitTestClip, min_eq_right hu, max_eq_right hl]

theorem unitTestClip_norm_le_one (x : ℝ) : ‖unitTestClip x‖ ≤ 1 := by
  simpa only [Real.norm_eq_abs, abs_le, Set.mem_Icc] using unitTestClip_mem x

noncomputable def clippedSelectedDeterminant {A : Type*} (n : ℕ)
    (coords : Fin n → Fin n → A) (x : A → ℝ) : ℝ :=
  Matrix.det (Matrix.of (fun i j => unitTestClip (x (coords i j))))

theorem clippedSelectedDeterminant_eq_det {A : Type*} (n : ℕ)
    (coords : Fin n → Fin n → A) (x : A → ℝ)
    (hx : ∀ i j, |x (coords i j)| ≤ 1) :
    clippedSelectedDeterminant n coords x = Matrix.det (Matrix.of (fun i j => x (coords i j))) := by
  unfold clippedSelectedDeterminant
  congr 1
  funext i j
  exact unitTestClip_eq_self (hx i j)

private theorem real_perm_sign_norm {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ‖((Equiv.Perm.sign σ : ℤ) : ℝ)‖ = 1 := by
  rw [Real.norm_eq_abs, ← Int.cast_abs, Equiv.Perm.sign_abs, Int.cast_one]

theorem clippedSelectedDeterminant_lipschitz {A : Type*} [Fintype A]
    (n : ℕ) (coords : Fin n → Fin n → A) :
    LipschitzWith ((n * n.factorial : ℕ) : ℝ≥0) (clippedSelectedDeterminant n coords) := by
  classical
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hprod (σ : Equiv.Perm (Fin n)) :
      ‖(∏ i, unitTestClip (x (coords (σ i) i))) -
        ∏ i, unitTestClip (y (coords (σ i) i))‖ ≤ (n : ℝ) * dist x y := by
    calc
      _ ≤ ∑ i : Fin n, ‖unitTestClip (x (coords (σ i) i)) -
          unitTestClip (y (coords (σ i) i))‖ :=
        VectorPolynomial.norm_finset_prod_sub_prod_le_sum Finset.univ _ _
          (fun i _ => unitTestClip_norm_le_one _) (fun i _ => unitTestClip_norm_le_one _)
      _ ≤ ∑ _i : Fin n, dist x y := by
        apply Finset.sum_le_sum
        intro i hi
        rw [← dist_eq_norm]
        exact (unitTestClip_lipschitz.dist_le_mul _ _).trans (by
          simpa using dist_le_pi_dist x y (coords (σ i) i))
      _ = (n : ℝ) * dist x y := by simp
  rw [dist_eq_norm, clippedSelectedDeterminant, clippedSelectedDeterminant,
    Matrix.det_apply', Matrix.det_apply', ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ σ : Equiv.Perm (Fin n),
        ‖((Equiv.Perm.sign σ : ℤ) : ℝ) * (∏ i, unitTestClip (x (coords (σ i) i))) -
          ((Equiv.Perm.sign σ : ℤ) : ℝ) * (∏ i, unitTestClip (y (coords (σ i) i)))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin n), (n : ℝ) * dist x y := by
      apply Finset.sum_le_sum
      intro σ hσ
      rw [← mul_sub, norm_mul, real_perm_sign_norm, one_mul]
      exact hprod σ
    _ = ↑((n * n.factorial : ℕ) : ℝ≥0) * dist x y := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, NNReal.coe_mul, NNReal.coe_natCast]
      ring

end Erdos3

end

section

namespace Erdos3
open scoped NNReal Classical

noncomputable def normalizedDeterminantCutoff {A : Type*} (n : ℕ)
    (coords : Fin 2 → Fin n → Fin n → A) (κ : ℝ) (x : A → ℝ) : ℝ :=
  max (scalarBadSublevelRamp κ (clippedSelectedDeterminant n (coords 0) x))
    (scalarBadSublevelRamp κ (clippedSelectedDeterminant n (coords 1) x))

theorem normalizedDeterminantCutoff_range {A : Type*} (n : ℕ)
    (coords : Fin 2 → Fin n → Fin n → A) (κ : ℝ) (x : A → ℝ) :
    normalizedDeterminantCutoff n coords κ x ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨(scalarBadSublevelRamp_range κ _).1.trans (le_max_left _ _),
    max_le (scalarBadSublevelRamp_range κ _).2 (scalarBadSublevelRamp_range κ _).2⟩

theorem normalizedDeterminantCutoff_lipschitz {A : Type*} [Fintype A] (n : ℕ)
    (coords : Fin 2 → Fin n → Fin n → A) {κ : ℝ} (hκ : 0 < κ) :
    LipschitzWith (⟨2 / κ, by positivity⟩ * ((n * n.factorial : ℕ) : ℝ≥0))
      (normalizedDeterminantCutoff n coords κ) := by
  unfold normalizedDeterminantCutoff
  have h (b : Fin 2) := (scalarBadSublevelRamp_lipschitz hκ).comp
    (clippedSelectedDeterminant_lipschitz n (coords b))
  simpa only [max_self, Function.comp_def] using (h 0).max (h 1)

theorem normalizedDeterminantCutoff_eq_one {A : Type*} (n : ℕ)
    (coords : Fin 2 → Fin n → Fin n → A) {κ : ℝ} (hκ : 0 < κ)
    (x : A → ℝ) (hx : ∀ b i j, |x (coords b i j)| ≤ 1)
    (hbad : ∃ b : Fin 2, |Matrix.det (fun i j => x (coords b i j))| ≤ κ / 2) :
    normalizedDeterminantCutoff n coords κ x = 1 := by
  obtain ⟨b, hb⟩ := hbad
  have he : clippedSelectedDeterminant n (coords b) x = Matrix.det (fun i j => x (coords b i j)) := by
    unfold clippedSelectedDeterminant
    congr 1
    funext i j
    exact unitTestClip_eq_self (hx b i j)
  have hb1 : scalarBadSublevelRamp κ (clippedSelectedDeterminant n (coords b) x) = 1 :=
    scalarBadSublevelRamp_eq_one hκ (by rw [he]; exact hb)
  apply le_antisymm (normalizedDeterminantCutoff_range n coords κ x).2
  fin_cases b
  · exact hb1 ▸ le_max_left _ _
  · exact hb1 ▸ le_max_right _ _

theorem normalizedDeterminantCutoff_eq_zero {A : Type*} (n : ℕ)
    (coords : Fin 2 → Fin n → Fin n → A) {κ : ℝ} (hκ : 0 < κ)
    (x : A → ℝ) (hx : ∀ b i j, |x (coords b i j)| ≤ 1)
    (hgood : ∀ b : Fin 2, κ ≤ |Matrix.det (fun i j => x (coords b i j))|) :
    normalizedDeterminantCutoff n coords κ x = 0 := by
  have he (b : Fin 2) : clippedSelectedDeterminant n (coords b) x =
      Matrix.det (fun i j => x (coords b i j)) := by
    unfold clippedSelectedDeterminant
    congr 1
    funext i j
    exact unitTestClip_eq_self (hx b i j)
  have hz (b : Fin 2) : scalarBadSublevelRamp κ (clippedSelectedDeterminant n (coords b) x) = 0 :=
    scalarBadSublevelRamp_eq_zero hκ (by rw [he]; exact hgood b)
  simp only [normalizedDeterminantCutoff, hz, max_self]

theorem normalizedDeterminantCutoff_indicator_bounds {A : Type*} (n : ℕ)
    (coords : Fin 2 → Fin n → Fin n → A) {κ : ℝ} (hκ : 0 < κ)
    (x : A → ℝ) (hx : ∀ b i j, |x (coords b i j)| ≤ 1) :
    (if ∃ b : Fin 2, |Matrix.det (fun i j => x (coords b i j))| ≤ κ / 2 then (1 : ℝ) else 0) ≤
      normalizedDeterminantCutoff n coords κ x ∧
    normalizedDeterminantCutoff n coords κ x ≤
      (if ∃ b : Fin 2, |Matrix.det (fun i j => x (coords b i j))| ≤ κ then (1 : ℝ) else 0) := by
  constructor
  · split_ifs with hbad
    · exact (normalizedDeterminantCutoff_eq_one n coords hκ x hx hbad).ge
    · exact (normalizedDeterminantCutoff_range n coords κ x).1
  · split_ifs with hbad
    · exact (normalizedDeterminantCutoff_range n coords κ x).2
    · exact (normalizedDeterminantCutoff_eq_zero n coords hκ x hx
        (fun b => le_of_lt (lt_of_not_ge (fun h => hbad ⟨b,h⟩)))).le

noncomputable def spatialMatrixBlockCutoff {G P : Type*} {n : ℕ}
    (e : Fin 2 × Fin n ↪ G) (κ : ℝ) (x : Option (G ⊕ P) × Fin n → ℝ) : ℝ :=
  normalizedDeterminantCutoff n (fun b i j => spatialMatrixBlockSlot e (b,j,i)) κ x

theorem spatialMatrixBlockCutoff_range {G P : Type*} {n : ℕ}
    (e : Fin 2 × Fin n ↪ G) (κ : ℝ) (x : Option (G ⊕ P) × Fin n → ℝ) :
    spatialMatrixBlockCutoff e κ x ∈ Set.Icc (0 : ℝ) 1 := by
  exact normalizedDeterminantCutoff_range n
    (fun b i j => spatialMatrixBlockSlot (P := P) e (b,j,i)) κ x

theorem spatialMatrixBlockCutoff_lipschitz {G P : Type*} [Fintype G] [Fintype P] {n : ℕ}
    (e : Fin 2 × Fin n ↪ G) {κ : ℝ} (hκ : 0 < κ) :
    LipschitzWith (⟨2 / κ, by positivity⟩ * ((n * n.factorial : ℕ) : ℝ≥0))
      (spatialMatrixBlockCutoff (P := P) e κ) := by
  unfold spatialMatrixBlockCutoff
  exact normalizedDeterminantCutoff_lipschitz n
    (fun b i j => spatialMatrixBlockSlot (P := P) e (b,j,i)) hκ

theorem spatialMatrixBlockCutoff_indicator_bounds {G P : Type*} {n : ℕ}
    (e : Fin 2 × Fin n ↪ G) (V : Option (G ⊕ P) × Fin n → ℝ) {κ : ℝ} (hκ : 0 < κ)
    (z : Option (G ⊕ P) × Fin n → ℤ)
    (hz : ∀ t, |(z t : ℝ) / V t| ≤ 1) :
    (if spatialMatrixBlockBad e V (κ / 2) z then (1 : ℝ) else 0) ≤
      spatialMatrixBlockCutoff e κ (fun t => (z t : ℝ) / V t) ∧
    spatialMatrixBlockCutoff e κ (fun t => (z t : ℝ) / V t) ≤
      (if spatialMatrixBlockBad e V κ z then (1 : ℝ) else 0) := by
  unfold spatialMatrixBlockBad spatialMatrixBlockCutoff spatialMatrixNormalizedEntries
  have hh := normalizedDeterminantCutoff_indicator_bounds n
    (fun b i j => spatialMatrixBlockSlot (P := P) e (b,j,i)) hκ
    (fun t => (z t : ℝ) / V t) (fun _ _ _ => hz _)
  split_ifs at hh ⊢ <;> exact hh

end Erdos3

end

end OAI

import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Topology.MetricSpace.Lipschitz
import OAI.Combinatorics.Progressions.Estimates.UniformProductAccuracy
import OAI.Combinatorics.Progressions.Polynomial.RealPolynomialEvaluationMass

namespace OAI

section

namespace Erdos3

open MvPolynomial
open scoped NNReal

theorem abs_aeval_sub_aeval_mass_box_bound {σ : Type*} [Fintype σ] (P : MvPolynomial σ ℝ)
    (v w : σ → ℝ) {B δ : ℝ} {s : ℕ} (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hv : ∀ i, |v i| ≤ B) (hw : ∀ i, |w i| ≤ B) (hvw : ∀ i, |v i - w i| ≤ δ)
    (hdegree : P.totalDegree ≤ s) :
    |aeval v P - aeval w P| ≤
      realPolynomialMass P * Fintype.card σ * s * B ^ (s * (Fintype.card σ + 1)) * δ := by
  classical
  have hmonomial (m : σ →₀ ℕ) (hm : m ∈ P.support) :
      |(∏ i, v i ^ m i) - ∏ i, w i ^ m i| ≤
        Fintype.card σ * (δ * s * B ^ s) * (B ^ s) ^ Fintype.card σ := by
    have hmdeg (i : σ) : m i ≤ s :=
      (monomial_le_degreeOf i hm).trans ((degreeOf_le_totalDegree P i).trans hdegree)
    have hpow (u : σ → ℝ) (hu : ∀ i, |u i| ≤ B) (i : σ) : |u i ^ m i| ≤ B ^ s := by
      rw [abs_pow]
      exact (pow_le_pow_left₀ (abs_nonneg _) (hu i) _).trans (pow_le_pow_right₀ hB (hmdeg i))
    simpa only [Finset.card_univ] using
      abs_finset_prod_sub_prod_le Finset.univ (fun i => v i ^ m i) (fun i => w i ^ m i)
        (one_le_pow₀ hB) (by positivity)
        (fun i _ => hpow v hv i) (fun i _ => hpow w hw i)
        (fun i _ => abs_pow_sub_pow_box_bound hB hδ (hv i) (hw i) (hvw i) (hmdeg i))
  change |P.eval₂ (RingHom.id ℝ) v - P.eval₂ (RingHom.id ℝ) w| ≤ _
  rw [eval₂_eq', eval₂_eq', ← Finset.sum_sub_distrib]
  simp only [RingHom.id_apply]
  calc
    _ ≤ ∑ m ∈ P.support, |P.coeff m * ∏ i, v i ^ m i - P.coeff m * ∏ i, w i ^ m i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ P.support, |P.coeff m| *
        (Fintype.card σ * (δ * s * B ^ s) * (B ^ s) ^ Fintype.card σ) := by
      apply Finset.sum_le_sum
      intro m hm
      rw [← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_left (hmonomial m hm) (abs_nonneg _)
    _ = _ := by
      rw [← Finset.sum_mul]
      simp only [realPolynomialMass, Nat.mul_add, Nat.mul_one, pow_add, pow_mul]
      ring

theorem lipschitzOn_realPolynomial_mass_box {σ : Type*} [Fintype σ] (P : MvPolynomial σ ℝ)
    (C B : ℝ≥0) {s : ℕ} (hB : 1 ≤ B) (hC : realPolynomialMass P ≤ C)
    (hdegree : P.totalDegree ≤ s) :
    LipschitzOnWith (C * Fintype.card σ * s * B ^ (s * (Fintype.card σ + 1)))
      (fun v : σ → ℝ => aeval v P) {v | ∀ i, |v i| ≤ B} := by
  apply LipschitzOnWith.of_dist_le_mul
  intro v hv w hw
  rw [Real.dist_eq]
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hdiff (i : σ) : |v i - w i| ≤ dist v w := by
    simpa only [Real.dist_eq] using dist_le_pi_dist v w i
  have h := abs_aeval_sub_aeval_mass_box_bound P v w hBr dist_nonneg hv hw hdiff hdegree
  apply h.trans
  simp only [NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_pow]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
      (pow_nonneg B.coe_nonneg _)) dist_nonneg

theorem lipschitzOn_realPolynomialVector_mass_box {σ τ : Type*} [Fintype σ] [Fintype τ]
    (P : τ → MvPolynomial σ ℝ) (C B : ℝ≥0) {s : ℕ} (hB : 1 ≤ B)
    (hC : ∀ j, realPolynomialMass (P j) ≤ C) (hdegree : ∀ j, (P j).totalDegree ≤ s) :
    LipschitzOnWith (C * Fintype.card σ * s * B ^ (s * (Fintype.card σ + 1)))
      (fun v : σ → ℝ => fun j => aeval v (P j)) {v | ∀ i, |v i| ≤ B} := by
  apply LipschitzOnWith.of_dist_le_mul
  intro v hv w hw
  apply (dist_pi_le_iff (mul_nonneg (by positivity) dist_nonneg)).mpr
  intro j
  exact (lipschitzOn_realPolynomial_mass_box (P j) C B hB (hC j) (hdegree j)).dist_le_mul v hv w hw

end Erdos3

end

end OAI

import Mathlib.Topology.Algebra.InfiniteSum.Ring
import OAI.Combinatorics.Progressions.Estimates.CorrelationDerivative

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem retainedCharacterGrid_tsum {K Χ : Type*}
    (S : Finset Χ) (coeff : Χ → ℂ) (g : K → ℂ)
    (phase : Χ → K → ℂ) (φ : K → ℂ) (v : ℂ)
    (hs : ∀ χ ∈ S, Summable (fun k => phase χ k * g k * φ k)) :
    (∑' k, g k * (∑ χ ∈ S, coeff χ * phase χ k) * φ k) / v =
      ∑ χ ∈ S, coeff χ * ((∑' k, phase χ k * g k * φ k) / v) := by
  have he (k : K) : g k * (∑ χ ∈ S, coeff χ * phase χ k) * φ k =
      ∑ χ ∈ S, coeff χ * (phase χ k * g k * φ k) := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro χ _
    ring
  simp_rw [he]
  rw [Summable.tsum_finsetSum (fun χ hχ => (hs χ hχ).mul_left (coeff χ))]
  simp_rw [tsum_mul_left, Finset.sum_div, mul_div_assoc]

theorem retainedCharacterGrid_expect {B Χ : Type*} [Fintype B]
    (S : Finset Χ) (coeff : Χ → ℂ) (phase : Χ → B → ℂ) (φ : B → ℂ) :
    (𝔼 b, (∑ χ ∈ S, coeff χ * phase χ b) * φ b) =
      ∑ χ ∈ S, coeff χ * (𝔼 b, phase χ b * φ b) := by
  simp only [Finset.expect_eq_sum_div_card, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro χ _
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, mul_div_assoc]

theorem retainedCharacterGrid_complexMean {B Χ : Type*} [Fintype B]
    (p : FiniteProbabilityWeights B) (S : Finset Χ) (coeff : Χ → ℂ)
    (phase : Χ → B → ℂ) (φ : B → ℂ) :
    p.complexMean (fun b => (∑ χ ∈ S, coeff χ * phase χ b) * φ b) =
      ∑ χ ∈ S, coeff χ * p.complexMean (fun b => phase χ b * φ b) := by
  simp only [FiniteProbabilityWeights.complexMean, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem retainedCharacterGrid_norm_sub_le {Χ : Type*}
    (S : Finset Χ) (coeff disc cont : Χ → ℂ) {M E : ℝ}
    (hE : 0 ≤ E) (hcoeff : (∑ χ ∈ S, ‖coeff χ‖) ≤ M)
    (he : ∀ χ ∈ S, ‖disc χ - cont χ‖ ≤ E) :
    ‖(∑ χ ∈ S, coeff χ * disc χ) - (∑ χ ∈ S, coeff χ * cont χ)‖ ≤ M * E := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  calc
    _ ≤ ∑ χ ∈ S, ‖coeff χ * (disc χ - cont χ)‖ := norm_sum_le _ _
    _ ≤ ∑ χ ∈ S, ‖coeff χ‖ * E := by
      apply Finset.sum_le_sum
      intro χ hχ
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (he χ hχ) (norm_nonneg _)
    _ = (∑ χ ∈ S, ‖coeff χ‖) * E := (Finset.sum_mul ..).symm
    _ ≤ M * E := mul_le_mul_of_nonneg_right hcoeff hE

theorem retainedCharacterGrid_tsum_sub_expect_le {K B Χ : Type*} [Fintype B]
    (S : Finset Χ) (coeff : Χ → ℂ) (g : K → ℂ)
    (phase : Χ → K → ℂ) (φ : K → ℂ) (v : ℂ)
    (refPhase : Χ → B → ℂ) (refTest : B → ℂ) {M E : ℝ}
    (hs : ∀ χ ∈ S, Summable (fun k => phase χ k * g k * φ k))
    (hE : 0 ≤ E) (hcoeff : (∑ χ ∈ S, ‖coeff χ‖) ≤ M)
    (he : ∀ χ ∈ S, ‖(∑' k, phase χ k * g k * φ k) / v -
      (𝔼 b, refPhase χ b * refTest b)‖ ≤ E) :
    ‖(∑' k, g k * (∑ χ ∈ S, coeff χ * phase χ k) * φ k) / v -
      (𝔼 b, (∑ χ ∈ S, coeff χ * refPhase χ b) * refTest b)‖ ≤ M * E := by
  rw [retainedCharacterGrid_tsum S coeff g phase φ v hs,
    retainedCharacterGrid_expect S coeff refPhase refTest]
  exact retainedCharacterGrid_norm_sub_le S coeff _ _ hE hcoeff he

end Erdos3

end

end OAI

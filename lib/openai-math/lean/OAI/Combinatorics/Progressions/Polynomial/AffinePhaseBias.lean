/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Fourier.RectangularGridCharacter
import OAI.Combinatorics.Progressions.Lattices.PhysicalSubboxResidueSlice

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem expect_pi_product {ι : Type*} {κ : ι → Type*} [Fintype ι] [DecidableEq ι] [∀ i, Fintype (κ i)]
    (f : ∀ i, κ i → ℂ) :
    (𝔼 x : ∀ i, κ i, ∏ i, f i (x i)) = ∏ i, 𝔼 y : κ i, f i y := by
  classical
  simp_rw [Fintype.expect_eq_sum_div_card]
  rw [Finset.prod_div_distrib, Fintype.prod_sum, Fintype.card_pi, Nat.cast_prod]

namespace CircleFourier

noncomputable def geometricCharacterMean (N : ℕ) (x : Circle) : ℂ :=
  𝔼 n : Fin N, character ((n : ℕ) • x)

theorem geometricCharacterMean_eq (N : ℕ) (x : Circle) :
    geometricCharacterMean N x = geometricCharacterSum N x / N := by
  rw [geometricCharacterMean, Fintype.expect_eq_sum_div_card, Fintype.card_fin,
    geometricCharacterSum_eq_sum_fin]

theorem norm_geometricCharacterMean_le_one (N : ℕ) (hN : 0 < N) (x : Circle) :
    ‖geometricCharacterMean N x‖ ≤ 1 := by
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  calc
    ‖geometricCharacterMean N x‖ ≤ 𝔼 n : Fin N, ‖character ((n : ℕ) • x)‖ := RCLike.norm_expect_le (K := ℂ)
    _ = 1 := by simp

theorem integerDistance_le_of_geometric_mean {N : ℕ} (hN : 0 < N) (x : Circle)
    {δ : ℝ} (hδ : 0 < δ) (hbias : δ ≤ ‖geometricCharacterMean N x‖) :
    integerDistance x ≤ 1 / (2 * N * δ) := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hnorm : ‖geometricCharacterMean N x‖ = ‖geometricCharacterSum N x‖ / N := by
    rw [geometricCharacterMean_eq, norm_div]
    simp
  have hprod := two_mul_integerDistance_mul_norm_geometricCharacterSum_le_one N x
  have hsmall : (N : ℝ) * δ ≤ ‖geometricCharacterSum N x‖ := by
    rw [hnorm, le_div_iff₀ hN'] at hbias
    simpa only [mul_comm] using hbias
  have h := (mul_le_mul_of_nonneg_left hsmall
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (integerDistance_nonneg x))).trans hprod
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * N * δ)).mpr
  nlinarith only [h]

noncomputable def linearPhaseMean {ι : Type*} [Fintype ι] [DecidableEq ι] (T : ι → ℕ) (a : ι → Circle) : ℂ :=
  𝔼 t : ∀ i, Fin (T i), character (∑ i, ((t i : ℕ) • a i))

theorem linearPhaseMean_eq_product {ι : Type*} [Fintype ι] [DecidableEq ι] (T : ι → ℕ) (a : ι → Circle) :
    linearPhaseMean T a = ∏ i, geometricCharacterMean (T i) (a i) := by
  simp only [linearPhaseMean, character_fintype_sum, geometricCharacterMean]
  exact expect_pi_product (fun i (n : Fin (T i)) => character ((n : ℕ) • a i))

theorem geometric_mean_norm_ge_of_linear_bias {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : ι → ℕ) (hT : ∀ i, 0 < T i) (a : ι → Circle) {δ : ℝ}
    (hbias : δ ≤ ‖linearPhaseMean T a‖) (i : ι) :
    δ ≤ ‖geometricCharacterMean (T i) (a i)‖ := by
  classical
  rw [linearPhaseMean_eq_product, norm_prod] at hbias
  apply hbias.trans
  have h := Finset.prod_le_prod_of_subset_of_le_one₀ (Finset.singleton_subset_iff.mpr (Finset.mem_univ i))
    (fun j _ => norm_nonneg (geometricCharacterMean (T j) (a j)))
    (fun j _ _ => norm_geometricCharacterMean_le_one (T j) (hT j) (a j))
  simpa only [Finset.prod_singleton] using h

theorem linear_phase_near_integers {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : ι → ℕ) (hT : ∀ i, 0 < T i) (a : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hbias : δ ≤ ‖linearPhaseMean T (fun i => (a i : Circle))‖) :
    ∀ i, |a i - round (a i)| ≤ 1 / (2 * T i * δ) := by
  intro i
  rw [← integerDistance_coe]
  exact integerDistance_le_of_geometric_mean (hT i) _ hδ
    (geometric_mean_norm_ge_of_linear_bias T hT _ hbias i)

end CircleFourier
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem integerBox_expect_eq_fin {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : ι → ℕ) (f : (ι → ℤ) → ℂ) :
    (𝔼 x ∈ integerBox T, f x) = 𝔼 t : ∀ i, Fin (T i), f (fun i => ((t i : ℕ) : ℤ)) := by
  symm
  apply Finset.expect_bij (fun t _ i => ((t i : ℕ) : ℤ))
  · intro t _
    rw [mem_integerBox]
    exact fun i => ⟨Int.natCast_nonneg _, by exact_mod_cast (t i).isLt⟩
  · intro t _
    rfl
  · intro t _ u _ h
    funext i
    apply Fin.ext
    exact_mod_cast congrFun h i
  · intro x hx
    have hx' := (mem_integerBox T x).mp hx
    let t : ∀ i, Fin (T i) := fun i => ⟨(x i).toNat, by have := hx' i; omega⟩
    refine ⟨t, Finset.mem_univ _, ?_⟩
    funext i
    change ((x i).toNat : ℤ) = x i
    exact Int.toNat_of_nonneg (hx' i).1

namespace CircleFourier

theorem affinePhaseMean_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : ι → ℕ) (c : ℂ) (a₀ : Circle) (a : ι → Circle) :
    (𝔼 t : ∀ i, Fin (T i), c * character (a₀ + ∑ i, (t i : ℕ) • a i)) =
      c * character a₀ * linearPhaseMean T a := by
  simp only [character_add, ← mul_assoc]
  rw [← Finset.mul_expect]
  rfl

theorem linearPhaseMean_norm_ge_of_affine_bias {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : ι → ℕ) (c : ℂ) (a₀ : Circle) (a : ι → Circle)
    {M δ : ℝ} (hM : 0 < M) (hc : ‖c‖ ≤ M)
    (hbias : δ ≤ ‖𝔼 t : ∀ i, Fin (T i), c * character (a₀ + ∑ i, (t i : ℕ) • a i)‖) :
    δ / M ≤ ‖linearPhaseMean T a‖ := by
  rw [affinePhaseMean_eq, norm_mul, norm_mul, norm_character, mul_one] at hbias
  apply (div_le_iff₀ hM).mpr
  exact hbias.trans ((mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans_eq (mul_comm _ _))

theorem affine_phase_near_integers {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : ι → ℕ) (hT : ∀ i, 0 < T i) (c : ℂ) (a₀ : Circle) (a : ι → ℝ)
    {M δ : ℝ} (hM : 0 < M) (hδ : 0 < δ) (hc : ‖c‖ ≤ M)
    (hbias : δ ≤ ‖𝔼 t : ∀ i, Fin (T i), c * character (a₀ + ∑ i, (t i : ℕ) • (a i : Circle))‖) :
    ∀ i, |a i - round (a i)| ≤ M / (2 * T i * δ) := by
  have h := linear_phase_near_integers T hT a (div_pos hδ hM)
    (linearPhaseMean_norm_ge_of_affine_bias T c a₀ _ hM hc hbias)
  intro i
  apply (h i).trans_eq
  field_simp

end CircleFourier
end Erdos3

end

end OAI

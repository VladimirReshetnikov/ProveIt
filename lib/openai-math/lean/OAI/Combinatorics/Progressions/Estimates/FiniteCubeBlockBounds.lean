/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Geometry.WeightedBlockSupportScale
import OAI.Combinatorics.Progressions.Probability.FiniteCubeBlockLaw

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def cubeSliceBlockBound {b g q : ℕ} {C : Type*}
    (s : Fin b → Fin g → FiniteCubeSlice q) (coeff : C → Fin b → ℤ) (c : C) (S : Finset (Fin q)) : ℤ :=
  ∑ a, |coeff c a| * (2 : ℤ) ^ S.card * ∏ j, ((q + 1 : ℕ) : ℤ) * (s a j).radius

theorem cubeSliceBlockSum_bound {b g q : ℕ} {C : Type*}
    (s : Fin b → Fin g → FiniteCubeSlice q) (coeff : C → Fin b → ℤ)
    (J : Finset (Finset (Fin q))) (center : J → ℤ) (x : CubeSliceBlockDomain s C) (S : J) :
    |cubeSliceBlockSum s coeff J center x S - center S| ≤ cubeSliceBlockBound s coeff x.1 S := by
  simp only [cubeSliceBlockSum, Pi.add_apply, Finset.sum_apply, add_sub_cancel_left]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro a _
  rw [abs_mul, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  simpa only [Fintype.card_fin] using integerBooleanBlockJet_bound
    (fun j => (s a j).coordinates (x.2 a j)) (fun j => (s a j).radius)
    (fun j i => (s a j).coordinates_abs_le (x.2 a j) i) S.val

theorem cubeSliceBlockBound_le_scale {b g q : ℕ} {C : Type*}
    (s : Fin b → Fin g → FiniteCubeSlice q) (coeff : C → Fin b → ℤ) (c : C)
    (H : Fin b → ℝ) {R F K : ℝ} (hR : 0 ≤ R)
    (hcoeff : ∀ a, |(coeff c a : ℝ)| ≤ H a)
    (hradius : ∀ a j, ((s a j).radius : ℝ) ≤ R * (s a j).length)
    (hvolume : ∀ a, H a * ∏ j, ((s a j).length : ℝ) ≤ F * K)
    (S : Finset (Fin q)) (hS : S.card ≤ g) :
    (cubeSliceBlockBound s coeff c S : ℝ) ≤ blockJetScaleBound q g b (R ^ g * F) * K := by
  simp only [cubeSliceBlockBound, Int.cast_sum, Int.cast_mul, Int.cast_abs, Int.cast_pow,
    Int.cast_ofNat, Int.cast_prod, Int.cast_natCast, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc
    _ ≤ ∑ _a : Fin b, (2 : ℝ) ^ g * ((q + 1 : ℕ) : ℝ) ^ g * (R ^ g * (F * K)) := by
      apply Finset.sum_le_sum
      intro a _
      have hp : (∏ j, ((s a j).radius : ℝ)) ≤ R ^ g * ∏ j, ((s a j).length : ℝ) := by
        calc
          _ ≤ ∏ j, R * ((s a j).length : ℝ) :=
            Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun j _ => hradius a j)
          _ = _ := by simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      have hc : |(coeff c a : ℝ)| * (∏ j, ((s a j).radius : ℝ)) ≤ R ^ g * (F * K) := by
        calc
          _ ≤ H a * (R ^ g * ∏ j, ((s a j).length : ℝ)) :=
            mul_le_mul (hcoeff a) hp (by positivity) ((abs_nonneg _).trans (hcoeff a))
          _ = R ^ g * (H a * ∏ j, ((s a j).length : ℝ)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (hvolume a) (pow_nonneg hR _)
      have ht := mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hS)
        (show 0 ≤ ((q + 1 : ℕ) : ℝ) ^ g by positivity)
      have he := mul_le_mul ht hc (by positivity : 0 ≤ |(coeff c a : ℝ)| * ∏ j, ((s a j).radius : ℝ))
        (by positivity : 0 ≤ (2 : ℝ) ^ g * ((q + 1 : ℕ) : ℝ) ^ g)
      convert he using 1
      ring
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, blockJetScaleBound]; ring

theorem cubeSliceBlockSum_scale_bound {b g q K : ℕ} {C : Type*}
    (s : Fin b → Fin g → FiniteCubeSlice q) (coeff : C → Fin b → ℤ) (H : Fin b → ℝ)
    {O F : ℝ} (hO : 0 ≤ O) (hcoeff : ∀ c a, |(coeff c a : ℝ)| ≤ H a)
    (hroot : ∀ a j, |((s a j).root : ℝ)| ≤ O * (s a j).length)
    (hvolume : ∀ a, H a * ∏ j, ((s a j).length : ℝ) ≤ F * K)
    (J : Finset (Finset (Fin q))) (hJ : ∀ S ∈ J, S.card ≤ g)
    (center : J → ℤ) (x : CubeSliceBlockDomain s C) (S : J) :
    |(cubeSliceBlockSum s coeff J center x S : ℝ) - center S| ≤
      blockJetScaleBound q g b ((O + 1) ^ g * F) * K := by
  have hb : |(cubeSliceBlockSum s coeff J center x S : ℝ) - center S| ≤
      (cubeSliceBlockBound s coeff x.1 S : ℝ) := by exact_mod_cast cubeSliceBlockSum_bound s coeff J center x S
  exact hb.trans (cubeSliceBlockBound_le_scale s coeff x.1 H (by linarith : 0 ≤ O + 1)
    (hcoeff x.1) (fun a j => (s a j).radius_relative (hroot a j)) hvolume S (hJ S S.property))

end Erdos3

end

end OAI

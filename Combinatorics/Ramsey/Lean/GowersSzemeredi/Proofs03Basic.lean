import GowersSzemeredi.Proofs02Uniformity
import Mathlib.Algebra.Order.Chebyshev

/-!
# Basic higher-uniformity proofs for Gowers (2001), Section 3

This module develops the finite-difference/Cauchy--Schwarz identity needed for
the monotonicity of higher-degree uniformity.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

lemma sum_difference_eq_norm_sum_sq {N : Nat} [NeZero N]
    (g : ZMod N → Complex) :
    ∑ a : ZMod N, ∑ s : ZMod N, difference g a s =
      ((‖∑ s : ZMod N, g s‖ ^ 2 : Real) : Complex) := by
  calc
    ∑ a : ZMod N, ∑ s : ZMod N, difference g a s =
        ∑ s : ZMod N, ∑ a : ZMod N, g s * star (g (s - a)) := by
      rw [sum_comm]
      rfl
    _ = ∑ s : ZMod N, ∑ u : ZMod N, g s * star (g u) := by
      apply Finset.sum_congr rfl
      intro s _
      simpa [Equiv.subLeft_apply] using
        (Equiv.sum_comp (Equiv.subLeft s) (fun u => g s * star (g u)))
    _ = (∑ s : ZMod N, g s) * star (∑ u : ZMod N, g u) := by
      simp only [star_sum, sum_mul, mul_sum]
      rw [sum_comm]
    _ = ((‖∑ s : ZMod N, g s‖ ^ 2 : Real) : Complex) := by
      rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow]

lemma cubeDifference_cons {N n : Nat} (f : ZMod N → Complex)
    (r : ZMod N) (a : Point N n) :
    cubeDifference f (Fin.cons r a) = difference (cubeDifference f a) r := by
  funext s
  simp only [cubeDifference, List.ofFn_cons, iteratedDifference]

lemma sum_point_succ {N n : Nat} [NeZero N] {M : Type*} [AddCommMonoid M]
    (F : Point N (n + 1) → M) :
    ∑ b : Point N (n + 1), F b =
      ∑ r : ZMod N, ∑ a : Point N n, F (Fin.cons r a) := by
  let e := Fin.consEquiv (fun _ : Fin (n + 1) => ZMod N)
  calc
    ∑ b : Point N (n + 1), F b = ∑ p : ZMod N × Point N n, F (e p) :=
      (e.sum_comp F).symm
    _ = ∑ r : ZMod N, ∑ a : Point N n, F (Fin.cons r a) := by
      rw [Fintype.sum_prod_type]
      rfl

lemma sum_cube_succ_eq_sum_norm_sq {N n : Nat} [NeZero N]
    (f : ZMod N → Complex) :
    ∑ b : Point N (n + 1), ∑ s : ZMod N, cubeDifference f b s =
      ((∑ a : Point N n, ‖∑ s : ZMod N, cubeDifference f a s‖ ^ 2 : Real) :
        Complex) := by
  calc
    ∑ b : Point N (n + 1), ∑ s : ZMod N, cubeDifference f b s =
        ∑ r : ZMod N, ∑ a : Point N n,
          ∑ s : ZMod N, cubeDifference f (Fin.cons r a) s :=
      sum_point_succ _
    _ = ∑ a : Point N n, ∑ r : ZMod N, ∑ s : ZMod N,
          difference (cubeDifference f a) r s := by
      rw [sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro r _
      simp only [cubeDifference_cons]
    _ = ∑ a : Point N n,
          ((‖∑ s : ZMod N, cubeDifference f a s‖ ^ 2 : Real) : Complex) := by
      apply Finset.sum_congr rfl
      intro a _
      exact sum_difference_eq_norm_sum_sq _
    _ = ((∑ a : Point N n, ‖∑ s : ZMod N, cubeDifference f a s‖ ^ 2 : Real) :
          Complex) := by
      rw [Complex.ofReal_sum]

lemma previousUniformEnergy_sq_le {N n : Nat} [NeZero N]
    (f : ZMod N → Complex) :
    (∑ a : Point N n, ‖∑ s : ZMod N, cubeDifference f a s‖ ^ 2) ^ 2 ≤
      (N : Real) ^ (n + 1) *
        ∑ b : Point N (n + 1), ‖∑ s : ZMod N, cubeDifference f b s‖ ^ 2 := by
  let D := ∑ a : Point N n, ‖∑ s : ZMod N, cubeDifference f a s‖ ^ 2
  let X : Point N (n + 1) → Complex :=
    fun b => ∑ s : ZMod N, cubeDifference f b s
  have hD : 0 ≤ D := Finset.sum_nonneg fun a _ => sq_nonneg _
  have htotal : ∑ b : Point N (n + 1), X b = (D : Complex) := by
    exact sum_cube_succ_eq_sum_norm_sq f
  have hnorm : ‖∑ b : Point N (n + 1), X b‖ = D := by
    rw [htotal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hD]
  have htriangle : ‖∑ b : Point N (n + 1), X b‖ ≤
      ∑ b : Point N (n + 1), ‖X b‖ := by
    simpa using norm_sum_le (Finset.univ : Finset (Point N (n + 1))) X
  have hcauchy : (∑ b : Point N (n + 1), ‖X b‖) ^ 2 ≤
      (Fintype.card (Point N (n + 1)) : Real) *
        ∑ b : Point N (n + 1), ‖X b‖ ^ 2 := by
    simpa using (sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (Point N (n + 1))))
      (f := fun b => ‖X b‖))
  change D ^ 2 ≤ (N : Real) ^ (n + 1) * ∑ b, ‖X b‖ ^ 2
  calc
    D ^ 2 = ‖∑ b : Point N (n + 1), X b‖ ^ 2 := by rw [hnorm]
    _ ≤ (∑ b : Point N (n + 1), ‖X b‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htriangle 2
    _ ≤ (Fintype.card (Point N (n + 1)) : Real) *
        ∑ b : Point N (n + 1), ‖X b‖ ^ 2 := hcauchy
    _ = (N : Real) ^ (n + 1) * ∑ b : Point N (n + 1), ‖X b‖ ^ 2 := by
      simp [Point, ZMod.card]

/-- **Gowers, Lemma 3.4.** Higher-degree uniformity is monotone, with the
square-root loss obtained from finite Cauchy--Schwarz. -/
theorem lemma_3_4_holds : lemma_3_4 := by
  intro N d _ f alpha hd _hdisc hUniform
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  let D := ∑ a : Point N n, ‖∑ s : ZMod N, cubeDifference f a s‖ ^ 2
  let U := ∑ b : Point N (n + 1), ‖∑ s : ZMod N, cubeDifference f b s‖ ^ 2
  change U ≤ alpha * (N : Real) ^ (n + 3) at hUniform
  change D ≤ alpha ^ ((1 : Real) / 2) * (N : Real) ^ (n + 2)
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hU_nonneg : 0 ≤ U := Finset.sum_nonneg fun b _ => sq_nonneg _
  have halphaMul : 0 ≤ alpha * (N : Real) ^ (n + 3) :=
    hU_nonneg.trans hUniform
  have halpha : 0 ≤ alpha :=
    nonneg_of_mul_nonneg_left halphaMul (pow_pos hN _)
  have hroot_nonneg : 0 ≤ alpha ^ ((1 : Real) / 2) :=
    Real.rpow_nonneg halpha _
  have hroot_pow : (alpha ^ ((1 : Real) / 2)) ^ 2 = alpha := by
    convert Real.rpow_inv_natCast_pow halpha (by norm_num : (2 : Nat) ≠ 0) using 1
    all_goals norm_num
  have hDsq : D ^ 2 ≤ alpha * (N : Real) ^ (2 * (n + 2)) := by
    calc
      D ^ 2 ≤ (N : Real) ^ (n + 1) * U :=
        previousUniformEnergy_sq_le f
      _ ≤ (N : Real) ^ (n + 1) * (alpha * (N : Real) ^ (n + 3)) :=
        mul_le_mul_of_nonneg_left hUniform (pow_nonneg hN.le _)
      _ = alpha * (N : Real) ^ (2 * (n + 2)) := by
        rw [show 2 * (n + 2) = (n + 1) + (n + 3) by omega, pow_add]
        ring
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : Nat) ≠ 0)
    (mul_nonneg hroot_nonneg (pow_nonneg hN.le _))
  calc
    D ^ 2 ≤ alpha * (N : Real) ^ (2 * (n + 2)) := hDsq
    _ = (alpha ^ ((1 : Real) / 2) * (N : Real) ^ (n + 2)) ^ 2 := by
      rw [mul_pow, hroot_pow, ← pow_mul]
      congr 2
      omega

end LeanProofs.GowersSzemeredi

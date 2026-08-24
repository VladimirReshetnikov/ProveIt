import GowersSzemeredi.Sections14_15
import GowersSzemeredi.Proofs01_03
import Mathlib.Analysis.MeanInequalities
import Mathlib.Algebra.Order.Chebyshev

/-!
# Fourier proof for Gowers (2001), Proposition 14.1

This module proves the weighted simultaneous-additivity estimate for the
first-coordinate correlations of a finite family of two-dimensional
disc-valued functions.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

@[simp] private lemma prop141_exponential_add {N : Nat} [NeZero N]
    (x y : ZMod N) : exponential (x + y) = exponential x * exponential y := by
  exact AddChar.map_add_eq_mul (ZMod.stdAddChar (N := N)) x y

@[simp] private lemma prop141_star_exponential {N : Nat} [NeZero N]
    (x : ZMod N) : star (exponential x) = exponential (-x) := by
  simpa only [exponential, starRingEnd_apply] using
    (AddChar.map_neg_eq_conj (ZMod.stdAddChar (N := N)) x).symm

private lemma prop141_coeff_sq_expansion {N : Nat} [NeZero N]
    (f : Pair N → Complex) (h r : ZMod N) :
    ((‖fourier (firstCoordinateCorrelation f h) r‖ ^ 2 : Real) : Complex) =
      ∑ y : ZMod N, ∑ x : ZMod N, ∑ u : ZMod N, ∑ w : ZMod N,
        f (x + h, y) * star (f (x, y)) *
          star (f (w + h, y - u)) * f (w, y - u) *
            exponential (-(r * u)) := by
  simp only [fourier, firstCoordinateCorrelation, ZMod.dft_apply, smul_eq_mul]
  calc
    ((‖∑ y : ZMod N, exponential (-(y * r)) *
        ∑ x : ZMod N, f (x + h, y) * star (f (x, y))‖ ^ 2 : Real) :
          Complex) =
        (∑ y : ZMod N, exponential (-(y * r)) *
          ∑ x : ZMod N, f (x + h, y) * star (f (x, y))) *
        star (∑ z : ZMod N, exponential (-(z * r)) *
          ∑ w : ZMod N, f (w + h, z) * star (f (w, z))) := by
            rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow]
    _ = ∑ y : ZMod N, ∑ x : ZMod N, ∑ z : ZMod N, ∑ w : ZMod N,
        (exponential (-(y * r)) *
          (f (x + h, y) * star (f (x, y)))) *
        ((f (w, z) * star (f (w + h, z))) * exponential (z * r)) := by
          simp only [star_sum, star_mul, star_star, prop141_star_exponential,
            neg_neg]
          simp_rw [mul_sum, sum_mul]
          simp_rw [mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro y _
          rw [Finset.sum_comm]
    _ = ∑ y : ZMod N, ∑ x : ZMod N, ∑ u : ZMod N, ∑ w : ZMod N,
        (exponential (-(y * r)) *
          (f (x + h, y) * star (f (x, y)))) *
        ((f (w, y - u) * star (f (w + h, y - u))) *
          exponential ((y - u) * r)) := by
            apply Finset.sum_congr rfl
            intro y _
            apply Finset.sum_congr rfl
            intro x _
            rw [← (Equiv.subLeft y).sum_comp]
            rfl
    _ = ∑ y : ZMod N, ∑ x : ZMod N, ∑ u : ZMod N, ∑ w : ZMod N,
        f (x + h, y) * star (f (x, y)) *
          star (f (w + h, y - u)) * f (w, y - u) *
            exponential (-(r * u)) := by
              apply Finset.sum_congr rfl
              intro y _
              apply Finset.sum_congr rfl
              intro x _
              apply Finset.sum_congr rfl
              intro u _
              apply Finset.sum_congr rfl
              intro w _
              have hphase :
                  exponential (-(y * r)) * exponential ((y - u) * r) =
                    exponential (-(r * u)) := by
                rw [← prop141_exponential_add]
                congr 1
                ring
              rw [← hphase]
              ring

private def prop141Outer {N p : Nat} (f : Fin p → Pair N → Complex)
    (y x u w : Fin p → ZMod N) : Complex :=
  ∏ i, star (f i (x i, y i)) * f i (w i, y i - u i)

private def prop141InnerTerm {N p : Nat} [NeZero N]
    (lambda : ZMod N → Real) (f : Fin p → Pair N → Complex)
    (sigma : Fin p → ZMod N → ZMod N)
    (y x u w : Fin p → ZMod N) (h : ZMod N) : Complex :=
  (lambda h : Complex) * ∏ i,
    f i (x i + h, y i) * star (f i (w i + h, y i - u i)) *
      exponential (-(sigma i h * u i))

private lemma prop141_energy_expansion {N p : Nat} [NeZero N]
    (lambda : ZMod N → Real) (f : Fin p → Pair N → Complex)
    (sigma : Fin p → ZMod N → ZMod N) :
    (((∑ h : ZMod N, lambda h * ∏ i : Fin p,
        ‖fourier (firstCoordinateCorrelation (f i) h) (sigma i h)‖ ^ 2 :
          Real)) : Complex) =
      ∑ y : Fin p → ZMod N, ∑ x : Fin p → ZMod N,
        ∑ u : Fin p → ZMod N, ∑ w : Fin p → ZMod N,
          prop141Outer f y x u w *
            ∑ h : ZMod N, prop141InnerTerm lambda f sigma y x u w h := by
  rw [Complex.ofReal_sum]
  calc
    (∑ h : ZMod N,
        ((lambda h * ∏ i : Fin p,
          ‖fourier (firstCoordinateCorrelation (f i) h) (sigma i h)‖ ^ 2 :
            Real) : Complex)) =
        ∑ h : ZMod N, (lambda h : Complex) * ∏ i : Fin p,
          ((‖fourier (firstCoordinateCorrelation (f i) h) (sigma i h)‖ ^ 2 :
            Real) : Complex) := by
              apply Finset.sum_congr rfl
              intro h _
              push_cast
              rfl
    _ = ∑ h : ZMod N, (lambda h : Complex) * ∏ i : Fin p,
        ∑ y : ZMod N, ∑ x : ZMod N, ∑ u : ZMod N, ∑ w : ZMod N,
          f i (x + h, y) * star (f i (x, y)) *
            star (f i (w + h, y - u)) * f i (w, y - u) *
              exponential (-(sigma i h * u)) := by
                apply Finset.sum_congr rfl
                intro h _
                congr 1
                apply Finset.prod_congr rfl
                intro i _
                rw [prop141_coeff_sq_expansion]
    _ = ∑ h : ZMod N, (lambda h : Complex) *
        ∑ y : Fin p → ZMod N, ∑ x : Fin p → ZMod N,
          ∑ u : Fin p → ZMod N, ∑ w : Fin p → ZMod N,
            ∏ i : Fin p,
              f i (x i + h, y i) * star (f i (x i, y i)) *
                star (f i (w i + h, y i - u i)) * f i (w i, y i - u i) *
                  exponential (-(sigma i h * u i)) := by
                    apply Finset.sum_congr rfl
                    intro h _
                    congr 1
                    rw [Fintype.prod_sum]
                    apply Finset.sum_congr rfl
                    intro y _
                    rw [Fintype.prod_sum]
                    apply Finset.sum_congr rfl
                    intro x _
                    rw [Fintype.prod_sum]
                    apply Finset.sum_congr rfl
                    intro u _
                    rw [Fintype.prod_sum]
    _ = ∑ y : Fin p → ZMod N, ∑ x : Fin p → ZMod N,
        ∑ u : Fin p → ZMod N, ∑ w : Fin p → ZMod N,
          prop141Outer f y x u w *
            ∑ h : ZMod N, prop141InnerTerm lambda f sigma y x u w h := by
              simp_rw [Finset.mul_sum]
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro y _
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro x _
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro u _
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro w _
              apply Finset.sum_congr rfl
              intro h _
              simp only [prop141Outer, prop141InnerTerm]
              calc
                (lambda h : Complex) * ∏ i : Fin p,
                    f i (x i + h, y i) * star (f i (x i, y i)) *
                      star (f i (w i + h, y i - u i)) *
                        f i (w i, y i - u i) *
                          exponential (-(sigma i h * u i)) =
                    (lambda h : Complex) * ∏ i : Fin p,
                      ((star (f i (x i, y i)) * f i (w i, y i - u i)) *
                        (f i (x i + h, y i) *
                          star (f i (w i + h, y i - u i)) *
                            exponential (-(sigma i h * u i)))) := by
                              congr 1
                              apply Finset.prod_congr rfl
                              intro i _
                              ring
                _ = (lambda h : Complex) *
                    ((∏ i : Fin p,
                      star (f i (x i, y i)) * f i (w i, y i - u i)) *
                    ∏ i : Fin p, f i (x i + h, y i) *
                      star (f i (w i + h, y i - u i)) *
                        exponential (-(sigma i h * u i))) := by
                          rw [Finset.prod_mul_distrib]
                _ = (∏ i : Fin p,
                      star (f i (x i, y i)) * f i (w i, y i - u i)) *
                    ((lambda h : Complex) * ∏ i : Fin p,
                      f i (x i + h, y i) *
                        star (f i (w i + h, y i - u i)) *
                          exponential (-(sigma i h * u i))) := by ring

private lemma prop141_outer_norm_le {N p : Nat}
    (f : Fin p → Pair N → Complex) (hf : ∀ i, DiscValued (f i))
    (y x u w : Fin p → ZMod N) : ‖prop141Outer f y x u w‖ ≤ 1 := by
  rw [prop141Outer, norm_prod]
  apply Finset.prod_le_one
  · intro i _
    positivity
  · intro i _
    rw [norm_mul, norm_star]
    calc
      ‖f i (x i, y i)‖ * ‖f i (w i, y i - u i)‖ ≤ 1 * 1 := by
        gcongr <;> apply hf
      _ = 1 := one_mul 1

private lemma prop141_initial_bound {N p : Nat} [NeZero N]
    (lambda : ZMod N → Real) (f : Fin p → Pair N → Complex)
    (sigma : Fin p → ZMod N → ZMod N)
    (hlambda : ∀ h, 0 ≤ lambda h) (hf : ∀ i, DiscValued (f i)) :
    (∑ h : ZMod N, lambda h * ∏ i : Fin p,
        ‖fourier (firstCoordinateCorrelation (f i) h) (sigma i h)‖ ^ 2) ≤
      ∑ y : Fin p → ZMod N, ∑ x : Fin p → ZMod N,
        ∑ u : Fin p → ZMod N, ∑ w : Fin p → ZMod N,
          ‖∑ h : ZMod N, prop141InnerTerm lambda f sigma y x u w h‖ := by
  let energy : Real := ∑ h : ZMod N, lambda h * ∏ i : Fin p,
    ‖fourier (firstCoordinateCorrelation (f i) h) (sigma i h)‖ ^ 2
  have henergy : 0 ≤ energy := by
    dsimp only [energy]
    apply Finset.sum_nonneg
    intro h _
    exact mul_nonneg (hlambda h) (Finset.prod_nonneg fun _ _ => sq_nonneg _)
  calc
    (∑ h : ZMod N, lambda h * ∏ i : Fin p,
        ‖fourier (firstCoordinateCorrelation (f i) h) (sigma i h)‖ ^ 2) =
        ‖((energy : Real) : Complex)‖ := by
          rw [Complex.norm_real, Real.norm_of_nonneg henergy]
    _ = ‖∑ y : Fin p → ZMod N, ∑ x : Fin p → ZMod N,
        ∑ u : Fin p → ZMod N, ∑ w : Fin p → ZMod N,
          prop141Outer f y x u w *
            ∑ h : ZMod N, prop141InnerTerm lambda f sigma y x u w h‖ := by
              rw [prop141_energy_expansion lambda f sigma]
    _ ≤ ∑ y : Fin p → ZMod N,
        ‖∑ x : Fin p → ZMod N, ∑ u : Fin p → ZMod N,
          ∑ w : Fin p → ZMod N, prop141Outer f y x u w *
            ∑ h : ZMod N, prop141InnerTerm lambda f sigma y x u w h‖ :=
              norm_sum_le _ _
    _ ≤ ∑ y : Fin p → ZMod N, ∑ x : Fin p → ZMod N,
        ‖∑ u : Fin p → ZMod N, ∑ w : Fin p → ZMod N,
          prop141Outer f y x u w *
            ∑ h : ZMod N, prop141InnerTerm lambda f sigma y x u w h‖ := by
              apply Finset.sum_le_sum
              intro y _
              exact norm_sum_le _ _
    _ ≤ ∑ y : Fin p → ZMod N, ∑ x : Fin p → ZMod N,
        ∑ u : Fin p → ZMod N,
          ‖∑ w : Fin p → ZMod N, prop141Outer f y x u w *
            ∑ h : ZMod N, prop141InnerTerm lambda f sigma y x u w h‖ := by
              apply Finset.sum_le_sum
              intro y _
              apply Finset.sum_le_sum
              intro x _
              exact norm_sum_le _ _
    _ ≤ ∑ y : Fin p → ZMod N, ∑ x : Fin p → ZMod N,
        ∑ u : Fin p → ZMod N, ∑ w : Fin p → ZMod N,
          ‖prop141Outer f y x u w *
            ∑ h : ZMod N, prop141InnerTerm lambda f sigma y x u w h‖ := by
              apply Finset.sum_le_sum
              intro y _
              apply Finset.sum_le_sum
              intro x _
              apply Finset.sum_le_sum
              intro u _
              exact norm_sum_le _ _
    _ ≤ ∑ y : Fin p → ZMod N, ∑ x : Fin p → ZMod N,
        ∑ u : Fin p → ZMod N, ∑ w : Fin p → ZMod N,
          ‖∑ h : ZMod N, prop141InnerTerm lambda f sigma y x u w h‖ := by
            apply Finset.sum_le_sum
            intro y _
            apply Finset.sum_le_sum
            intro x _
            apply Finset.sum_le_sum
            intro u _
            apply Finset.sum_le_sum
            intro w _
            rw [norm_mul]
            exact mul_le_of_le_one_left (norm_nonneg _)
              (prop141_outer_norm_le f hf y x u w)

private lemma prop141_l1_cauchy {N p : Nat} [NeZero N]
    (F : (Fin p → ZMod N) → (Fin p → ZMod N) →
      (Fin p → ZMod N) → (Fin p → ZMod N) → Real) :
    (∑ y : Fin p → ZMod N, ∑ x : Fin p → ZMod N,
        ∑ u : Fin p → ZMod N, ∑ w : Fin p → ZMod N,
          F y x u w) ^ 2 ≤
      (N : Real) ^ (4 * p) *
        ∑ y : Fin p → ZMod N, ∑ x : Fin p → ZMod N,
          ∑ u : Fin p → ZMod N, ∑ w : Fin p → ZMod N,
            (F y x u w) ^ 2 := by
  let U := Fin p → ZMod N
  have hcard : Fintype.card U = N ^ p := by simp [U]
  calc
    _ ≤ (N : Real) ^ p * ∑ y : U,
        (∑ x : U, ∑ u : U, ∑ w : U, F y x u w) ^ 2 := by
          simpa only [U, Finset.card_univ, hcard, Nat.cast_pow] using
            (sq_sum_le_card_mul_sum_sq
              (s := (Finset.univ : Finset U))
              (f := fun y => ∑ x : U, ∑ u : U, ∑ w : U, F y x u w))
    _ ≤ (N : Real) ^ p * ∑ y : U, (N : Real) ^ p * ∑ x : U,
        (∑ u : U, ∑ w : U, F y x u w) ^ 2 := by
          gcongr with y
          simpa only [Finset.card_univ, hcard, Nat.cast_pow] using
            (sq_sum_le_card_mul_sum_sq
              (s := (Finset.univ : Finset U))
              (f := fun x => ∑ u : U, ∑ w : U, F y x u w))
    _ ≤ (N : Real) ^ p * ∑ y : U, (N : Real) ^ p * ∑ x : U,
        (N : Real) ^ p * ∑ u : U, (∑ w : U, F y x u w) ^ 2 := by
          gcongr with y x
          simpa only [Finset.card_univ, hcard, Nat.cast_pow] using
            (sq_sum_le_card_mul_sum_sq
              (s := (Finset.univ : Finset U))
              (f := fun u => ∑ w : U, F y x u w))
    _ ≤ (N : Real) ^ p * ∑ y : U, (N : Real) ^ p * ∑ x : U,
        (N : Real) ^ p * ∑ u : U, (N : Real) ^ p * ∑ w : U,
          (F y x u w) ^ 2 := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply Finset.sum_le_sum
            intro y _
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply Finset.sum_le_sum
            intro x _
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply Finset.sum_le_sum
            intro u _
            simpa only [Finset.card_univ, hcard, Nat.cast_pow] using
              (sq_sum_le_card_mul_sum_sq
                (s := (Finset.univ : Finset U)) (f := F y x u))
    _ = _ := by
      simp_rw [← Finset.mul_sum]
      rw [show 4 * p = p + p + p + p by omega, pow_add, pow_add, pow_add]
      ring

private def prop141A {N p : Nat} (f : Fin p → Pair N → Complex)
    (y x u w : Fin p → ZMod N) (s : ZMod N) : Complex :=
  ∏ i, f i (s + x i, y i) * star (f i (s + w i, y i - u i))

private def prop141B {N p : Nat} [NeZero N] (lambda : ZMod N → Real)
    (sigma : Fin p → ZMod N → ZMod N)
    (u : Fin p → ZMod N) (h : ZMod N) : Complex :=
  (lambda h : Complex) * ∏ i, exponential (sigma i h * u i)

private def prop141AddRightEquiv {N : Nat} (s : ZMod N) : ZMod N ≃ ZMod N where
  toFun h := h + s
  invFun t := t - s
  left_inv h := by ring
  right_inv t := by ring

@[simp] private lemma prop141AddRightEquiv_apply {N : Nat} (s h : ZMod N) :
    prop141AddRightEquiv s h = h + s := rfl

private lemma prop141_correlation_eq {N p : Nat} [NeZero N]
    (lambda : ZMod N → Real) (f : Fin p → Pair N → Complex)
    (sigma : Fin p → ZMod N → ZMod N)
    (y x u w : Fin p → ZMod N) (s : ZMod N) :
    correlation (prop141A f y x u w) (prop141B lambda sigma u) s =
      ∑ h : ZMod N, prop141InnerTerm lambda f sigma y
        (fun i => s + x i) u (fun i => s + w i) h := by
  classical
  simp only [correlation]
  rw [← (prop141AddRightEquiv s).sum_comp]
  simp only [prop141AddRightEquiv_apply, add_sub_cancel_right]
  apply Finset.sum_congr rfl
  intro h _
  simp only [prop141A, prop141B, prop141InnerTerm, star_mul, star_prod,
    Complex.star_def, Complex.conj_ofReal, prop141_star_exponential]
  calc
    (∏ i : Fin p,
        f i (h + s + x i, y i) * star (f i (h + s + w i, y i - u i))) *
        ((∏ i : Fin p, exponential (-(sigma i h * u i))) *
          (lambda h : Complex)) =
      (lambda h : Complex) *
        ((∏ i : Fin p,
          f i (h + s + x i, y i) * star (f i (h + s + w i, y i - u i))) *
        ∏ i : Fin p, exponential (-(sigma i h * u i))) := by ring
    _ = (lambda h : Complex) * ∏ i : Fin p,
        ((f i (h + s + x i, y i) *
          star (f i (h + s + w i, y i - u i))) *
            exponential (-(sigma i h * u i))) := by
              congr 1
              exact (Finset.prod_mul_distrib
                (s := (Finset.univ : Finset (Fin p)))).symm
    _ = (lambda h : Complex) * ∏ i : Fin p,
        f i (s + x i + h, y i) * star (f i (s + w i + h, y i - u i)) *
          exponential (-(sigma i h * u i)) := by
            congr 1
            apply Finset.prod_congr rfl
            intro i _
            have hx : h + s + x i = s + x i + h := by ring
            have hw : h + s + w i = s + w i + h := by ring
            rw [hx, hw]

private def prop141VectorShiftEquiv {N p : Nat} (s : ZMod N) :
    (Fin p → ZMod N) ≃ (Fin p → ZMod N) where
  toFun x := fun i => s + x i
  invFun x := fun i => x i - s
  left_inv x := by
    funext i
    ring
  right_inv x := by
    funext i
    ring

private lemma prop141_double_shift_sum {N p : Nat} [NeZero N]
    (F : (Fin p → ZMod N) → (Fin p → ZMod N) → Real) :
    (∑ s : ZMod N, ∑ x : Fin p → ZMod N, ∑ w : Fin p → ZMod N,
        F (fun i => s + x i) (fun i => s + w i)) =
      (N : Real) * ∑ x : Fin p → ZMod N, ∑ w : Fin p → ZMod N,
        F x w := by
  calc
    _ = ∑ _s : ZMod N, ∑ x : Fin p → ZMod N,
        ∑ w : Fin p → ZMod N, F x w := by
          apply Finset.sum_congr rfl
          intro s _
          calc
            (∑ x : Fin p → ZMod N, ∑ w : Fin p → ZMod N,
                F (fun i => s + x i) (fun i => s + w i)) =
                ∑ x : Fin p → ZMod N, ∑ w : Fin p → ZMod N,
                  F x (fun i => s + w i) := by
                    exact Fintype.sum_equiv (prop141VectorShiftEquiv (p := p) s)
                      (fun x => ∑ w : Fin p → ZMod N,
                        F (fun i => s + x i) (fun i => s + w i))
                      (fun x => ∑ w : Fin p → ZMod N,
                        F x (fun i => s + w i)) (fun _ => rfl)
            _ = _ := by
              apply Finset.sum_congr rfl
              intro x _
              exact Fintype.sum_equiv (prop141VectorShiftEquiv (p := p) s)
                (fun w => F x (fun i => s + w i)) (F x) (fun _ => rfl)
    _ = _ := by simp

private lemma prop141_mixed_eq_l2 {N p : Nat} [NeZero N]
    (lambda : ZMod N → Real) (f : Fin p → Pair N → Complex)
    (sigma : Fin p → ZMod N → ZMod N) :
    (∑ y : Fin p → ZMod N, ∑ x : Fin p → ZMod N,
        ∑ u : Fin p → ZMod N, ∑ w : Fin p → ZMod N,
          ∑ r : ZMod N,
            ‖fourier (prop141A f y x u w) r‖ ^ 2 *
              ‖fourier (prop141B lambda sigma u) r‖ ^ 2) =
      (N : Real) ^ 2 *
        ∑ y : Fin p → ZMod N, ∑ x : Fin p → ZMod N,
          ∑ u : Fin p → ZMod N, ∑ w : Fin p → ZMod N,
            ‖∑ h : ZMod N, prop141InnerTerm lambda f sigma y x u w h‖ ^ 2 := by
  let U := Fin p → ZMod N
  calc
    _ = ∑ y : U, ∑ x : U, ∑ u : U, ∑ w : U,
        (N : Real) * ∑ s : ZMod N,
          ‖correlation (prop141A f y x u w) (prop141B lambda sigma u) s‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro y _
            apply Finset.sum_congr rfl
            intro x _
            apply Finset.sum_congr rfl
            intro u _
            apply Finset.sum_congr rfl
            intro w _
            exact lemma_2_1_holds N (prop141A f y x u w)
              (prop141B lambda sigma u)
    _ = (N : Real) * ∑ y : U, ∑ x : U, ∑ u : U, ∑ w : U,
        ∑ s : ZMod N,
          ‖correlation (prop141A f y x u w) (prop141B lambda sigma u) s‖ ^ 2 := by
            simp_rw [← Finset.mul_sum]
    _ = (N : Real) * ∑ y : U, ∑ x : U, ∑ u : U, ∑ w : U,
        ∑ s : ZMod N,
          ‖∑ h : ZMod N, prop141InnerTerm lambda f sigma y
            (fun i => s + x i) u (fun i => s + w i) h‖ ^ 2 := by
              apply congrArg (fun t : Real => (N : Real) * t)
              apply Finset.sum_congr rfl
              intro y _
              apply Finset.sum_congr rfl
              intro x _
              apply Finset.sum_congr rfl
              intro u _
              apply Finset.sum_congr rfl
              intro w _
              apply Finset.sum_congr rfl
              intro s _
              rw [prop141_correlation_eq]
    _ = (N : Real) * ((N : Real) *
        ∑ y : U, ∑ x : U, ∑ u : U, ∑ w : U,
          ‖∑ h : ZMod N, prop141InnerTerm lambda f sigma y x u w h‖ ^ 2) := by
            congr 1
            calc
              (∑ y : U, ∑ x : U, ∑ u : U, ∑ w : U,
                  ∑ s : ZMod N,
                    ‖∑ h : ZMod N, prop141InnerTerm lambda f sigma y
                      (fun i => s + x i) u (fun i => s + w i) h‖ ^ 2) =
                  ∑ y : U, ∑ u : U, ∑ s : ZMod N,
                    ∑ x : U, ∑ w : U,
                      ‖∑ h : ZMod N, prop141InnerTerm lambda f sigma y
                        (fun i => s + x i) u (fun i => s + w i) h‖ ^ 2 := by
                          apply Finset.sum_congr rfl
                          intro y _
                          rw [Finset.sum_comm]
                          apply Finset.sum_congr rfl
                          intro u _
                          calc
                            (∑ x : U, ∑ w : U, ∑ s : ZMod N,
                                ‖∑ h : ZMod N,
                                  prop141InnerTerm lambda f sigma y
                                    (fun i => s + x i) u
                                    (fun i => s + w i) h‖ ^ 2) =
                                ∑ x : U, ∑ s : ZMod N, ∑ w : U,
                                  ‖∑ h : ZMod N,
                                    prop141InnerTerm lambda f sigma y
                                      (fun i => s + x i) u
                                      (fun i => s + w i) h‖ ^ 2 := by
                                    apply Finset.sum_congr rfl
                                    intro x _
                                    exact Finset.sum_comm
                            _ = _ := Finset.sum_comm
              _ = ∑ y : U, ∑ u : U, (N : Real) * ∑ x : U, ∑ w : U,
                  ‖∑ h : ZMod N, prop141InnerTerm lambda f sigma y x u w h‖ ^ 2 := by
                    apply Finset.sum_congr rfl
                    intro y _
                    apply Finset.sum_congr rfl
                    intro u _
                    exact prop141_double_shift_sum (N := N) (p := p)
                      (fun x w =>
                        ‖∑ h : ZMod N,
                          prop141InnerTerm lambda f sigma y x u w h‖ ^ 2)
              _ = (N : Real) * ∑ y : U, ∑ u : U, ∑ x : U, ∑ w : U,
                  ‖∑ h : ZMod N, prop141InnerTerm lambda f sigma y x u w h‖ ^ 2 := by
                    simp_rw [← Finset.mul_sum]
              _ = (N : Real) * ∑ y : U, ∑ x : U, ∑ u : U, ∑ w : U,
                  ‖∑ h : ZMod N, prop141InnerTerm lambda f sigma y x u w h‖ ^ 2 := by
                    apply congrArg (fun t : Real => (N : Real) * t)
                    apply Finset.sum_congr rfl
                    intro y _
                    exact Finset.sum_comm
    _ = _ := by
      simp only [pow_two, mul_assoc]
      rfl

private lemma prop141_fourth_moment_le {N : Nat} [NeZero N]
    (g : ZMod N → Complex) (hg : DiscValued g) :
    ∑ r : ZMod N, ‖fourier g r‖ ^ 4 ≤ (N : Real) ^ 4 := by
  have hcorr (t : ZMod N) : ‖correlation g g t‖ ≤ (N : Real) := by
    calc
      ‖correlation g g t‖ ≤ ∑ s : ZMod N, ‖g s * star (g (s - t))‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _s : ZMod N, (1 : Real) := by
        apply Finset.sum_le_sum
        intro s _
        rw [norm_mul, norm_star]
        calc
          ‖g s‖ * ‖g (s - t)‖ ≤ 1 * 1 := by gcongr <;> apply hg
          _ = 1 := one_mul 1
      _ = (N : Real) := by simp
  have hid :
      (∑ r : ZMod N, ‖fourier g r‖ ^ 4) =
        (N : Real) * ∑ t : ZMod N, ‖correlation g g t‖ ^ 2 := by
    calc
      _ = ∑ r : ZMod N, ‖fourier g r‖ ^ 2 * ‖fourier g r‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro r _
        ring
      _ = _ := by simpa [correlation] using lemma_2_1_holds N g g
  rw [hid]
  calc
    (N : Real) * ∑ t : ZMod N, ‖correlation g g t‖ ^ 2 ≤
        (N : Real) * ∑ _t : ZMod N, (N : Real) ^ 2 := by
          gcongr with t
          exact hcorr t
    _ = (N : Real) ^ 4 := by simp; ring

private lemma prop141A_disc {N p : Nat}
    (f : Fin p → Pair N → Complex) (hf : ∀ i, DiscValued (f i))
    (y x u w : Fin p → ZMod N) : DiscValued (prop141A f y x u w) := by
  intro s
  rw [prop141A, norm_prod]
  apply Finset.prod_le_one
  · intro i _
    positivity
  · intro i _
    rw [norm_mul, norm_star]
    calc
      ‖f i (s + x i, y i)‖ * ‖f i (s + w i, y i - u i)‖ ≤ 1 * 1 := by
        gcongr <;> apply hf
      _ = 1 := one_mul 1

private lemma prop141_fourthA_le {N p : Nat} [NeZero N]
    (f : Fin p → Pair N → Complex) (hf : ∀ i, DiscValued (f i)) :
    (∑ y : Fin p → ZMod N, ∑ x : Fin p → ZMod N,
        ∑ u : Fin p → ZMod N, ∑ w : Fin p → ZMod N,
          ∑ r : ZMod N, ‖fourier (prop141A f y x u w) r‖ ^ 4) ≤
      (N : Real) ^ (4 * p + 4) := by
  let U := Fin p → ZMod N
  have hcard : Fintype.card U = N ^ p := by simp [U]
  calc
    _ ≤ ∑ _y : U, ∑ _x : U, ∑ _u : U, ∑ _w : U,
        (N : Real) ^ 4 := by
          apply Finset.sum_le_sum
          intro y _
          apply Finset.sum_le_sum
          intro x _
          apply Finset.sum_le_sum
          intro u _
          apply Finset.sum_le_sum
          intro w _
          exact prop141_fourth_moment_le (prop141A f y x u w)
            (prop141A_disc f hf y x u w)
    _ = (N : Real) ^ (4 * p + 4) := by
      simp only [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
      push_cast
      rw [show 4 * p + 4 = p + p + p + p + 4 by omega,
        pow_add, pow_add, pow_add, pow_add]
      ring

private lemma prop141_global_cauchy {N p : Nat} [NeZero N]
    (lambda : ZMod N → Real) (f : Fin p → Pair N → Complex)
    (sigma : Fin p → ZMod N → ZMod N) :
    (∑ y : Fin p → ZMod N, ∑ x : Fin p → ZMod N,
        ∑ u : Fin p → ZMod N, ∑ w : Fin p → ZMod N,
          ∑ r : ZMod N,
            ‖fourier (prop141A f y x u w) r‖ ^ 2 *
              ‖fourier (prop141B lambda sigma u) r‖ ^ 2) ^ 2 ≤
      (∑ y : Fin p → ZMod N, ∑ x : Fin p → ZMod N,
        ∑ u : Fin p → ZMod N, ∑ w : Fin p → ZMod N,
          ∑ r : ZMod N, ‖fourier (prop141A f y x u w) r‖ ^ 4) *
      ∑ _y : Fin p → ZMod N, ∑ _x : Fin p → ZMod N,
        ∑ u : Fin p → ZMod N, ∑ _w : Fin p → ZMod N,
          ∑ r : ZMod N, ‖fourier (prop141B lambda sigma u) r‖ ^ 4 := by
  let U := Fin p → ZMod N
  have h := Finset.sum_mul_sq_le_sq_mul_sq
    ((((Finset.univ : Finset U) ×ˢ (Finset.univ : Finset U)) ×ˢ
      ((Finset.univ : Finset U) ×ˢ (Finset.univ : Finset U))) ×ˢ
        (Finset.univ : Finset (ZMod N)))
    (fun z => ‖fourier
      (prop141A f z.1.1.1 z.1.1.2 z.1.2.1 z.1.2.2) z.2‖ ^ 2)
    (fun z => ‖fourier (prop141B lambda sigma z.1.2.1) z.2‖ ^ 2)
  simpa only [Finset.sum_product, ← pow_mul] using h

private lemma prop141_sum_exponential_mul {N : Nat} [NeZero N]
    (x : ZMod N) :
    ∑ u : ZMod N, exponential (x * u) =
      if x = 0 then (N : Complex) else 0 := by
  simpa [exponential, mul_comm] using
    AddChar.sum_mulShift x (ZMod.isPrimitive_stdAddChar N)

private lemma prop141_vector_orthogonality {N p : Nat} [NeZero N]
    (x : Fin p → ZMod N) :
    (∑ u : Fin p → ZMod N, ∏ i, exponential (x i * u i)) =
      if ∀ i, x i = 0 then ((N : Nat) ^ p : Complex) else 0 := by
  calc
    _ = ∏ i : Fin p, ∑ a : ZMod N, exponential (x i * a) := by
      exact (Fintype.prod_sum
        (fun i (a : ZMod N) => exponential (x i * a))).symm
    _ = ∏ i : Fin p, if x i = 0 then (N : Complex) else 0 := by
      apply Finset.prod_congr rfl
      intro i _
      rw [prop141_sum_exponential_mul]
    _ = if ∀ i, x i = 0 then ((N : Nat) ^ p : Complex) else 0 := by
      by_cases h : ∀ i, x i = 0
      · rw [if_pos h]
        simp only [h, if_true, Finset.prod_const, Finset.card_univ]
        rw [Fintype.card_fin]
      · rw [if_neg h, Finset.prod_eq_zero_iff]
        push Not at h
        obtain ⟨i, hi⟩ := h
        exact ⟨i, Finset.mem_univ i, if_neg hi⟩

private lemma prop141_prod_four {p : Nat} (a b c d : Fin p → Complex) :
    (∏ i, a i) * (∏ i, b i) * (∏ i, c i) * (∏ i, d i) =
      ∏ i, a i * b i * c i * d i := by
  symm
  simp only [Finset.prod_mul_distrib]

private lemma prop141_b_product {N p : Nat} [NeZero N]
    (lambda : ZMod N → Real) (sigma : Fin p → ZMod N → ZMod N)
    (q : Fin 4 → ZMod N) (u : Fin p → ZMod N) :
    prop141B lambda sigma u (q 0) *
        star (prop141B lambda sigma u (q 1) *
          prop141B lambda sigma u (q 2)) *
        prop141B lambda sigma u (q 3) =
      ((lambda (q 0) * lambda (q 1) * lambda (q 2) * lambda (q 3) : Real) :
        Complex) *
        ∏ i, exponential
          ((sigma i (q 0) - sigma i (q 1) - sigma i (q 2) +
            sigma i (q 3)) * u i) := by
  simp only [prop141B, star_mul, star_prod, Complex.star_def,
    Complex.conj_ofReal, prop141_star_exponential]
  push_cast
  have hphase :
      (∏ i : Fin p, exponential (sigma i (q 0) * u i)) *
          (∏ i : Fin p, exponential (-(sigma i (q 2) * u i))) *
          (∏ i : Fin p, exponential (-(sigma i (q 1) * u i))) *
          (∏ i : Fin p, exponential (sigma i (q 3) * u i)) =
        ∏ i : Fin p, exponential
          ((sigma i (q 0) - sigma i (q 1) - sigma i (q 2) +
            sigma i (q 3)) * u i) := by
    rw [prop141_prod_four]
    apply Finset.prod_congr rfl
    intro i _
    rw [← prop141_exponential_add, ← prop141_exponential_add,
      ← prop141_exponential_add]
    congr 1
    ring
  calc
    ((lambda (q 0) : Complex) * ∏ i, exponential (sigma i (q 0) * u i)) *
          ((∏ i, exponential (-(sigma i (q 2) * u i))) *
            (lambda (q 2) : Complex) *
            ((∏ i, exponential (-(sigma i (q 1) * u i))) *
              (lambda (q 1) : Complex))) *
        ((lambda (q 3) : Complex) *
          ∏ i, exponential (sigma i (q 3) * u i)) =
      (lambda (q 0) : Complex) * lambda (q 1) * lambda (q 2) * lambda (q 3) *
        (((∏ i, exponential (sigma i (q 0) * u i)) *
          (∏ i, exponential (-(sigma i (q 2) * u i))) *
          (∏ i, exponential (-(sigma i (q 1) * u i))) *
          ∏ i, exponential (sigma i (q 3) * u i))) := by ring
    _ = (lambda (q 0) : Complex) * lambda (q 1) * lambda (q 2) * lambda (q 3) *
        ∏ i, exponential
          ((sigma i (q 0) - sigma i (q 1) - sigma i (q 2) +
            sigma i (q 3)) * u i) := by rw [hphase]

private lemma prop141_sum_b_product {N p : Nat} [NeZero N]
    (lambda : ZMod N → Real) (sigma : Fin p → ZMod N → ZMod N)
    (q : Fin 4 → ZMod N) :
    (∑ u : Fin p → ZMod N,
      prop141B lambda sigma u (q 0) *
        star (prop141B lambda sigma u (q 1) *
          prop141B lambda sigma u (q 2)) *
        prop141B lambda sigma u (q 3)) =
      if (∀ i,
          sigma i (q 0) - sigma i (q 1) = sigma i (q 2) - sigma i (q 3))
      then (((N : Real) ^ p *
        (lambda (q 0) * lambda (q 1) * lambda (q 2) * lambda (q 3)) : Real) :
          Complex)
      else 0 := by
  simp_rw [prop141_b_product]
  rw [← Finset.mul_sum, prop141_vector_orthogonality]
  by_cases h : ∀ i,
      sigma i (q 0) - sigma i (q 1) = sigma i (q 2) - sigma i (q 3)
  · have hz : ∀ i,
        sigma i (q 0) - sigma i (q 1) - sigma i (q 2) + sigma i (q 3) = 0 := by
      intro i
      calc
        _ = (sigma i (q 0) - sigma i (q 1)) -
            (sigma i (q 2) - sigma i (q 3)) := by abel
        _ = 0 := sub_eq_zero.mpr (h i)
    rw [if_pos hz, if_pos h]
    push_cast
    ring
  · have hnz : ¬ ∀ i,
        sigma i (q 0) - sigma i (q 1) - sigma i (q 2) + sigma i (q 3) = 0 := by
      intro hz
      apply h
      intro i
      apply sub_eq_zero.mp
      calc
        (sigma i (q 0) - sigma i (q 1)) -
            (sigma i (q 2) - sigma i (q 3)) =
          sigma i (q 0) - sigma i (q 1) - sigma i (q 2) +
            sigma i (q 3) := by abel
        _ = 0 := hz i
    rw [if_neg hnz, if_neg h]
    simp

private lemma prop141_fourthB_eq_weight {N p : Nat} [NeZero N]
    (lambda : ZMod N → Real) (sigma : Fin p → ZMod N → ZMod N) :
    (∑ u : Fin p → ZMod N, ∑ r : ZMod N,
        ‖fourier (prop141B lambda sigma u) r‖ ^ 4) =
      (N : Real) ^ (p + 1) * simultaneouslyAdditiveWeight lambda sigma := by
  classical
  have hcomplex :
      (((∑ u : Fin p → ZMod N, ∑ r : ZMod N,
          ‖fourier (prop141B lambda sigma u) r‖ ^ 4 : Real)) : Complex) =
        (((N : Real) ^ (p + 1) * simultaneouslyAdditiveWeight lambda sigma :
          Real) : Complex) := by
    rw [Complex.ofReal_sum]
    calc
      (∑ u : Fin p → ZMod N,
          ((∑ r : ZMod N, ‖fourier (prop141B lambda sigma u) r‖ ^ 4 :
            Real) : Complex)) =
          ∑ u : Fin p → ZMod N, (N : Complex) *
            ∑ q : Fin 4 → ZMod N,
              if q 0 - q 1 = q 2 - q 3 then
                prop141B lambda sigma u (q 0) *
                  star (prop141B lambda sigma u (q 1) *
                    prop141B lambda sigma u (q 2)) *
                  prop141B lambda sigma u (q 3)
              else 0 := by
                apply Finset.sum_congr rfl
                intro u _
                exact identity_2_6_holds N (prop141B lambda sigma u)
      _ = (N : Complex) * ∑ q : Fin 4 → ZMod N,
          if q 0 - q 1 = q 2 - q 3 then
            ∑ u : Fin p → ZMod N,
              prop141B lambda sigma u (q 0) *
                star (prop141B lambda sigma u (q 1) *
                  prop141B lambda sigma u (q 2)) *
                prop141B lambda sigma u (q 3)
          else 0 := by
            rw [← Finset.mul_sum]
            congr 1
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro q _
            by_cases hadd : q 0 - q 1 = q 2 - q 3 <;> simp [hadd]
      _ = (N : Complex) * ∑ q : Fin 4 → ZMod N,
          if IsSimultaneouslyAdditive sigma q then
            (((N : Real) ^ p *
              (lambda (q 0) * lambda (q 1) * lambda (q 2) * lambda (q 3)) :
                Real) : Complex)
          else 0 := by
            congr 1
            apply Finset.sum_congr rfl
            intro q _
            rw [prop141_sum_b_product]
            by_cases hadd : q 0 - q 1 = q 2 - q 3 <;>
              by_cases hsigma : ∀ i,
                sigma i (q 0) - sigma i (q 1) =
                  sigma i (q 2) - sigma i (q 3) <;>
              simp [IsSimultaneouslyAdditive, hadd, hsigma]
      _ = (N : Complex) * ((N : Complex) ^ p *
          ∑ q : Fin 4 → ZMod N,
            if IsSimultaneouslyAdditive sigma q then
              ((lambda (q 0) * lambda (q 1) * lambda (q 2) * lambda (q 3) :
                Real) : Complex)
            else 0) := by
              congr 1
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro q _
              by_cases hq : IsSimultaneouslyAdditive sigma q
              · rw [if_pos hq, if_pos hq]
                push_cast
                rfl
              · rw [if_neg hq, if_neg hq]
                simp
      _ = (((N : Real) ^ (p + 1) * simultaneouslyAdditiveWeight lambda sigma :
          Real) : Complex) := by
            unfold simultaneouslyAdditiveWeight
            rw [show
              (∑ q : Fin 4 → ZMod N,
                if IsSimultaneouslyAdditive sigma q then
                  ((lambda (q 0) * lambda (q 1) * lambda (q 2) *
                    lambda (q 3) : Real) : Complex)
                else 0) =
              (((∑ q : Fin 4 → ZMod N,
                if IsSimultaneouslyAdditive sigma q then
                  lambda (q 0) * lambda (q 1) * lambda (q 2) * lambda (q 3)
                else 0 : Real)) : Complex) by
                  rw [Complex.ofReal_sum]
                  apply Finset.sum_congr rfl
                  intro q _
                  by_cases hq : IsSimultaneouslyAdditive sigma q <;> simp [hq]]
            push_cast
            ring
  exact Complex.ofReal_injective hcomplex

private def prop141QuadEquiv (X : Type*) : (Fin 4 → X) ≃ (Fin 4 → X) where
  toFun q := ![q 0, q 3, q 2, q 1]
  invFun q := ![q 0, q 3, q 2, q 1]
  left_inv q := by
    funext i
    fin_cases i <;> rfl
  right_inv q := by
    funext i
    fin_cases i <;> rfl

private lemma prop141_prod_fin_four (a : Fin 4 → Real) :
    (∏ i, a i) = a 0 * a 1 * a 2 * a 3 := by
  rw [Fin.prod_univ_four]

private lemma prop141_weight_eq_energy {N p : Nat} [NeZero N]
    (lambda : ZMod N → Real) (sigma : Fin p → ZMod N → ZMod N) :
    simultaneouslyAdditiveWeight lambda sigma =
      weightedSimultaneousAdditiveEnergy Finset.univ lambda sigma := by
  classical
  unfold simultaneouslyAdditiveWeight weightedSimultaneousAdditiveEnergy
  apply Fintype.sum_equiv (prop141QuadEquiv (ZMod N))
  intro q
  simp only [prop141QuadEquiv, Finset.mem_univ, forall_const, true_and,
    IsAdditiveQuadruple]
  by_cases hadd : q 0 - q 1 = q 2 - q 3
  · have hadd' : q 0 + q 3 = q 2 + q 1 :=
      sub_eq_sub_iff_add_eq_add.mp hadd
    by_cases hsigma : ∀ i,
        sigma i (q 0) - sigma i (q 1) =
          sigma i (q 2) - sigma i (q 3)
    · have hsigma' : ∀ i,
          sigma i (q 0) + sigma i (q 3) =
            sigma i (q 2) + sigma i (q 1) := fun i =>
        sub_eq_sub_iff_add_eq_add.mp (hsigma i)
      rw [if_pos ⟨hadd, hsigma⟩, if_pos ⟨hadd', hsigma'⟩,
        prop141_prod_fin_four]
      change lambda (q 0) * lambda (q 1) * lambda (q 2) * lambda (q 3) =
        lambda (q 0) * lambda (q 3) * lambda (q 2) * lambda (q 1)
      ring
    · have hsigma' : ¬ ∀ i,
          sigma i (q 0) + sigma i (q 3) =
            sigma i (q 2) + sigma i (q 1) := by
        intro h
        exact hsigma fun i => sub_eq_sub_iff_add_eq_add.mpr (h i)
      rw [if_neg (fun h => hsigma h.2), if_neg]
      exact fun h => hsigma' h.2
  · have hadd' : q 0 + q 3 ≠ q 2 + q 1 := fun h =>
      hadd (sub_eq_sub_iff_add_eq_add.mpr h)
    rw [if_neg]
    · rw [if_neg]
      exact fun h => hadd' h.1
    · exact fun h => hadd h.1

private lemma prop141_fourthB_total_eq_energy {N p : Nat} [NeZero N]
    (lambda : ZMod N → Real) (sigma : Fin p → ZMod N → ZMod N) :
    (∑ _y : Fin p → ZMod N, ∑ _x : Fin p → ZMod N,
        ∑ u : Fin p → ZMod N, ∑ _w : Fin p → ZMod N,
          ∑ r : ZMod N, ‖fourier (prop141B lambda sigma u) r‖ ^ 4) =
      (N : Real) ^ (4 * p + 1) *
        weightedSimultaneousAdditiveEnergy Finset.univ lambda sigma := by
  let U := Fin p → ZMod N
  have hcard : Fintype.card U = N ^ p := by simp [U]
  calc
    _ = ∑ y : U, ∑ u : U, ∑ _x : U, ∑ _w : U,
        ∑ r : ZMod N, ‖fourier (prop141B lambda sigma u) r‖ ^ 4 := by
          apply Finset.sum_congr rfl
          intro y _
          exact Finset.sum_comm
    _ = ∑ u : U, ∑ _y : U, ∑ _x : U, ∑ _w : U,
        ∑ r : ZMod N, ‖fourier (prop141B lambda sigma u) r‖ ^ 4 :=
      Finset.sum_comm
    _ = (N : Real) ^ (3 * p) *
        ∑ u : U, ∑ r : ZMod N,
          ‖fourier (prop141B lambda sigma u) r‖ ^ 4 := by
            simp only [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
            push_cast
            simp_rw [← Finset.mul_sum]
            rw [show 3 * p = p + p + p by omega, pow_add, pow_add]
            ring
    _ = (N : Real) ^ (3 * p) *
        ((N : Real) ^ (p + 1) *
          simultaneouslyAdditiveWeight lambda sigma) := by
            rw [prop141_fourthB_eq_weight]
    _ = (N : Real) ^ (4 * p + 1) *
        weightedSimultaneousAdditiveEnergy Finset.univ lambda sigma := by
          rw [prop141_weight_eq_energy]
          rw [show 4 * p + 1 = 3 * p + (p + 1) by omega, pow_add]
          ring

/-- Proposition 14.1 follows by expanding the squared Fourier coefficients,
applying Cauchy--Schwarz over the four vector variables, introducing a common
scalar shift, and using character orthogonality for the `Fin p` family. -/
theorem proposition_14_1_holds : proposition_14_1 := by
  intro N p _ lambda f sigma alpha hAlpha hlambda hf hlarge
  let L1 : Real :=
    ∑ y : Fin p → ZMod N, ∑ x : Fin p → ZMod N,
      ∑ u : Fin p → ZMod N, ∑ w : Fin p → ZMod N,
        ‖∑ h : ZMod N, prop141InnerTerm lambda f sigma y x u w h‖
  let L2 : Real :=
    ∑ y : Fin p → ZMod N, ∑ x : Fin p → ZMod N,
      ∑ u : Fin p → ZMod N, ∑ w : Fin p → ZMod N,
        ‖∑ h : ZMod N, prop141InnerTerm lambda f sigma y x u w h‖ ^ 2
  let mixed : Real :=
    ∑ y : Fin p → ZMod N, ∑ x : Fin p → ZMod N,
      ∑ u : Fin p → ZMod N, ∑ w : Fin p → ZMod N,
        ∑ r : ZMod N,
          ‖fourier (prop141A f y x u w) r‖ ^ 2 *
            ‖fourier (prop141B lambda sigma u) r‖ ^ 2
  let fourthA : Real :=
    ∑ y : Fin p → ZMod N, ∑ x : Fin p → ZMod N,
      ∑ u : Fin p → ZMod N, ∑ w : Fin p → ZMod N,
        ∑ r : ZMod N, ‖fourier (prop141A f y x u w) r‖ ^ 4
  let fourthB : Real :=
    ∑ _y : Fin p → ZMod N, ∑ _x : Fin p → ZMod N,
      ∑ u : Fin p → ZMod N, ∑ _w : Fin p → ZMod N,
        ∑ r : ZMod N, ‖fourier (prop141B lambda sigma u) r‖ ^ 4
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hN4p : (0 : Real) < (N : Real) ^ (4 * p) := by positivity
  have hN4p4 : (0 : Real) < (N : Real) ^ (4 * p + 4) := by positivity
  have hN4p1 : (0 : Real) < (N : Real) ^ (4 * p + 1) := by positivity
  have hL1 : alpha * (N : Real) ^ (4 * p + 1) ≤ L1 := hlarge.trans <| by
    simpa only [L1] using prop141_initial_bound lambda f sigma hlambda hf
  have hL1_nonneg : 0 ≤ L1 := by
    dsimp only [L1]
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hbase_nonneg : 0 ≤ alpha * (N : Real) ^ (4 * p + 1) :=
    mul_nonneg hAlpha (by positivity)
  have hL1sq :
      (alpha * (N : Real) ^ (4 * p + 1)) ^ 2 ≤ L1 ^ 2 :=
    (sq_le_sq₀ hbase_nonneg hL1_nonneg).2 hL1
  have hCauchy1 : L1 ^ 2 ≤ (N : Real) ^ (4 * p) * L2 := by
    simpa only [L1, L2] using
      (prop141_l1_cauchy (N := N) (p := p)
        (fun y x u w =>
          ‖∑ h : ZMod N, prop141InnerTerm lambda f sigma y x u w h‖))
  have hL2 : alpha ^ 2 * (N : Real) ^ (4 * p + 2) ≤ L2 := by
    apply le_of_mul_le_mul_left _ hN4p
    calc
      (N : Real) ^ (4 * p) *
          (alpha ^ 2 * (N : Real) ^ (4 * p + 2)) =
          (alpha * (N : Real) ^ (4 * p + 1)) ^ 2 := by
            rw [show 4 * p + 2 = 4 * p + 1 + 1 by omega,
              pow_add, pow_succ]
            ring
      _ ≤ L1 ^ 2 := hL1sq
      _ ≤ (N : Real) ^ (4 * p) * L2 := hCauchy1
  have hmixed_eq : mixed = (N : Real) ^ 2 * L2 := by
    simpa only [mixed, L2] using prop141_mixed_eq_l2 lambda f sigma
  have hmixed : alpha ^ 2 * (N : Real) ^ (4 * p + 4) ≤ mixed := by
    calc
      alpha ^ 2 * (N : Real) ^ (4 * p + 4) =
          (N : Real) ^ 2 *
            (alpha ^ 2 * (N : Real) ^ (4 * p + 2)) := by
              rw [show 4 * p + 4 = 2 + (4 * p + 2) by omega, pow_add]
              ring
      _ ≤ (N : Real) ^ 2 * L2 :=
        mul_le_mul_of_nonneg_left hL2 (by positivity)
      _ = mixed := hmixed_eq.symm
  have hfourthA : fourthA ≤ (N : Real) ^ (4 * p + 4) := by
    simpa only [fourthA] using prop141_fourthA_le f hf
  have hmixed_nonneg : 0 ≤ mixed := by
    dsimp only [mixed]
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hfourthB_nonneg : 0 ≤ fourthB := by
    dsimp only [fourthB]
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => pow_nonneg (norm_nonneg _) 4
  have hmixed_sq :
      (alpha ^ 2 * (N : Real) ^ (4 * p + 4)) ^ 2 ≤ mixed ^ 2 := by
    apply (sq_le_sq₀
      (mul_nonneg (sq_nonneg _) (pow_nonneg hN.le _)) hmixed_nonneg).2
    exact hmixed
  have hglobal : mixed ^ 2 ≤ fourthA * fourthB := by
    simpa only [mixed, fourthA, fourthB] using
      prop141_global_cauchy lambda f sigma
  have hfourthB :
      alpha ^ 4 * (N : Real) ^ (4 * p + 4) ≤ fourthB := by
    apply le_of_mul_le_mul_left _ hN4p4
    calc
      (N : Real) ^ (4 * p + 4) *
          (alpha ^ 4 * (N : Real) ^ (4 * p + 4)) =
          (alpha ^ 2 * (N : Real) ^ (4 * p + 4)) ^ 2 := by ring
      _ ≤ mixed ^ 2 := hmixed_sq
      _ ≤ fourthA * fourthB := hglobal
      _ ≤ (N : Real) ^ (4 * p + 4) * fourthB :=
        mul_le_mul_of_nonneg_right hfourthA hfourthB_nonneg
  have hfourthB_eq :
      fourthB = (N : Real) ^ (4 * p + 1) *
        weightedSimultaneousAdditiveEnergy Finset.univ lambda sigma := by
    simpa only [fourthB] using prop141_fourthB_total_eq_energy lambda sigma
  apply le_of_mul_le_mul_left _ hN4p1
  calc
    (N : Real) ^ (4 * p + 1) * (alpha ^ 4 * (N : Real) ^ 3) =
        alpha ^ 4 * (N : Real) ^ (4 * p + 4) := by
          calc
            _ = alpha ^ 4 * (N : Real) ^ ((4 * p + 1) + 3) := by
              rw [pow_add]
              ring
            _ = _ := by rw [show (4 * p + 1) + 3 = 4 * p + 4 by omega]
    _ ≤ fourthB := hfourthB
    _ = (N : Real) ^ (4 * p + 1) *
        weightedSimultaneousAdditiveEnergy Finset.univ lambda sigma :=
      hfourthB_eq

end LeanProofs.GowersSzemeredi

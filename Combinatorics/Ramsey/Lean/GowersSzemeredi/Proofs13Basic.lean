import GowersSzemeredi.Sections12_13
import GowersSzemeredi.Proofs01_03
import Mathlib.Analysis.MeanInequalities
import Mathlib.Algebra.Order.Chebyshev

/-!
# Basic proofs for Gowers (2001), Section 13

This module proves Lemma 13.1 and its indicator-function specialization,
Corollary 13.2.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

@[simp] private lemma prop131_exponential_add {N : Nat} [NeZero N]
    (x y : ZMod N) : exponential (x + y) = exponential x * exponential y := by
  exact AddChar.map_add_eq_mul (ZMod.stdAddChar (N := N)) x y

@[simp] private lemma prop131_star_exponential {N : Nat} [NeZero N]
    (x : ZMod N) : star (exponential x) = exponential (-x) := by
  simpa only [exponential, starRingEnd_apply] using
    (AddChar.map_neg_eq_conj (ZMod.stdAddChar (N := N)) x).symm

private def prop131Outer {N : Nat} (f : Pair N → Complex)
    (u x y y' : ZMod N) : Complex :=
  star (f (x, y')) * f (x - u, y)

private def prop131InnerTerm {N : Nat} [NeZero N]
    (f : Pair N → Complex) (sigma : ZMod N → ZMod N)
    (u x y y' h : ZMod N) : Complex :=
  f (x, y' + h) * star (f (x - u, y + h)) *
    exponential (-(u * sigma h))

private lemma prop131_coeff_sq_expansion {N : Nat} [NeZero N]
    (f : Pair N → Complex) (h r : ZMod N) :
    ((‖fourier (verticalCorrelation f h) r‖ ^ 2 : Real) : Complex) =
      ∑ x : ZMod N, ∑ y' : ZMod N, ∑ u : ZMod N, ∑ y : ZMod N,
        prop131Outer f u x y y' *
          (f (x, y' + h) * star (f (x - u, y + h)) *
            exponential (-(u * r))) := by
  simp only [fourier, verticalCorrelation, ZMod.dft_apply, smul_eq_mul]
  calc
    ((‖∑ x : ZMod N, exponential (-(x * r)) *
        ∑ y : ZMod N, f (x, y + h) * star (f (x, y))‖ ^ 2 : Real) : Complex) =
        (∑ x : ZMod N, exponential (-(x * r)) *
          ∑ y : ZMod N, f (x, y + h) * star (f (x, y))) *
        star (∑ t : ZMod N, exponential (-(t * r)) *
          ∑ z : ZMod N, f (t, z + h) * star (f (t, z))) := by
            rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow]
    _ = ∑ x : ZMod N, ∑ y : ZMod N, ∑ t : ZMod N, ∑ z : ZMod N,
        (exponential (-(x * r)) * (f (x, y + h) * star (f (x, y)))) *
          ((f (t, z) * star (f (t, z + h))) * exponential (t * r)) := by
            simp only [star_sum, star_mul, star_star, prop131_star_exponential,
              neg_neg]
            simp_rw [mul_sum, sum_mul]
            simp_rw [mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro x _
            rw [Finset.sum_comm]
    _ = ∑ x : ZMod N, ∑ y : ZMod N, ∑ u : ZMod N, ∑ z : ZMod N,
        (exponential (-(x * r)) * (f (x, y + h) * star (f (x, y)))) *
          ((f (x - u, z) * star (f (x - u, z + h))) *
            exponential ((x - u) * r)) := by
              apply Finset.sum_congr rfl
              intro x _
              apply Finset.sum_congr rfl
              intro y _
              rw [← (Equiv.subLeft x).sum_comp]
              rfl
    _ = ∑ x : ZMod N, ∑ y' : ZMod N, ∑ u : ZMod N, ∑ y : ZMod N,
        prop131Outer f u x y y' *
          (f (x, y' + h) * star (f (x - u, y + h)) *
            exponential (-(u * r))) := by
              apply Finset.sum_congr rfl
              intro x _
              apply Finset.sum_congr rfl
              intro y' _
              apply Finset.sum_congr rfl
              intro u _
              apply Finset.sum_congr rfl
              intro y _
              have hphase :
                  exponential (-(x * r)) * exponential ((x - u) * r) =
                    exponential (-(u * r)) := by
                rw [← prop131_exponential_add]
                congr 1
                ring
              rw [prop131Outer, ← hphase]
              ring

private lemma prop131_energy_expansion {N : Nat} [NeZero N]
    (f : Pair N → Complex) (B : Finset (ZMod N))
    (sigma : ZMod N → ZMod N) :
    (((∑ h ∈ B,
        ‖fourier (verticalCorrelation f h) (sigma h)‖ ^ 2 : Real)) : Complex) =
      ∑ x : ZMod N, ∑ y' : ZMod N, ∑ u : ZMod N, ∑ y : ZMod N,
        prop131Outer f u x y y' *
          ∑ h ∈ B, prop131InnerTerm f sigma u x y y' h := by
  rw [Complex.ofReal_sum]
  simp_rw [prop131_coeff_sq_expansion]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y' _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [← Finset.mul_sum]
  rfl

private lemma prop131_outer_norm_le {N : Nat} (f : Pair N → Complex)
    (hf : DiscValued f) (u x y y' : ZMod N) :
    ‖prop131Outer f u x y y'‖ ≤ 1 := by
  rw [prop131Outer, norm_mul, norm_star]
  calc
    ‖f (x, y')‖ * ‖f (x - u, y)‖ ≤ 1 * 1 := by gcongr <;> apply hf
    _ = 1 := one_mul 1

private lemma prop131_initial_bound {N : Nat} [NeZero N]
    (f : Pair N → Complex) (B : Finset (ZMod N))
    (sigma : ZMod N → ZMod N) (hf : DiscValued f) :
    (∑ h ∈ B, ‖fourier (verticalCorrelation f h) (sigma h)‖ ^ 2) ≤
      ∑ x : ZMod N, ∑ y' : ZMod N, ∑ u : ZMod N, ∑ y : ZMod N,
        ‖∑ h ∈ B, prop131InnerTerm f sigma u x y y' h‖ := by
  let energy : Real :=
    ∑ h ∈ B, ‖fourier (verticalCorrelation f h) (sigma h)‖ ^ 2
  have henergy : 0 ≤ energy := by
    dsimp only [energy]
    positivity
  calc
    (∑ h ∈ B, ‖fourier (verticalCorrelation f h) (sigma h)‖ ^ 2) =
        ‖((energy : Real) : Complex)‖ := by
          rw [Complex.norm_real, Real.norm_of_nonneg henergy]
    _ = ‖∑ x : ZMod N, ∑ y' : ZMod N, ∑ u : ZMod N, ∑ y : ZMod N,
        prop131Outer f u x y y' *
          ∑ h ∈ B, prop131InnerTerm f sigma u x y y' h‖ := by
            rw [prop131_energy_expansion f B sigma]
    _ ≤ ∑ x : ZMod N,
        ‖∑ y' : ZMod N, ∑ u : ZMod N, ∑ y : ZMod N,
          prop131Outer f u x y y' *
            ∑ h ∈ B, prop131InnerTerm f sigma u x y y' h‖ :=
              norm_sum_le _ _
    _ ≤ ∑ x : ZMod N, ∑ y' : ZMod N,
        ‖∑ u : ZMod N, ∑ y : ZMod N,
          prop131Outer f u x y y' *
            ∑ h ∈ B, prop131InnerTerm f sigma u x y y' h‖ := by
              gcongr with x
              exact norm_sum_le _ _
    _ ≤ ∑ x : ZMod N, ∑ y' : ZMod N, ∑ u : ZMod N,
        ‖∑ y : ZMod N, prop131Outer f u x y y' *
          ∑ h ∈ B, prop131InnerTerm f sigma u x y y' h‖ := by
            gcongr with x y'
            exact norm_sum_le _ _
    _ ≤ ∑ x : ZMod N, ∑ y' : ZMod N, ∑ u : ZMod N, ∑ y : ZMod N,
        ‖prop131Outer f u x y y' *
          ∑ h ∈ B, prop131InnerTerm f sigma u x y y' h‖ := by
            gcongr with x y' u
            exact norm_sum_le _ _
    _ ≤ ∑ x : ZMod N, ∑ y' : ZMod N, ∑ u : ZMod N, ∑ y : ZMod N,
        ‖∑ h ∈ B, prop131InnerTerm f sigma u x y y' h‖ := by
          apply Finset.sum_le_sum
          intro x _
          apply Finset.sum_le_sum
          intro y' _
          apply Finset.sum_le_sum
          intro u _
          apply Finset.sum_le_sum
          intro y _
          rw [norm_mul]
          exact mul_le_of_le_one_left (norm_nonneg _)
            (prop131_outer_norm_le f hf u x y y')

private lemma prop131_l1_cauchy {N : Nat} [NeZero N]
    (F : ZMod N → ZMod N → ZMod N → ZMod N → Real) :
    (∑ x : ZMod N, ∑ y' : ZMod N, ∑ u : ZMod N, ∑ y : ZMod N,
        F x y' u y) ^ 2 ≤
      (N : Real) ^ 4 *
        ∑ x : ZMod N, ∑ y' : ZMod N, ∑ u : ZMod N, ∑ y : ZMod N,
          (F x y' u y) ^ 2 := by
  calc
    _ ≤ (N : Real) * ∑ x : ZMod N,
        (∑ y' : ZMod N, ∑ u : ZMod N, ∑ y : ZMod N,
          F x y' u y) ^ 2 := by
            simpa only [Finset.card_univ, ZMod.card] using
              (sq_sum_le_card_mul_sum_sq
                (s := (Finset.univ : Finset (ZMod N)))
                (f := fun x => ∑ y' : ZMod N, ∑ u : ZMod N, ∑ y : ZMod N,
                  F x y' u y))
    _ ≤ (N : Real) * ∑ x : ZMod N, (N : Real) * ∑ y' : ZMod N,
        (∑ u : ZMod N, ∑ y : ZMod N, F x y' u y) ^ 2 := by
          gcongr with x
          simpa only [Finset.card_univ, ZMod.card] using
            (sq_sum_le_card_mul_sum_sq
              (s := (Finset.univ : Finset (ZMod N)))
              (f := fun y' => ∑ u : ZMod N, ∑ y : ZMod N, F x y' u y))
    _ ≤ (N : Real) * ∑ x : ZMod N, (N : Real) * ∑ y' : ZMod N,
        (N : Real) * ∑ u : ZMod N,
          (∑ y : ZMod N, F x y' u y) ^ 2 := by
            gcongr with x y'
            simpa only [Finset.card_univ, ZMod.card] using
              (sq_sum_le_card_mul_sum_sq
                (s := (Finset.univ : Finset (ZMod N)))
                (f := fun u => ∑ y : ZMod N, F x y' u y))
    _ ≤ (N : Real) * ∑ x : ZMod N, (N : Real) * ∑ y' : ZMod N,
        (N : Real) * ∑ u : ZMod N, (N : Real) * ∑ y : ZMod N,
          (F x y' u y) ^ 2 := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply Finset.sum_le_sum
            intro x _
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply Finset.sum_le_sum
            intro y' _
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply Finset.sum_le_sum
            intro u _
            simpa only [Finset.card_univ, ZMod.card] using
              (sq_sum_le_card_mul_sum_sq
                (s := (Finset.univ : Finset (ZMod N))) (f := F x y' u))
    _ = _ := by
      simp_rw [← Finset.mul_sum]
      ring

private def prop131A {N : Nat} (f : Pair N → Complex)
    (u x w h : ZMod N) : Complex :=
  f (x, w + h) * star (f (x - u, h))

private def prop131G {N : Nat} [NeZero N] (B : Finset (ZMod N))
    (sigma : ZMod N → ZMod N) (u h : ZMod N) : Complex :=
  indicator B h * exponential (sigma h * u)

@[simp] private lemma prop131_star_indicator {N : Nat}
    (B : Finset (ZMod N)) (h : ZMod N) :
    star (indicator B h) = indicator B h := by
  classical
  simp only [indicator]
  split_ifs <;> simp

private def prop131AddRightEquiv {N : Nat} (y : ZMod N) : ZMod N ≃ ZMod N where
  toFun h := h + y
  invFun s := s - y
  left_inv h := by ring
  right_inv s := by ring

@[simp] private lemma prop131AddRightEquiv_apply {N : Nat} (y h : ZMod N) :
    prop131AddRightEquiv y h = h + y := rfl

@[simp] private lemma prop131AddRightEquiv_symm_apply {N : Nat} (y h : ZMod N) :
    (prop131AddRightEquiv y).symm h = h - y := rfl

private lemma prop131_correlation_eq {N : Nat} [NeZero N]
    (f : Pair N → Complex) (B : Finset (ZMod N))
    (sigma : ZMod N → ZMod N) (u x w y : ZMod N) :
    correlation (prop131A f u x w) (prop131G B sigma u) y =
      ∑ h ∈ B, prop131InnerTerm f sigma u x y (w + y) h := by
  classical
  simp only [correlation]
  rw [← (prop131AddRightEquiv y).sum_comp]
  simp only [prop131AddRightEquiv_apply, add_sub_cancel_right]
  unfold prop131A prop131G prop131InnerTerm
  simp only [star_mul, prop131_star_indicator, prop131_star_exponential]
  simp only [indicator, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  rw [show (Finset.univ.filter fun h : ZMod N => h ∈ B) = B by
    ext h
    simp]
  apply Finset.sum_congr rfl
  intro h hh
  have hwy : w + (h + y) = w + y + h := by ring
  have hyh : h + y = y + h := by ring
  have hphase : -(sigma h * u) = -(u * sigma h) := by ring
  rw [hwy, hyh, hphase]

private lemma prop131_shift_pair_sum {N : Nat} [NeZero N]
    (F : ZMod N → ZMod N → Real) :
    (∑ y' : ZMod N, ∑ y : ZMod N, F y y') =
      ∑ w : ZMod N, ∑ y : ZMod N, F y (w + y) := by
  calc
    _ = ∑ y : ZMod N, ∑ y' : ZMod N, F y y' := Finset.sum_comm
    _ = ∑ y : ZMod N, ∑ w : ZMod N, F y (w + y) := by
      apply Finset.sum_congr rfl
      intro y _
      exact Fintype.sum_equiv (prop131AddRightEquiv y).symm
        (fun y' => F y y') (fun w => F y (w + y)) (fun y' => by
          congr 2
          simp)
    _ = _ := Finset.sum_comm

private lemma prop131_mixed_eq_l2 {N : Nat} [NeZero N]
    (f : Pair N → Complex) (B : Finset (ZMod N))
    (sigma : ZMod N → ZMod N) :
    (∑ u : ZMod N, ∑ x : ZMod N, ∑ w : ZMod N, ∑ r : ZMod N,
        ‖fourier (prop131A f u x w) r‖ ^ 2 *
          ‖fourier (prop131G B sigma u) r‖ ^ 2) =
      (N : Real) *
        ∑ x : ZMod N, ∑ y' : ZMod N, ∑ u : ZMod N, ∑ y : ZMod N,
          ‖∑ h ∈ B, prop131InnerTerm f sigma u x y y' h‖ ^ 2 := by
  calc
    _ = ∑ u : ZMod N, ∑ x : ZMod N, ∑ w : ZMod N,
        (N : Real) * ∑ y : ZMod N,
          ‖correlation (prop131A f u x w) (prop131G B sigma u) y‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro u _
            apply Finset.sum_congr rfl
            intro x _
            apply Finset.sum_congr rfl
            intro w _
            exact lemma_2_1_holds N (prop131A f u x w) (prop131G B sigma u)
    _ = (N : Real) * ∑ u : ZMod N, ∑ x : ZMod N, ∑ w : ZMod N,
        ∑ y : ZMod N,
          ‖correlation (prop131A f u x w) (prop131G B sigma u) y‖ ^ 2 := by
            simp_rw [← Finset.mul_sum]
    _ = (N : Real) * ∑ u : ZMod N, ∑ x : ZMod N, ∑ w : ZMod N,
        ∑ y : ZMod N,
          ‖∑ h ∈ B, prop131InnerTerm f sigma u x y (w + y) h‖ ^ 2 := by
            congr 1
            apply Finset.sum_congr rfl
            intro u _
            apply Finset.sum_congr rfl
            intro x _
            apply Finset.sum_congr rfl
            intro w _
            apply Finset.sum_congr rfl
            intro y _
            rw [prop131_correlation_eq]
    _ = (N : Real) *
        ∑ x : ZMod N, ∑ y' : ZMod N, ∑ u : ZMod N, ∑ y : ZMod N,
          ‖∑ h ∈ B, prop131InnerTerm f sigma u x y y' h‖ ^ 2 := by
            congr 1
            calc
              (∑ u : ZMod N, ∑ x : ZMod N, ∑ w : ZMod N,
                  ∑ y : ZMod N,
                    ‖∑ h ∈ B,
                      prop131InnerTerm f sigma u x y (w + y) h‖ ^ 2) =
                  ∑ x : ZMod N, ∑ u : ZMod N, ∑ w : ZMod N,
                    ∑ y : ZMod N,
                      ‖∑ h ∈ B,
                        prop131InnerTerm f sigma u x y (w + y) h‖ ^ 2 :=
                          Finset.sum_comm
              _ = ∑ x : ZMod N, ∑ u : ZMod N, ∑ y' : ZMod N,
                  ∑ y : ZMod N,
                    ‖∑ h ∈ B, prop131InnerTerm f sigma u x y y' h‖ ^ 2 := by
                      apply Finset.sum_congr rfl
                      intro x _
                      apply Finset.sum_congr rfl
                      intro u _
                      exact (prop131_shift_pair_sum (N := N)
                        (fun y y' =>
                          ‖∑ h ∈ B,
                            prop131InnerTerm f sigma u x y y' h‖ ^ 2)).symm
              _ = _ := by
                apply Finset.sum_congr rfl
                intro x _
                exact Finset.sum_comm

private lemma prop131_fourth_moment_le {N : Nat} [NeZero N]
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

private lemma prop131A_disc {N : Nat} (f : Pair N → Complex)
    (hf : DiscValued f) (u x w : ZMod N) : DiscValued (prop131A f u x w) := by
  intro h
  rw [prop131A, norm_mul, norm_star]
  calc
    ‖f (x, w + h)‖ * ‖f (x - u, h)‖ ≤ 1 * 1 := by gcongr <;> apply hf
    _ = 1 := one_mul 1

private lemma prop131_fourthA_le {N : Nat} [NeZero N]
    (f : Pair N → Complex) (hf : DiscValued f) :
    (∑ u : ZMod N, ∑ x : ZMod N, ∑ w : ZMod N, ∑ r : ZMod N,
        ‖fourier (prop131A f u x w) r‖ ^ 4) ≤ (N : Real) ^ 7 := by
  calc
    _ ≤ ∑ _u : ZMod N, ∑ _x : ZMod N, ∑ _w : ZMod N,
        (N : Real) ^ 4 := by
          apply Finset.sum_le_sum
          intro u _
          apply Finset.sum_le_sum
          intro x _
          apply Finset.sum_le_sum
          intro w _
          exact prop131_fourth_moment_le (prop131A f u x w)
            (prop131A_disc f hf u x w)
    _ = (N : Real) ^ 7 := by simp; ring

private abbrev prop131QuadMem {N : Nat} (B : Finset (ZMod N))
    (q : Fin 4 → ZMod N) : Prop :=
  q 0 ∈ B ∧ q 1 ∈ B ∧ q 2 ∈ B ∧ q 3 ∈ B

private abbrev prop131AltAdditive {N : Nat} (B : Finset (ZMod N))
    (sigma : ZMod N → ZMod N) (q : Fin 4 → ZMod N) : Prop :=
  prop131QuadMem B q ∧ q 0 - q 1 = q 2 - q 3 ∧
    sigma (q 0) - sigma (q 1) = sigma (q 2) - sigma (q 3)

private def prop131QuadEquiv (X : Type*) : (Fin 4 → X) ≃ (Fin 4 → X) where
  toFun q := ![q 0, q 3, q 2, q 1]
  invFun q := ![q 0, q 3, q 2, q 1]
  left_inv q := by
    funext i
    fin_cases i <;> rfl
  right_inv q := by
    funext i
    fin_cases i <;> rfl

private lemma prop131_alt_count_eq {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (sigma : ZMod N → ZMod N) :
    countWhere (prop131AltAdditive B sigma) = phiAdditiveCount B sigma := by
  classical
  unfold countWhere phiAdditiveCount
  apply Finset.card_equiv (prop131QuadEquiv (ZMod N))
  intro q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [prop131AltAdditive, prop131QuadMem, IsPhiAdditive,
    IsAdditiveQuadruple, prop131QuadEquiv]
  constructor
  · rintro ⟨⟨h0, h1, h2, h3⟩, hadd, hsigma⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i
      fin_cases i <;> assumption
    · exact sub_eq_sub_iff_add_eq_add.mp hadd
    · exact sub_eq_sub_iff_add_eq_add.mp hsigma
  · rintro ⟨hmem, hadd, hsigma⟩
    have h0 := hmem 0
    have h1 := hmem 1
    have h2 := hmem 2
    have h3 := hmem 3
    exact ⟨⟨h0, h3, h2, h1⟩,
      sub_eq_sub_iff_add_eq_add.mpr hadd,
      sub_eq_sub_iff_add_eq_add.mpr hsigma⟩

private lemma prop131_g_product {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (sigma : ZMod N → ZMod N)
    (u : ZMod N) (q : Fin 4 → ZMod N) :
    prop131G B sigma u (q 0) *
        star (prop131G B sigma u (q 1) * prop131G B sigma u (q 2)) *
        prop131G B sigma u (q 3) =
      if prop131QuadMem B q then
        exponential
          ((sigma (q 0) - sigma (q 1) - sigma (q 2) + sigma (q 3)) * u)
      else 0 := by
  classical
  simp only [prop131G, indicator, star_mul]
  by_cases h0 : q 0 ∈ B <;> by_cases h1 : q 1 ∈ B <;>
    by_cases h2 : q 2 ∈ B <;> by_cases h3 : q 3 ∈ B
  all_goals simp only [h0, h1, h2, h3, if_true, if_false, one_mul, zero_mul,
    mul_zero, star_zero, star_one, prop131QuadMem, and_self, and_true]
  all_goals try {rfl}
  rw [prop131_star_exponential, prop131_star_exponential]
  calc
    _ = exponential (sigma (q 0) * u +
        (-(sigma (q 2) * u) + (-(sigma (q 1) * u) + sigma (q 3) * u))) := by
          rw [prop131_exponential_add, prop131_exponential_add,
            prop131_exponential_add]
          ring
    _ = _ := by
      congr 1
      ring

private lemma prop131_sum_exponential_mul {N : Nat} [NeZero N]
    (x : ZMod N) :
    ∑ u : ZMod N, exponential (x * u) =
      if x = 0 then (N : Complex) else 0 := by
  simpa [exponential, mul_comm] using
    AddChar.sum_mulShift x (ZMod.isPrimitive_stdAddChar N)

private lemma prop131_sum_g_product {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (sigma : ZMod N → ZMod N)
    (q : Fin 4 → ZMod N) :
    (∑ u : ZMod N,
      prop131G B sigma u (q 0) *
        star (prop131G B sigma u (q 1) * prop131G B sigma u (q 2)) *
        prop131G B sigma u (q 3)) =
      if prop131QuadMem B q ∧
          sigma (q 0) - sigma (q 1) = sigma (q 2) - sigma (q 3)
        then (N : Complex) else 0 := by
  simp_rw [prop131_g_product]
  by_cases hmem : prop131QuadMem B q
  · simp_rw [if_pos hmem]
    rw [prop131_sum_exponential_mul]
    by_cases hsigma :
        sigma (q 0) - sigma (q 1) = sigma (q 2) - sigma (q 3)
    · have hcond : prop131QuadMem B q ∧
          sigma (q 0) - sigma (q 1) = sigma (q 2) - sigma (q 3) :=
        ⟨hmem, hsigma⟩
      have hzero :
          sigma (q 0) - sigma (q 1) - sigma (q 2) + sigma (q 3) = 0 := by
        calc
          _ = (sigma (q 0) - sigma (q 1)) -
              (sigma (q 2) - sigma (q 3)) := by abel
          _ = 0 := by rw [hsigma, sub_self]
      rw [if_pos hzero, if_pos hcond]
    · have hne :
          sigma (q 0) - sigma (q 1) - sigma (q 2) + sigma (q 3) ≠ 0 := by
        intro hzero
        apply hsigma
        apply sub_eq_zero.mp
        calc
          (sigma (q 0) - sigma (q 1)) - (sigma (q 2) - sigma (q 3)) =
              sigma (q 0) - sigma (q 1) - sigma (q 2) + sigma (q 3) := by abel
          _ = 0 := hzero
      have hcond : ¬ (prop131QuadMem B q ∧
          sigma (q 0) - sigma (q 1) = sigma (q 2) - sigma (q 3)) :=
        fun h => hsigma h.2
      rw [if_neg hne, if_neg hcond]
  · simp_rw [if_neg hmem]
    rw [if_neg (fun h => hmem h.1)]
    simp

private lemma prop131_g_fourth_eq_count {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (sigma : ZMod N → ZMod N) :
    (∑ u : ZMod N, ∑ r : ZMod N,
        ‖fourier (prop131G B sigma u) r‖ ^ 4) =
      (N : Real) ^ 2 * phiAdditiveCount B sigma := by
  classical
  have hcomplex :
      (((∑ u : ZMod N, ∑ r : ZMod N,
          ‖fourier (prop131G B sigma u) r‖ ^ 4 : Real)) : Complex) =
        (((N : Real) ^ 2 * countWhere (prop131AltAdditive B sigma) : Real) :
          Complex) := by
    rw [Complex.ofReal_sum]
    calc
      (∑ u : ZMod N,
          ((∑ r : ZMod N, ‖fourier (prop131G B sigma u) r‖ ^ 4 : Real) :
            Complex)) =
          ∑ u : ZMod N, (N : Complex) * ∑ q : Fin 4 → ZMod N,
            if q 0 - q 1 = q 2 - q 3 then
              prop131G B sigma u (q 0) *
                star (prop131G B sigma u (q 1) * prop131G B sigma u (q 2)) *
                prop131G B sigma u (q 3)
            else 0 := by
              apply Finset.sum_congr rfl
              intro u _
              exact identity_2_6_holds N (prop131G B sigma u)
      _ = (N : Complex) * ∑ q : Fin 4 → ZMod N,
          if q 0 - q 1 = q 2 - q 3 then
            ∑ u : ZMod N,
              prop131G B sigma u (q 0) *
                star (prop131G B sigma u (q 1) * prop131G B sigma u (q 2)) *
                prop131G B sigma u (q 3)
          else 0 := by
            rw [← Finset.mul_sum]
            congr 1
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro q _
            by_cases hadd : q 0 - q 1 = q 2 - q 3 <;> simp [hadd]
      _ = (N : Complex) * ∑ q : Fin 4 → ZMod N,
          if prop131AltAdditive B sigma q then (N : Complex) else 0 := by
            congr 1
            apply Finset.sum_congr rfl
            intro q _
            rw [prop131_sum_g_product]
            by_cases hmem : prop131QuadMem B q <;>
              by_cases hadd : q 0 - q 1 = q 2 - q 3 <;>
              by_cases hsigma :
                sigma (q 0) - sigma (q 1) = sigma (q 2) - sigma (q 3) <;>
              simp [prop131AltAdditive, hmem, hadd, hsigma]
      _ = (((N : Real) ^ 2 * countWhere (prop131AltAdditive B sigma) : Real) :
          Complex) := by
            push_cast
            unfold countWhere
            rw [← Finset.sum_filter]
            simp only [Finset.sum_const, nsmul_eq_mul]
            ring_nf
            congr 1
            norm_cast
            apply congrArg Finset.card
            ext q
            simp
  rw [prop131_alt_count_eq B sigma] at hcomplex
  exact Complex.ofReal_injective hcomplex

private lemma prop131_fourthG_eq_count {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (sigma : ZMod N → ZMod N) :
    (∑ u : ZMod N, ∑ _x : ZMod N, ∑ _w : ZMod N, ∑ r : ZMod N,
        ‖fourier (prop131G B sigma u) r‖ ^ 4) =
      (N : Real) ^ 4 * phiAdditiveCount B sigma := by
  calc
    _ = (N : Real) ^ 2 *
        ∑ u : ZMod N, ∑ r : ZMod N,
          ‖fourier (prop131G B sigma u) r‖ ^ 4 := by
            simp only [Finset.sum_const, Finset.card_univ, ZMod.card,
              nsmul_eq_mul]
            simp_rw [← Finset.mul_sum]
            ring
    _ = (N : Real) ^ 2 *
        ((N : Real) ^ 2 * phiAdditiveCount B sigma) := by
          rw [prop131_g_fourth_eq_count]
    _ = (N : Real) ^ 4 * phiAdditiveCount B sigma := by ring

private lemma prop131_global_cauchy {N : Nat} [NeZero N]
    (f : Pair N → Complex) (B : Finset (ZMod N))
    (sigma : ZMod N → ZMod N) :
    (∑ u : ZMod N, ∑ x : ZMod N, ∑ w : ZMod N, ∑ r : ZMod N,
        ‖fourier (prop131A f u x w) r‖ ^ 2 *
          ‖fourier (prop131G B sigma u) r‖ ^ 2) ^ 2 ≤
      (∑ u : ZMod N, ∑ x : ZMod N, ∑ w : ZMod N, ∑ r : ZMod N,
        ‖fourier (prop131A f u x w) r‖ ^ 4) *
      ∑ u : ZMod N, ∑ _x : ZMod N, ∑ _w : ZMod N, ∑ r : ZMod N,
        ‖fourier (prop131G B sigma u) r‖ ^ 4 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq
    ((((Finset.univ : Finset (ZMod N)) ×ˢ (Finset.univ : Finset (ZMod N))) ×ˢ
      (Finset.univ : Finset (ZMod N))) ×ˢ (Finset.univ : Finset (ZMod N)))
    (fun z => ‖fourier (prop131A f z.1.1.1 z.1.1.2 z.1.2) z.2‖ ^ 2)
    (fun z => ‖fourier (prop131G B sigma z.1.1.1) z.2‖ ^ 2)
  simpa only [Finset.sum_product, ← pow_mul] using h

/-- Lemma 13.1 follows from two Cauchy--Schwarz inequalities, the Fourier
correlation identity, and character orthogonality. -/
theorem lemma_13_1_holds : lemma_13_1 := by
  intro N _ f B sigma alpha hAlpha hf hlarge
  let L1 : Real :=
    ∑ x : ZMod N, ∑ y' : ZMod N, ∑ u : ZMod N, ∑ y : ZMod N,
      ‖∑ h ∈ B, prop131InnerTerm f sigma u x y y' h‖
  let L2 : Real :=
    ∑ x : ZMod N, ∑ y' : ZMod N, ∑ u : ZMod N, ∑ y : ZMod N,
      ‖∑ h ∈ B, prop131InnerTerm f sigma u x y y' h‖ ^ 2
  let mixed : Real :=
    ∑ u : ZMod N, ∑ x : ZMod N, ∑ w : ZMod N, ∑ r : ZMod N,
      ‖fourier (prop131A f u x w) r‖ ^ 2 *
        ‖fourier (prop131G B sigma u) r‖ ^ 2
  let fourthA : Real :=
    ∑ u : ZMod N, ∑ x : ZMod N, ∑ w : ZMod N, ∑ r : ZMod N,
      ‖fourier (prop131A f u x w) r‖ ^ 4
  let fourthG : Real :=
    ∑ u : ZMod N, ∑ _x : ZMod N, ∑ _w : ZMod N, ∑ r : ZMod N,
      ‖fourier (prop131G B sigma u) r‖ ^ 4
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hN4 : (0 : Real) < (N : Real) ^ 4 := by positivity
  have hN7 : (0 : Real) < (N : Real) ^ 7 := by positivity
  have hL1 : alpha * (N : Real) ^ 5 ≤ L1 := hlarge.trans <| by
    simpa only [L1] using prop131_initial_bound f B sigma hf
  have hL1_nonneg : 0 ≤ L1 := by
    dsimp only [L1]
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hbase_nonneg : 0 ≤ alpha * (N : Real) ^ 5 :=
    mul_nonneg hAlpha.le (by positivity)
  have hL1sq : (alpha * (N : Real) ^ 5) ^ 2 ≤ L1 ^ 2 :=
    (sq_le_sq₀ hbase_nonneg hL1_nonneg).2 hL1
  have hCauchy1 : L1 ^ 2 ≤ (N : Real) ^ 4 * L2 := by
    simpa only [L1, L2] using
      (prop131_l1_cauchy (N := N)
        (fun x y' u y =>
          ‖∑ h ∈ B, prop131InnerTerm f sigma u x y y' h‖))
  have hL2 : alpha ^ 2 * (N : Real) ^ 6 ≤ L2 := by
    apply le_of_mul_le_mul_left _ hN4
    calc
      (N : Real) ^ 4 * (alpha ^ 2 * (N : Real) ^ 6) =
          (alpha * (N : Real) ^ 5) ^ 2 := by ring
      _ ≤ L1 ^ 2 := hL1sq
      _ ≤ (N : Real) ^ 4 * L2 := hCauchy1
  have hmixed_eq : mixed = (N : Real) * L2 := by
    simpa only [mixed, L2] using prop131_mixed_eq_l2 f B sigma
  have hmixed : alpha ^ 2 * (N : Real) ^ 7 ≤ mixed := by
    calc
      alpha ^ 2 * (N : Real) ^ 7 =
          (N : Real) * (alpha ^ 2 * (N : Real) ^ 6) := by ring
      _ ≤ (N : Real) * L2 := mul_le_mul_of_nonneg_left hL2 hN.le
      _ = mixed := hmixed_eq.symm
  have hfourthA : fourthA ≤ (N : Real) ^ 7 := by
    simpa only [fourthA] using prop131_fourthA_le f hf
  have hmixed_nonneg : 0 ≤ mixed := by
    dsimp only [mixed]
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hfourthG_nonneg : 0 ≤ fourthG := by
    dsimp only [fourthG]
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        pow_nonneg (norm_nonneg _) 4
  have hmixed_sq : (alpha ^ 2 * (N : Real) ^ 7) ^ 2 ≤ mixed ^ 2 := by
    apply (sq_le_sq₀
      (mul_nonneg (sq_nonneg _) (pow_nonneg hN.le 7)) hmixed_nonneg).2
    exact hmixed
  have hglobal : mixed ^ 2 ≤ fourthA * fourthG := by
    simpa only [mixed, fourthA, fourthG] using prop131_global_cauchy f B sigma
  have hfourthG : alpha ^ 4 * (N : Real) ^ 7 ≤ fourthG := by
    apply le_of_mul_le_mul_left _ hN7
    calc
      (N : Real) ^ 7 * (alpha ^ 4 * (N : Real) ^ 7) =
          (alpha ^ 2 * (N : Real) ^ 7) ^ 2 := by ring
      _ ≤ mixed ^ 2 := hmixed_sq
      _ ≤ fourthA * fourthG := hglobal
      _ ≤ (N : Real) ^ 7 * fourthG :=
        mul_le_mul_of_nonneg_right hfourthA hfourthG_nonneg
  have hfourthG_eq :
      fourthG = (N : Real) ^ 4 * phiAdditiveCount B sigma := by
    simpa only [fourthG] using prop131_fourthG_eq_count B sigma
  apply le_of_mul_le_mul_left _ hN4
  calc
    (N : Real) ^ 4 * (alpha ^ 4 * (N : Real) ^ 3) =
        alpha ^ 4 * (N : Real) ^ 7 := by ring
    _ ≤ fourthG := hfourthG
    _ = (N : Real) ^ 4 * phiAdditiveCount B sigma := hfourthG_eq

private def prop132Indicator {N : Nat} (A : Finset (Pair N)) :
    Pair N → Complex :=
  fun z => if z ∈ A then 1 else 0

private lemma prop132_indicator_disc {N : Nat} (A : Finset (Pair N)) :
    DiscValued (prop132Indicator A) := by
  intro z
  classical
  simp only [prop132Indicator]
  split_ifs <;> simp

private lemma prop132_fiber_count_eq {N : Nat} [NeZero N]
    (A : Finset (Pair N)) (h x : ZMod N) :
    verticalEdgeFiberCount A h x =
      ((Finset.univ : Finset (ZMod N)).filter fun y =>
        (x, y) ∈ A ∧ (x, y + h) ∈ A).card := by
  classical
  unfold verticalEdgeFiberCount verticalEdgeDomain
  apply Finset.card_bij (fun z _ => z.2)
  · rintro ⟨zx, zy⟩ hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    rcases hz with ⟨⟨hzA, hzAh⟩, hzx⟩
    subst zx
    exact ⟨hzA, hzAh⟩
  · rintro ⟨ax, ay⟩ ha ⟨bx, byy⟩ hb hab
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    rcases ha with ⟨ha, hax⟩
    rcases hb with ⟨hb, hbx⟩
    simp only at hab
    congr
    · exact hax.trans hbx.symm
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    refine ⟨(x, y), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hy, trivial⟩

private lemma prop132_indicator_product {N : Nat} (A : Finset (Pair N))
    (h x y : ZMod N) :
    prop132Indicator A (x, y + h) * star (prop132Indicator A (x, y)) =
      if (x, y) ∈ A ∧ (x, y + h) ∈ A then 1 else 0 := by
  classical
  by_cases hy : (x, y) ∈ A <;> by_cases hyh : (x, y + h) ∈ A <;>
    simp [prop132Indicator, hy, hyh]

private lemma prop132_verticalCorrelation_eq {N : Nat} [NeZero N]
    (A : Finset (Pair N)) (h : ZMod N) :
    verticalCorrelation (prop132Indicator A) h = verticalEdgeFiberFunction A h := by
  funext x
  rw [verticalCorrelation, verticalEdgeFiberFunction, prop132_fiber_count_eq]
  simp_rw [prop132_indicator_product]
  rw [← Finset.sum_filter]
  simp

/-- Corollary 13.2 is Lemma 13.1 applied to the indicator of the given
two-dimensional set. -/
theorem corollary_13_2_holds : corollary_13_2 := by
  intro N _ A B sigma alpha hAlpha hlarge
  apply lemma_13_1_holds N (prop132Indicator A) B sigma alpha hAlpha
  · exact prop132_indicator_disc A
  · simpa only [prop132_verticalCorrelation_eq] using hlarge

end LeanProofs.GowersSzemeredi

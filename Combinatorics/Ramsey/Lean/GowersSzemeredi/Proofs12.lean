import GowersSzemeredi.Sections12_13
import GowersSzemeredi.Proofs01_03
import Mathlib.Analysis.MeanInequalities
import Mathlib.Algebra.Order.Chebyshev

/-!
# Proofs for Gowers (2001), Section 12

This module proves the weighted simultaneous-additivity estimate of
Proposition 12.1.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

@[simp] private lemma prop121_exponential_add {N : Nat} [NeZero N]
    (x y : ZMod N) : exponential (x + y) = exponential x * exponential y := by
  exact AddChar.map_add_eq_mul (ZMod.stdAddChar (N := N)) x y

@[simp] private lemma prop121_star_exponential {N : Nat} [NeZero N]
    (x : ZMod N) : star (exponential x) = exponential (-x) := by
  simpa only [exponential, starRingEnd_apply] using
    (AddChar.map_neg_eq_conj (ZMod.stdAddChar (N := N)) x).symm

private lemma prop121_coeff_sq_expansion {N : Nat} [NeZero N]
    (f : ZMod N → Complex) (k r : ZMod N) :
    ((‖fourier (difference f k) r‖ ^ 2 : Real) : Complex) =
      ∑ u : ZMod N, ∑ s : ZMod N,
        f s * star (f (s - u)) * star (f (s - k)) * f (s - k - u) *
          exponential (-(r * u)) := by
  simp only [fourier, difference, ZMod.dft_apply, smul_eq_mul]
  calc
    ((‖∑ s : ZMod N, exponential (-(s * r)) *
        (f s * star (f (s - k)))‖ ^ 2 : Real) : Complex) =
        (∑ s : ZMod N, exponential (-(s * r)) *
          (f s * star (f (s - k)))) *
        star (∑ t : ZMod N, exponential (-(t * r)) *
          (f t * star (f (t - k)))) := by
            rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow]
    _ = ∑ s : ZMod N, ∑ t : ZMod N,
          (exponential (-(s * r)) * (f s * star (f (s - k)))) *
            ((f (t - k) * star (f t)) * exponential (t * r)) := by
              simp only [star_sum, star_mul, star_star, prop121_star_exponential, neg_neg]
              simp_rw [sum_mul, mul_sum]
    _ = ∑ s : ZMod N, ∑ u : ZMod N,
          (exponential (-(s * r)) * (f s * star (f (s - k)))) *
            ((f (s - u - k) * star (f (s - u))) * exponential ((s - u) * r)) := by
              apply Finset.sum_congr rfl
              intro s _
              rw [← (Equiv.subLeft s).sum_comp]
              rfl
    _ = ∑ u : ZMod N, ∑ s : ZMod N,
          f s * star (f (s - u)) * star (f (s - k)) * f (s - k - u) *
            exponential (-(r * u)) := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro u _
              apply Finset.sum_congr rfl
              intro s _
              have hphase :
                  exponential (-(s * r)) * exponential ((s - u) * r) =
                    exponential (-(r * u)) := by
                rw [← prop121_exponential_add]
                congr 1
                ring
              rw [← hphase]
              ring

private def prop121Outer {N p : Nat} (f : Fin p → ZMod N → Complex)
    (u s : Fin p → ZMod N) : Complex :=
  ∏ i, f i (s i) * star (f i (s i - u i))

private def prop121InnerTerm {N p : Nat} [NeZero N]
    (lambda : ZMod N → Real) (f : Fin p → ZMod N → Complex)
    (phi : Fin p → ZMod N → ZMod N)
    (u s : Fin p → ZMod N) (k : ZMod N) : Complex :=
  (lambda k : Complex) * ∏ i,
    star (f i (s i - k)) * f i (s i - k - u i) *
      exponential (-(phi i k * u i))

private lemma prop121_energy_expansion {N p : Nat} [NeZero N]
    (lambda : ZMod N → Real) (f : Fin p → ZMod N → Complex)
    (phi : Fin p → ZMod N → ZMod N) :
    (((∑ k : ZMod N, lambda k *
        ∏ i : Fin p, ‖fourier (difference (f i) k) (phi i k)‖ ^ 2 : Real)) : Complex) =
      ∑ u : Fin p → ZMod N, ∑ s : Fin p → ZMod N,
        prop121Outer f u s * ∑ k : ZMod N, prop121InnerTerm lambda f phi u s k := by
  rw [Complex.ofReal_sum]
  calc
    (∑ k : ZMod N,
        ((lambda k * ∏ i : Fin p,
          ‖fourier (difference (f i) k) (phi i k)‖ ^ 2 : Real) : Complex)) =
        ∑ k : ZMod N, (lambda k : Complex) *
          ∏ i : Fin p,
            ((‖fourier (difference (f i) k) (phi i k)‖ ^ 2 : Real) : Complex) := by
              apply Finset.sum_congr rfl
              intro k _
              push_cast
              rfl
    _ = ∑ k : ZMod N, (lambda k : Complex) *
        ∏ i : Fin p, ∑ u : ZMod N, ∑ s : ZMod N,
          f i s * star (f i (s - u)) * star (f i (s - k)) *
            f i (s - k - u) * exponential (-(phi i k * u)) := by
              apply Finset.sum_congr rfl
              intro k _
              congr 1
              apply Finset.prod_congr rfl
              intro i _
              rw [prop121_coeff_sq_expansion]
    _ = ∑ k : ZMod N, (lambda k : Complex) *
        ∑ u : Fin p → ZMod N, ∑ s : Fin p → ZMod N,
          ∏ i : Fin p,
            (f i (s i) * star (f i (s i - u i)) *
              star (f i (s i - k)) * f i (s i - k - u i) *
                exponential (-(phi i k * u i))) := by
              apply Finset.sum_congr rfl
              intro k _
              congr 1
              rw [Fintype.prod_sum]
              apply Finset.sum_congr rfl
              intro u _
              rw [Fintype.prod_sum]
    _ = ∑ u : Fin p → ZMod N, ∑ s : Fin p → ZMod N,
        prop121Outer f u s * ∑ k : ZMod N, prop121InnerTerm lambda f phi u s k := by
              simp only [prop121Outer, prop121InnerTerm]
              conv_lhs =>
                enter [2, k]
                rw [Finset.mul_sum]
                enter [2, u]
                rw [Finset.mul_sum]
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro u _
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro s _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k _
              calc
                (lambda k : Complex) * ∏ i : Fin p,
                    f i (s i) * star (f i (s i - u i)) *
                      star (f i (s i - k)) * f i (s i - k - u i) *
                        exponential (-(phi i k * u i)) =
                    (lambda k : Complex) * ∏ i : Fin p,
                      ((f i (s i) * star (f i (s i - u i))) *
                        (star (f i (s i - k)) * f i (s i - k - u i) *
                          exponential (-(phi i k * u i)))) := by
                            congr 1
                            apply Finset.prod_congr rfl
                            intro i _
                            ring
                _ = (lambda k : Complex) *
                    ((∏ i : Fin p, f i (s i) * star (f i (s i - u i))) *
                      ∏ i : Fin p, star (f i (s i - k)) *
                        f i (s i - k - u i) * exponential (-(phi i k * u i))) := by
                          rw [Finset.prod_mul_distrib]
                _ = (∏ i : Fin p, f i (s i) * star (f i (s i - u i))) *
                    ((lambda k : Complex) * ∏ i : Fin p,
                      star (f i (s i - k)) * f i (s i - k - u i) *
                        exponential (-(phi i k * u i))) := by ring

private lemma prop121_outer_norm_le {N p : Nat}
    (f : Fin p → ZMod N → Complex) (hf : ∀ i, DiscValued (f i))
    (u s : Fin p → ZMod N) : ‖prop121Outer f u s‖ ≤ 1 := by
  rw [prop121Outer, norm_prod]
  apply Finset.prod_le_one
  · intro i _
    positivity
  · intro i _
    rw [norm_mul, norm_star]
    calc
      ‖f i (s i)‖ * ‖f i (s i - u i)‖ ≤ 1 * 1 := by
        gcongr <;> apply hf
      _ = 1 := one_mul 1

private lemma prop121_initial_bound {N p : Nat} [NeZero N]
    (lambda : ZMod N → Real) (f : Fin p → ZMod N → Complex)
    (phi : Fin p → ZMod N → ZMod N)
    (hlambda : ∀ k, 0 ≤ lambda k) (hf : ∀ i, DiscValued (f i)) :
    (∑ k : ZMod N, lambda k *
        ∏ i : Fin p, ‖fourier (difference (f i) k) (phi i k)‖ ^ 2) ≤
      ∑ u : Fin p → ZMod N, ∑ s : Fin p → ZMod N,
        ‖∑ k : ZMod N, prop121InnerTerm lambda f phi u s k‖ := by
  let energy : Real := ∑ k : ZMod N, lambda k *
    ∏ i : Fin p, ‖fourier (difference (f i) k) (phi i k)‖ ^ 2
  have henergy : 0 ≤ energy := by
    dsimp only [energy]
    apply Finset.sum_nonneg
    intro k _
    exact mul_nonneg (hlambda k) (Finset.prod_nonneg fun _ _ => sq_nonneg _)
  calc
    (∑ k : ZMod N, lambda k *
        ∏ i : Fin p, ‖fourier (difference (f i) k) (phi i k)‖ ^ 2) =
        ‖((energy : Real) : Complex)‖ := by
          rw [Complex.norm_real, Real.norm_of_nonneg henergy]
    _ = ‖∑ u : Fin p → ZMod N, ∑ s : Fin p → ZMod N,
          prop121Outer f u s *
            ∑ k : ZMod N, prop121InnerTerm lambda f phi u s k‖ := by
              rw [prop121_energy_expansion lambda f phi]
    _ ≤ ∑ u : Fin p → ZMod N,
        ‖∑ s : Fin p → ZMod N, prop121Outer f u s *
          ∑ k : ZMod N, prop121InnerTerm lambda f phi u s k‖ :=
            norm_sum_le _ _
    _ ≤ ∑ u : Fin p → ZMod N, ∑ s : Fin p → ZMod N,
        ‖prop121Outer f u s *
          ∑ k : ZMod N, prop121InnerTerm lambda f phi u s k‖ := by
            apply Finset.sum_le_sum
            intro u _
            exact norm_sum_le _ _
    _ ≤ ∑ u : Fin p → ZMod N, ∑ s : Fin p → ZMod N,
        ‖∑ k : ZMod N, prop121InnerTerm lambda f phi u s k‖ := by
            apply Finset.sum_le_sum
            intro u _
            apply Finset.sum_le_sum
            intro s _
            rw [norm_mul]
            exact (mul_le_of_le_one_left (norm_nonneg _)
              (prop121_outer_norm_le f hf u s))

private lemma prop121_l1_cauchy {N p : Nat} [NeZero N]
    (F : (Fin p → ZMod N) → (Fin p → ZMod N) → Real) :
    (∑ u : Fin p → ZMod N, ∑ s : Fin p → ZMod N, F u s) ^ 2 ≤
      (N : Real) ^ (2 * p) *
        ∑ u : Fin p → ZMod N, ∑ s : Fin p → ZMod N, (F u s) ^ 2 := by
  have hcard : Fintype.card (Fin p → ZMod N) = N ^ p := by simp
  calc
    (∑ u : Fin p → ZMod N, ∑ s : Fin p → ZMod N, F u s) ^ 2 ≤
        (N : Real) ^ p *
          ∑ u : Fin p → ZMod N, (∑ s : Fin p → ZMod N, F u s) ^ 2 := by
            simpa only [Finset.card_univ, hcard, Nat.cast_pow, Nat.cast_ofNat] using
              (sq_sum_le_card_mul_sum_sq
                (s := (Finset.univ : Finset (Fin p → ZMod N)))
                (f := fun u => ∑ s, F u s))
    _ ≤ (N : Real) ^ p * ∑ u : Fin p → ZMod N,
        ((N : Real) ^ p * ∑ s : Fin p → ZMod N, (F u s) ^ 2) := by
          gcongr with u
          simpa only [Finset.card_univ, hcard, Nat.cast_pow, Nat.cast_ofNat] using
            (sq_sum_le_card_mul_sum_sq
              (s := (Finset.univ : Finset (Fin p → ZMod N))) (f := F u))
    _ = (N : Real) ^ (2 * p) *
        ∑ u : Fin p → ZMod N, ∑ s : Fin p → ZMod N, (F u s) ^ 2 := by
          rw [← Finset.mul_sum]
          ring

private def prop121A {N p : Nat} (f : Fin p → ZMod N → Complex)
    (u v : Fin p → ZMod N) (x : ZMod N) : Complex :=
  ∏ i, star (f i (-v i - x)) * f i (-v i - x - u i)

private def prop121B {N p : Nat} [NeZero N] (lambda : ZMod N → Real)
    (phi : Fin p → ZMod N → ZMod N)
    (u : Fin p → ZMod N) (x : ZMod N) : Complex :=
  (lambda x : Complex) * ∏ i, exponential (phi i x * u i)

private lemma prop121_correlation_eq {N p : Nat} [NeZero N]
    (lambda : ZMod N → Real) (f : Fin p → ZMod N → Complex)
    (phi : Fin p → ZMod N → ZMod N)
    (u v : Fin p → ZMod N) (s : ZMod N) :
    correlation (prop121A f u v) (prop121B lambda phi u) (-s) =
      ∑ k : ZMod N, prop121InnerTerm lambda f phi u (fun i => s - v i) k := by
  classical
  simp only [correlation, prop121A, prop121B, prop121InnerTerm]
  rw [← (Equiv.subRight s).sum_comp]
  simp only [Equiv.subRight_apply, sub_neg_eq_add, sub_add_cancel, star_mul,
    star_prod, Complex.star_def, Complex.conj_ofReal, prop121_star_exponential]
  apply Finset.sum_congr rfl
  intro k _
  calc
    (∏ i : Fin p, star (f i (-v i - (k - s))) *
        f i (-v i - (k - s) - u i)) *
        ((∏ i : Fin p, exponential (-(phi i k * u i))) * (lambda k : Complex)) =
      (lambda k : Complex) *
        ((∏ i : Fin p, star (f i (-v i - (k - s))) *
          f i (-v i - (k - s) - u i)) *
        ∏ i : Fin p, exponential (-(phi i k * u i))) := by ring
    _ = (lambda k : Complex) * ∏ i : Fin p,
        ((star (f i (-v i - (k - s))) * f i (-v i - (k - s) - u i)) *
          exponential (-(phi i k * u i))) := by
            congr 1
            exact (Finset.prod_mul_distrib (s := (Finset.univ : Finset (Fin p)))).symm
    _ = (lambda k : Complex) * ∏ i : Fin p,
        star (f i (s - v i - k)) * f i (s - v i - k - u i) *
          exponential (-(phi i k * u i)) := by
            congr 1
            apply Finset.prod_congr rfl
            intro i _
            congr 1
            · ring

private def prop121SubEquiv {N p : Nat} (s : ZMod N) :
    (Fin p → ZMod N) ≃ (Fin p → ZMod N) where
  toFun v := fun i => s - v i
  invFun v := fun i => s - v i
  left_inv v := by
    funext i
    ring
  right_inv v := by
    funext i
    ring

private lemma prop121_shift_sum {N p : Nat} [NeZero N]
    (F : (Fin p → ZMod N) → Real) :
    (∑ s : ZMod N, ∑ v : Fin p → ZMod N, F (fun i => s - v i)) =
      (N : Real) * ∑ x : Fin p → ZMod N, F x := by
  calc
    (∑ s : ZMod N, ∑ v : Fin p → ZMod N, F (fun i => s - v i)) =
        ∑ _s : ZMod N, ∑ x : Fin p → ZMod N, F x := by
          apply Finset.sum_congr rfl
          intro s _
          exact Fintype.sum_equiv (prop121SubEquiv (p := p) s)
            (fun v => F (fun i => s - v i)) F (fun _ => rfl)
    _ = (N : Real) * ∑ x : Fin p → ZMod N, F x := by simp

private lemma prop121_mixed_eq_l2 {N p : Nat} [NeZero N]
    (lambda : ZMod N → Real) (f : Fin p → ZMod N → Complex)
    (phi : Fin p → ZMod N → ZMod N) :
    (∑ u : Fin p → ZMod N, ∑ v : Fin p → ZMod N, ∑ r : ZMod N,
        ‖fourier (prop121A f u v) r‖ ^ 2 *
          ‖fourier (prop121B lambda phi u) r‖ ^ 2) =
      (N : Real) ^ 2 *
        ∑ u : Fin p → ZMod N, ∑ x : Fin p → ZMod N,
          ‖∑ k : ZMod N, prop121InnerTerm lambda f phi u x k‖ ^ 2 := by
  calc
    _ = ∑ u : Fin p → ZMod N, ∑ v : Fin p → ZMod N,
        (N : Real) * ∑ t : ZMod N,
          ‖correlation (prop121A f u v) (prop121B lambda phi u) t‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro u _
            apply Finset.sum_congr rfl
            intro v _
            exact lemma_2_1_holds N (prop121A f u v) (prop121B lambda phi u)
    _ = (N : Real) * ∑ u : Fin p → ZMod N, ∑ s : ZMod N,
        ∑ v : Fin p → ZMod N,
          ‖∑ k : ZMod N,
            prop121InnerTerm lambda f phi u (fun i => s - v i) k‖ ^ 2 := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro u _
              rw [← Finset.mul_sum]
              congr 1
              calc
                (∑ v : Fin p → ZMod N, ∑ t : ZMod N,
                    ‖correlation (prop121A f u v) (prop121B lambda phi u) t‖ ^ 2) =
                    ∑ v : Fin p → ZMod N, ∑ s : ZMod N,
                      ‖correlation (prop121A f u v)
                        (prop121B lambda phi u) (-s)‖ ^ 2 := by
                          apply Finset.sum_congr rfl
                          intro v _
                          symm
                          exact Fintype.sum_equiv (Equiv.neg (ZMod N)) _ _
                            (fun _ => rfl)
                _ = ∑ s : ZMod N, ∑ v : Fin p → ZMod N,
                    ‖∑ k : ZMod N,
                      prop121InnerTerm lambda f phi u (fun i => s - v i) k‖ ^ 2 := by
                        rw [Finset.sum_comm]
                        apply Finset.sum_congr rfl
                        intro s _
                        apply Finset.sum_congr rfl
                        intro v _
                        rw [prop121_correlation_eq]
    _ = (N : Real) * ∑ u : Fin p → ZMod N,
        ((N : Real) * ∑ x : Fin p → ZMod N,
          ‖∑ k : ZMod N, prop121InnerTerm lambda f phi u x k‖ ^ 2) := by
            congr 1
            apply Finset.sum_congr rfl
            intro u _
            exact prop121_shift_sum (N := N) (p := p)
              (fun x => ‖∑ k : ZMod N, prop121InnerTerm lambda f phi u x k‖ ^ 2)
    _ = (N : Real) ^ 2 *
        ∑ u : Fin p → ZMod N, ∑ x : Fin p → ZMod N,
          ‖∑ k : ZMod N, prop121InnerTerm lambda f phi u x k‖ ^ 2 := by
            rw [← Finset.mul_sum]
            ring

private lemma prop121_fourth_moment_le {N : Nat} [NeZero N]
    (h : ZMod N → Complex) (hh : DiscValued h) :
    ∑ r : ZMod N, ‖fourier h r‖ ^ 4 ≤ (N : Real) ^ 4 := by
  have hcorr (t : ZMod N) : ‖correlation h h t‖ ≤ (N : Real) := by
    calc
      ‖correlation h h t‖ ≤ ∑ s : ZMod N, ‖h s * star (h (s - t))‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _s : ZMod N, (1 : Real) := by
        apply Finset.sum_le_sum
        intro s _
        rw [norm_mul, norm_star]
        calc
          ‖h s‖ * ‖h (s - t)‖ ≤ 1 * 1 := by gcongr <;> apply hh
          _ = 1 := one_mul 1
      _ = (N : Real) := by simp
  have hid :
      (∑ r : ZMod N, ‖fourier h r‖ ^ 4) =
        (N : Real) * ∑ t : ZMod N, ‖correlation h h t‖ ^ 2 := by
    calc
      _ = ∑ r : ZMod N, ‖fourier h r‖ ^ 2 * ‖fourier h r‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro r _
        ring
      _ = _ := by simpa [correlation] using lemma_2_1_holds N h h
  rw [hid]
  calc
    (N : Real) * ∑ t : ZMod N, ‖correlation h h t‖ ^ 2 ≤
        (N : Real) * ∑ _t : ZMod N, (N : Real) ^ 2 := by
          gcongr with t
          exact hcorr t
    _ = (N : Real) ^ 4 := by simp; ring

private lemma prop121A_disc {N p : Nat}
    (f : Fin p → ZMod N → Complex) (hf : ∀ i, DiscValued (f i))
    (u v : Fin p → ZMod N) : DiscValued (prop121A f u v) := by
  intro x
  rw [prop121A, norm_prod]
  apply Finset.prod_le_one
  · intro i _
    positivity
  · intro i _
    rw [norm_mul, norm_star]
    calc
      ‖f i (-v i - x)‖ * ‖f i (-v i - x - u i)‖ ≤ 1 * 1 := by
        gcongr <;> apply hf
      _ = 1 := one_mul 1

private lemma prop121_fourthA_le {N p : Nat} [NeZero N]
    (f : Fin p → ZMod N → Complex) (hf : ∀ i, DiscValued (f i)) :
    (∑ u : Fin p → ZMod N, ∑ v : Fin p → ZMod N, ∑ r : ZMod N,
      ‖fourier (prop121A f u v) r‖ ^ 4) ≤ (N : Real) ^ (2 * p + 4) := by
  have hcard : Fintype.card (Fin p → ZMod N) = N ^ p := by simp
  calc
    _ ≤ ∑ _u : Fin p → ZMod N, ∑ _v : Fin p → ZMod N,
        (N : Real) ^ 4 := by
          apply Finset.sum_le_sum
          intro u _
          apply Finset.sum_le_sum
          intro v _
          exact prop121_fourth_moment_le (prop121A f u v) (prop121A_disc f hf u v)
    _ = (N : Real) ^ (2 * p + 4) := by
          simp only [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
          push_cast
          ring

private lemma prop121_global_cauchy {N p : Nat} [NeZero N]
    (lambda : ZMod N → Real) (f : Fin p → ZMod N → Complex)
    (phi : Fin p → ZMod N → ZMod N) :
    (∑ u : Fin p → ZMod N, ∑ v : Fin p → ZMod N, ∑ r : ZMod N,
        ‖fourier (prop121A f u v) r‖ ^ 2 *
          ‖fourier (prop121B lambda phi u) r‖ ^ 2) ^ 2 ≤
      (∑ u : Fin p → ZMod N, ∑ v : Fin p → ZMod N, ∑ r : ZMod N,
        ‖fourier (prop121A f u v) r‖ ^ 4) *
      ∑ u : Fin p → ZMod N, ∑ _v : Fin p → ZMod N, ∑ r : ZMod N,
        ‖fourier (prop121B lambda phi u) r‖ ^ 4 := by
  let U := Fin p → ZMod N
  have h := Finset.sum_mul_sq_le_sq_mul_sq
    (((Finset.univ : Finset U) ×ˢ (Finset.univ : Finset U)) ×ˢ
      (Finset.univ : Finset (ZMod N)))
    (fun z => ‖fourier (prop121A f z.1.1 z.1.2) z.2‖ ^ 2)
    (fun z => ‖fourier (prop121B lambda phi z.1.1) z.2‖ ^ 2)
  simpa only [Finset.sum_product, ← pow_mul] using h

private lemma prop121_sum_exponential_mul {N : Nat} [NeZero N] (x : ZMod N) :
    ∑ u : ZMod N, exponential (x * u) = if x = 0 then (N : Complex) else 0 := by
  simpa [exponential, mul_comm] using
    AddChar.sum_mulShift x (ZMod.isPrimitive_stdAddChar N)

private lemma prop121_vector_orthogonality {N p : Nat} [NeZero N]
    (x : Fin p → ZMod N) :
    (∑ u : Fin p → ZMod N, ∏ i, exponential (x i * u i)) =
      if ∀ i, x i = 0 then ((N : Nat) ^ p : Complex) else 0 := by
  calc
    (∑ u : Fin p → ZMod N, ∏ i, exponential (x i * u i)) =
        ∏ i : Fin p, ∑ a : ZMod N, exponential (x i * a) := by
          exact (Fintype.prod_sum (fun i (a : ZMod N) => exponential (x i * a))).symm
    _ = ∏ i : Fin p, if x i = 0 then (N : Complex) else 0 := by
          apply Finset.prod_congr rfl
          intro i _
          rw [prop121_sum_exponential_mul]
    _ = if ∀ i, x i = 0 then ((N : Nat) ^ p : Complex) else 0 := by
          by_cases h : ∀ i, x i = 0
          · rw [if_pos h]
            simp only [h, if_true, Finset.prod_const, Finset.card_univ]
            rw [Fintype.card_fin]
          · rw [if_neg h, Finset.prod_eq_zero_iff]
            push Not at h
            obtain ⟨i, hi⟩ := h
            exact ⟨i, Finset.mem_univ i, if_neg hi⟩

private lemma prop121_prod_four {p : Nat} (a b c d : Fin p → Complex) :
    (∏ i, a i) * (∏ i, b i) * (∏ i, c i) * (∏ i, d i) =
      ∏ i, a i * b i * c i * d i := by
  symm
  simp only [Finset.prod_mul_distrib]

private lemma prop121_b_product {N p : Nat} [NeZero N]
    (lambda : ZMod N → Real) (phi : Fin p → ZMod N → ZMod N)
    (q : Fin 4 → ZMod N) (u : Fin p → ZMod N) :
    prop121B lambda phi u (q 0) *
        star (prop121B lambda phi u (q 1) * prop121B lambda phi u (q 2)) *
        prop121B lambda phi u (q 3) =
      ((lambda (q 0) * lambda (q 1) * lambda (q 2) * lambda (q 3) : Real) : Complex) *
        ∏ i, exponential
          ((phi i (q 0) - phi i (q 1) - phi i (q 2) + phi i (q 3)) * u i) := by
  simp only [prop121B, star_mul, star_prod, Complex.star_def, Complex.conj_ofReal,
    prop121_star_exponential]
  push_cast
  have hphase :
      (∏ i : Fin p, exponential (phi i (q 0) * u i)) *
          (∏ i : Fin p, exponential (-(phi i (q 2) * u i))) *
          (∏ i : Fin p, exponential (-(phi i (q 1) * u i))) *
          (∏ i : Fin p, exponential (phi i (q 3) * u i)) =
        ∏ i : Fin p, exponential
          ((phi i (q 0) - phi i (q 1) - phi i (q 2) + phi i (q 3)) * u i) := by
    rw [prop121_prod_four]
    apply Finset.prod_congr rfl
    intro i _
    rw [← prop121_exponential_add, ← prop121_exponential_add,
      ← prop121_exponential_add]
    congr 1
    ring
  calc
    ((lambda (q 0) : Complex) * ∏ i, exponential (phi i (q 0) * u i)) *
          ((∏ i, exponential (-(phi i (q 2) * u i))) * (lambda (q 2) : Complex) *
            ((∏ i, exponential (-(phi i (q 1) * u i))) * (lambda (q 1) : Complex))) *
        ((lambda (q 3) : Complex) * ∏ i, exponential (phi i (q 3) * u i)) =
      (lambda (q 0) : Complex) * lambda (q 1) * lambda (q 2) * lambda (q 3) *
        (((∏ i, exponential (phi i (q 0) * u i)) *
          (∏ i, exponential (-(phi i (q 2) * u i))) *
          (∏ i, exponential (-(phi i (q 1) * u i))) *
          ∏ i, exponential (phi i (q 3) * u i))) := by ring
    _ = (lambda (q 0) : Complex) * lambda (q 1) * lambda (q 2) * lambda (q 3) *
        ∏ i, exponential
          ((phi i (q 0) - phi i (q 1) - phi i (q 2) + phi i (q 3)) * u i) := by
            rw [hphase]

private lemma prop121_sum_b_product {N p : Nat} [NeZero N]
    (lambda : ZMod N → Real) (phi : Fin p → ZMod N → ZMod N)
    (q : Fin 4 → ZMod N) :
    (∑ u : Fin p → ZMod N,
      prop121B lambda phi u (q 0) *
        star (prop121B lambda phi u (q 1) * prop121B lambda phi u (q 2)) *
        prop121B lambda phi u (q 3)) =
      if (∀ i, phi i (q 0) - phi i (q 1) = phi i (q 2) - phi i (q 3)) then
        (((N : Real) ^ p *
          (lambda (q 0) * lambda (q 1) * lambda (q 2) * lambda (q 3)) : Real) : Complex)
      else 0 := by
  simp_rw [prop121_b_product]
  rw [← Finset.mul_sum, prop121_vector_orthogonality]
  by_cases h : ∀ i, phi i (q 0) - phi i (q 1) = phi i (q 2) - phi i (q 3)
  · have hz : ∀ i,
        phi i (q 0) - phi i (q 1) - phi i (q 2) + phi i (q 3) = 0 := by
      intro i
      calc
        phi i (q 0) - phi i (q 1) - phi i (q 2) + phi i (q 3) =
            (phi i (q 0) - phi i (q 1)) -
              (phi i (q 2) - phi i (q 3)) := by abel
        _ = 0 := sub_eq_zero.mpr (h i)
    rw [if_pos hz, if_pos h]
    push_cast
    ring
  · have hnz : ¬ ∀ i,
        phi i (q 0) - phi i (q 1) - phi i (q 2) + phi i (q 3) = 0 := by
      intro hz
      apply h
      intro i
      have hi := hz i
      apply sub_eq_zero.mp
      calc
        (phi i (q 0) - phi i (q 1)) - (phi i (q 2) - phi i (q 3)) =
            phi i (q 0) - phi i (q 1) - phi i (q 2) + phi i (q 3) := by abel
        _ = 0 := hi
    rw [if_neg hnz, if_neg h]
    simp

private lemma prop121_fourthB_eq_weight {N p : Nat} [NeZero N]
    (lambda : ZMod N → Real) (phi : Fin p → ZMod N → ZMod N) :
    (∑ u : Fin p → ZMod N, ∑ r : ZMod N,
        ‖fourier (prop121B lambda phi u) r‖ ^ 4) =
      (N : Real) ^ (p + 1) * simultaneouslyAdditiveWeight lambda phi := by
  classical
  have hcomplex :
      (((∑ u : Fin p → ZMod N, ∑ r : ZMod N,
          ‖fourier (prop121B lambda phi u) r‖ ^ 4 : Real)) : Complex) =
        (((N : Real) ^ (p + 1) *
          simultaneouslyAdditiveWeight lambda phi : Real) : Complex) := by
    rw [Complex.ofReal_sum]
    calc
      (∑ u : Fin p → ZMod N,
          ((∑ r : ZMod N,
            ‖fourier (prop121B lambda phi u) r‖ ^ 4 : Real) : Complex)) =
          ∑ u : Fin p → ZMod N, (N : Complex) *
            ∑ q : Fin 4 → ZMod N,
              if q 0 - q 1 = q 2 - q 3 then
                prop121B lambda phi u (q 0) *
                  star (prop121B lambda phi u (q 1) *
                    prop121B lambda phi u (q 2)) *
                  prop121B lambda phi u (q 3)
              else 0 := by
                apply Finset.sum_congr rfl
                intro u _
                exact identity_2_6_holds N (prop121B lambda phi u)
      _ = (N : Complex) * ∑ q : Fin 4 → ZMod N,
          if q 0 - q 1 = q 2 - q 3 then
            ∑ u : Fin p → ZMod N,
              prop121B lambda phi u (q 0) *
                star (prop121B lambda phi u (q 1) *
                  prop121B lambda phi u (q 2)) *
                prop121B lambda phi u (q 3)
          else 0 := by
            rw [← Finset.mul_sum]
            congr 1
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro q _
            by_cases hadd : q 0 - q 1 = q 2 - q 3 <;> simp [hadd]
      _ = (N : Complex) * ∑ q : Fin 4 → ZMod N,
          if IsSimultaneouslyAdditive phi q then
            (((N : Real) ^ p *
              (lambda (q 0) * lambda (q 1) * lambda (q 2) *
                lambda (q 3)) : Real) : Complex)
          else 0 := by
            congr 1
            apply Finset.sum_congr rfl
            intro q _
            rw [prop121_sum_b_product]
            by_cases hadd : q 0 - q 1 = q 2 - q 3 <;>
              by_cases hphi : ∀ i,
                phi i (q 0) - phi i (q 1) = phi i (q 2) - phi i (q 3) <;>
              simp [IsSimultaneouslyAdditive, hadd, hphi]
      _ = (N : Complex) * ((N : Complex) ^ p *
          ∑ q : Fin 4 → ZMod N,
            if IsSimultaneouslyAdditive phi q then
              ((lambda (q 0) * lambda (q 1) * lambda (q 2) *
                lambda (q 3) : Real) : Complex)
            else 0) := by
              congr 1
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro q _
              by_cases hq : IsSimultaneouslyAdditive phi q
              · rw [if_pos hq, if_pos hq]
                push_cast
                rfl
              · rw [if_neg hq, if_neg hq]
                simp
      _ = (((N : Real) ^ (p + 1) *
          simultaneouslyAdditiveWeight lambda phi : Real) : Complex) := by
            unfold simultaneouslyAdditiveWeight
            rw [show
              (∑ q : Fin 4 → ZMod N,
                if IsSimultaneouslyAdditive phi q then
                  ((lambda (q 0) * lambda (q 1) * lambda (q 2) *
                    lambda (q 3) : Real) : Complex)
                else 0) =
              (((∑ q : Fin 4 → ZMod N,
                if IsSimultaneouslyAdditive phi q then
                  lambda (q 0) * lambda (q 1) * lambda (q 2) * lambda (q 3)
                else 0 : Real)) : Complex) by
                  rw [Complex.ofReal_sum]
                  apply Finset.sum_congr rfl
                  intro q _
                  by_cases hq : IsSimultaneouslyAdditive phi q <;> simp [hq]]
            push_cast
            ring
  exact Complex.ofReal_injective hcomplex

private lemma prop121_fourthB_with_v {N p : Nat} [NeZero N]
    (lambda : ZMod N → Real) (phi : Fin p → ZMod N → ZMod N) :
    (∑ u : Fin p → ZMod N, ∑ _v : Fin p → ZMod N, ∑ r : ZMod N,
        ‖fourier (prop121B lambda phi u) r‖ ^ 4) =
      (N : Real) ^ p *
        ∑ u : Fin p → ZMod N, ∑ r : ZMod N,
          ‖fourier (prop121B lambda phi u) r‖ ^ 4 := by
  have hcard : Fintype.card (Fin p → ZMod N) = N ^ p := by simp
  simp only [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
  push_cast
  rw [← Finset.mul_sum]

/-- Proposition 12.1 follows by introducing a common scalar shift, applying
Cauchy--Schwarz twice, and then using character orthogonality in every member
of the `Fin p` family. -/
theorem proposition_12_1_holds : proposition_12_1 := by
  intro N p _ lambda f phi alpha hAlpha hlambda hf hlarge
  let L1 : Real := ∑ u : Fin p → ZMod N, ∑ s : Fin p → ZMod N,
    ‖∑ k : ZMod N, prop121InnerTerm lambda f phi u s k‖
  let L2 : Real := ∑ u : Fin p → ZMod N, ∑ s : Fin p → ZMod N,
    ‖∑ k : ZMod N, prop121InnerTerm lambda f phi u s k‖ ^ 2
  let mixed : Real :=
    ∑ u : Fin p → ZMod N, ∑ v : Fin p → ZMod N, ∑ r : ZMod N,
      ‖fourier (prop121A f u v) r‖ ^ 2 *
        ‖fourier (prop121B lambda phi u) r‖ ^ 2
  let fourthA : Real :=
    ∑ u : Fin p → ZMod N, ∑ v : Fin p → ZMod N, ∑ r : ZMod N,
      ‖fourier (prop121A f u v) r‖ ^ 4
  let fourthBuv : Real :=
    ∑ u : Fin p → ZMod N, ∑ v : Fin p → ZMod N, ∑ r : ZMod N,
      ‖fourier (prop121B lambda phi u) r‖ ^ 4
  let fourthB : Real :=
    ∑ u : Fin p → ZMod N, ∑ r : ZMod N,
      ‖fourier (prop121B lambda phi u) r‖ ^ 4
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hN2p : (0 : Real) < (N : Real) ^ (2 * p) := by positivity
  have hN2p4 : (0 : Real) < (N : Real) ^ (2 * p + 4) := by positivity
  have hN2p1 : (0 : Real) < (N : Real) ^ (2 * p + 1) := by positivity
  have hL1 : alpha * (N : Real) ^ (2 * p + 1) ≤ L1 := hlarge.trans <| by
    simpa only [L1] using prop121_initial_bound lambda f phi hlambda hf
  have hL1_nonneg : 0 ≤ L1 := by
    dsimp only [L1]
    positivity
  have hbase_nonneg : 0 ≤ alpha * (N : Real) ^ (2 * p + 1) :=
    mul_nonneg hAlpha.le (by positivity)
  have hL1sq :
      (alpha * (N : Real) ^ (2 * p + 1)) ^ 2 ≤ L1 ^ 2 :=
    (sq_le_sq₀ hbase_nonneg hL1_nonneg).2 hL1
  have hCauchy1 : L1 ^ 2 ≤ (N : Real) ^ (2 * p) * L2 := by
    simpa only [L1, L2] using
      (prop121_l1_cauchy (N := N) (p := p)
        (fun u s =>
          ‖∑ k : ZMod N, prop121InnerTerm lambda f phi u s k‖))
  have hL2 : alpha ^ 2 * (N : Real) ^ (2 * p + 2) ≤ L2 := by
    apply le_of_mul_le_mul_left _ hN2p
    calc
      (N : Real) ^ (2 * p) *
          (alpha ^ 2 * (N : Real) ^ (2 * p + 2)) =
          (alpha * (N : Real) ^ (2 * p + 1)) ^ 2 := by
            rw [show 2 * p + 2 = 2 * p + 1 + 1 by omega,
              pow_add, pow_succ]
            ring
      _ ≤ L1 ^ 2 := hL1sq
      _ ≤ (N : Real) ^ (2 * p) * L2 := hCauchy1
  have hmixed_eq : mixed = (N : Real) ^ 2 * L2 := by
    simpa only [mixed, L2] using prop121_mixed_eq_l2 lambda f phi
  have hmixed : alpha ^ 2 * (N : Real) ^ (2 * p + 4) ≤ mixed := by
    calc
      alpha ^ 2 * (N : Real) ^ (2 * p + 4) =
          (N : Real) ^ 2 *
            (alpha ^ 2 * (N : Real) ^ (2 * p + 2)) := by
              rw [show 2 * p + 4 = 2 + (2 * p + 2) by omega, pow_add]
              ring
      _ ≤ (N : Real) ^ 2 * L2 :=
        mul_le_mul_of_nonneg_left hL2 (by positivity)
      _ = mixed := hmixed_eq.symm
  have hfourthA : fourthA ≤ (N : Real) ^ (2 * p + 4) := by
    simpa only [fourthA] using prop121_fourthA_le f hf
  have hmixed_nonneg : 0 ≤ mixed := by
    dsimp only [mixed]
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hfourthBuv_nonneg : 0 ≤ fourthBuv := by
    dsimp only [fourthBuv]
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => pow_nonneg (norm_nonneg _) 4
  have hmixed_sq :
      (alpha ^ 2 * (N : Real) ^ (2 * p + 4)) ^ 2 ≤ mixed ^ 2 := by
    apply (sq_le_sq₀
      (mul_nonneg (sq_nonneg _) (pow_nonneg hN.le _)) hmixed_nonneg).2
    exact hmixed
  have hglobal : mixed ^ 2 ≤ fourthA * fourthBuv := by
    simpa only [mixed, fourthA, fourthBuv] using
      prop121_global_cauchy lambda f phi
  have hfourthBuv :
      alpha ^ 4 * (N : Real) ^ (2 * p + 4) ≤ fourthBuv := by
    apply le_of_mul_le_mul_left _ hN2p4
    calc
      (N : Real) ^ (2 * p + 4) *
          (alpha ^ 4 * (N : Real) ^ (2 * p + 4)) =
          (alpha ^ 2 * (N : Real) ^ (2 * p + 4)) ^ 2 := by ring
      _ ≤ mixed ^ 2 := hmixed_sq
      _ ≤ fourthA * fourthBuv := hglobal
      _ ≤ (N : Real) ^ (2 * p + 4) * fourthBuv :=
        mul_le_mul_of_nonneg_right hfourthA hfourthBuv_nonneg
  have hfourthBuv_eq :
      fourthBuv = (N : Real) ^ (2 * p + 1) *
        simultaneouslyAdditiveWeight lambda phi := by
    calc
      fourthBuv = (N : Real) ^ p * fourthB := by
        simpa only [fourthBuv, fourthB] using prop121_fourthB_with_v lambda phi
      _ = (N : Real) ^ p *
          ((N : Real) ^ (p + 1) * simultaneouslyAdditiveWeight lambda phi) := by
            rw [show fourthB = (N : Real) ^ (p + 1) *
              simultaneouslyAdditiveWeight lambda phi by
                simpa only [fourthB] using prop121_fourthB_eq_weight lambda phi]
      _ = (N : Real) ^ (2 * p + 1) *
          simultaneouslyAdditiveWeight lambda phi := by
            calc
              (N : Real) ^ p *
                  ((N : Real) ^ (p + 1) *
                    simultaneouslyAdditiveWeight lambda phi) =
                  (N : Real) ^ (p + (p + 1)) *
                    simultaneouslyAdditiveWeight lambda phi := by
                      rw [pow_add]
                      ring
              _ = _ := by rw [show p + (p + 1) = 2 * p + 1 by omega]
  apply le_of_mul_le_mul_left _ hN2p1
  calc
    (N : Real) ^ (2 * p + 1) * (alpha ^ 4 * (N : Real) ^ 3) =
        alpha ^ 4 * (N : Real) ^ (2 * p + 4) := by
          calc
            _ = alpha ^ 4 * (N : Real) ^ ((2 * p + 1) + 3) := by
              rw [pow_add]
              ring
            _ = _ := by rw [show (2 * p + 1) + 3 = 2 * p + 4 by omega]
    _ ≤ fourthBuv := hfourthBuv
    _ = (N : Real) ^ (2 * p + 1) *
        simultaneouslyAdditiveWeight lambda phi := hfourthBuv_eq

end LeanProofs.GowersSzemeredi

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

attribute [simp] exponential_add

attribute [simp] star_exponential

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
              simp only [star_sum, star_mul, star_star, star_exponential, neg_neg]
              simp_rw [sum_mul, mul_sum]
    _ = ∑ s : ZMod N, ∑ u : ZMod N,
          (exponential (-(s * r)) * (f s * star (f (s - k)))) *
            ((f (s - u - k) * star (f (s - u))) * exponential ((s - u) * r)) := by
              refine Finset.sum_congr rfl fun s _ => ?_
              rw [← (Equiv.subLeft s).sum_comp]
              rfl
    _ = ∑ u : ZMod N, ∑ s : ZMod N,
          f s * star (f (s - u)) * star (f (s - k)) * f (s - k - u) *
            exponential (-(r * u)) := by
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun s _ => ?_
              have hphase :
                  exponential (-(s * r)) * exponential ((s - u) * r) =
                    exponential (-(r * u)) := by
                rw [← exponential_add]
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
  simp_rw [Complex.ofReal_mul, Complex.ofReal_prod, prop121_coeff_sq_expansion, Fintype.prod_sum,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [prop121Outer, prop121InnerTerm]
  rw [mul_left_comm, ← Finset.prod_mul_distrib]
  exact congrArg _ (Finset.prod_congr rfl fun i _ => by ring)

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
            gcongr with u _ s _
            rw [norm_mul]
            exact (mul_le_of_le_one_left (norm_nonneg _)
              (prop121_outer_norm_le f hf u s))

private lemma prop121_l1_cauchy {N p : Nat} [NeZero N]
    (F : (Fin p → ZMod N) → (Fin p → ZMod N) → Real) :
    (∑ u : Fin p → ZMod N, ∑ s : Fin p → ZMod N, F u s) ^ 2 ≤
      (N : Real) ^ (2 * p) *
        ∑ u : Fin p → ZMod N, ∑ s : Fin p → ZMod N, (F u s) ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset ((Fin p → ZMod N) × (Fin p → ZMod N)))) (f := fun q => F q.1 q.2)
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, ZMod.card,
    Fintype.sum_prod_type] at h
  calc _ ≤ _ := h
    _ = _ := by push_cast; ring

private def prop121A {N p : Nat} (f : Fin p → ZMod N → Complex)
    (u v : Fin p → ZMod N) (x : ZMod N) : Complex :=
  ∏ i, star (f i (-v i - x)) * f i (-v i - x - u i)

def prop121B {N p : Nat} [NeZero N] (lambda : ZMod N → Real)
    (phi : Fin p → ZMod N → ZMod N)
    (u : Fin p → ZMod N) (x : ZMod N) : Complex :=
  (lambda x : Complex) * ∏ i, exponential (phi i x * u i)

private lemma prop121_correlation_eq {N p : Nat} [NeZero N]
    (lambda : ZMod N → Real) (f : Fin p → ZMod N → Complex)
    (phi : Fin p → ZMod N → ZMod N)
    (u v : Fin p → ZMod N) (s : ZMod N) :
    correlation (prop121A f u v) (prop121B lambda phi u) (-s) =
      ∑ k : ZMod N, prop121InnerTerm lambda f phi u (fun i => s - v i) k := by
  simp only [correlation, prop121A, prop121B, prop121InnerTerm]
  rw [← (Equiv.subRight s).sum_comp]
  simp only [Equiv.subRight_apply, sub_neg_eq_add, sub_add_cancel, star_mul,
    star_prod, Complex.star_def, Complex.conj_ofReal, star_exponential]
  refine Finset.sum_congr rfl fun k _ => ?_
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
            refine Finset.prod_congr rfl fun i _ => ?_
            congr 1
            · ring

private lemma prop121_shift_sum {N p : Nat} [NeZero N]
    (F : (Fin p → ZMod N) → Real) :
    (∑ s : ZMod N, ∑ v : Fin p → ZMod N, F (fun i => s - v i)) =
      (N : Real) * ∑ x : Fin p → ZMod N, F x := by
  calc
    (∑ s : ZMod N, ∑ v : Fin p → ZMod N, F (fun i => s - v i)) =
        ∑ _s : ZMod N, ∑ x : Fin p → ZMod N, F x := by
          refine Finset.sum_congr rfl fun s _ => ?_
          exact Fintype.sum_equiv
              ({ toFun v := fun i => s - v i
                 invFun v := fun i => s - v i
                 left_inv v := by norm_num
                 right_inv v := by
                   funext i
                   ring } : (Fin p → ZMod N) ≃ (Fin p → ZMod N))
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
          ‖correlation (prop121A f u v) (prop121B lambda phi u) t‖ ^ 2 :=
      Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => lemma_2_1_holds N _ _
    _ = (N : Real) * ∑ u : Fin p → ZMod N, ∑ s : ZMod N,
        ∑ v : Fin p → ZMod N,
          ‖∑ k : ZMod N,
            prop121InnerTerm lambda f phi u (fun i => s - v i) k‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [← Finset.mul_sum]
      congr 1
      calc
        _ = ∑ v : Fin p → ZMod N, ∑ s : ZMod N,
              ‖correlation (prop121A f u v) (prop121B lambda phi u) (-s)‖ ^ 2 :=
          Finset.sum_congr rfl fun v _ =>
            (Fintype.sum_equiv (Equiv.neg (ZMod N)) _ _ fun _ => rfl).symm
        _ = _ := by
          rw [Finset.sum_comm]
          simp_rw [prop121_correlation_eq]
    _ = (N : Real) * ∑ u : Fin p → ZMod N,
        ((N : Real) * ∑ x : Fin p → ZMod N,
          ‖∑ k : ZMod N, prop121InnerTerm lambda f phi u x k‖ ^ 2) := by
      congr 1
      exact Finset.sum_congr rfl fun u _ => prop121_shift_sum (N := N) (p := p)
        (fun x => ‖∑ k : ZMod N, prop121InnerTerm lambda f phi u x k‖ ^ 2)
    _ = (N : Real) ^ 2 *
        ∑ u : Fin p → ZMod N, ∑ x : Fin p → ZMod N,
          ‖∑ k : ZMod N, prop121InnerTerm lambda f phi u x k‖ ^ 2 := by
      rw [← Finset.mul_sum]
      ring

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
          gcongr with u _ v _
          exact fourier_fourth_moment_le (prop121A f u v) (prop121A_disc f hf u v)
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

alias prop121_sum_exponential_mul := fejer_sum_exponential_mul

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
    star_exponential]
  push_cast
  have hphase :
      (∏ i : Fin p, exponential (phi i (q 0) * u i)) *
          (∏ i : Fin p, exponential (-(phi i (q 2) * u i))) *
          (∏ i : Fin p, exponential (-(phi i (q 1) * u i))) *
          (∏ i : Fin p, exponential (phi i (q 3) * u i)) =
        ∏ i : Fin p, exponential
          ((phi i (q 0) - phi i (q 1) - phi i (q 2) + phi i (q 3)) * u i) := by
    rw [prop141_prod_four]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← exponential_add, ← exponential_add,
      ← exponential_add]
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

lemma prop121_fourthB_eq_weight {N p : Nat} [NeZero N]
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
                refine Finset.sum_congr rfl fun u _ => ?_
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
            refine Finset.sum_congr rfl fun q _ => ?_
            by_cases hadd : q 0 - q 1 = q 2 - q 3 <;> simp [hadd]
      _ = (N : Complex) * ∑ q : Fin 4 → ZMod N,
          if IsSimultaneouslyAdditive phi q then
            (((N : Real) ^ p *
              (lambda (q 0) * lambda (q 1) * lambda (q 2) *
                lambda (q 3)) : Real) : Complex)
          else 0 := by
            congr 1
            refine Finset.sum_congr rfl fun q _ => ?_
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
              refine Finset.sum_congr rfl fun q _ => ?_
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
                  refine Finset.sum_congr rfl fun q _ => ?_
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
  have hL1_nonneg : 0 ≤ L1 := by positivity
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
          (alpha * (N : Real) ^ (2 * p + 1)) ^ 2 := by ring
      _ ≤ L1 ^ 2 := hL1sq
      _ ≤ (N : Real) ^ (2 * p) * L2 := hCauchy1
  have hmixed_eq : mixed = (N : Real) ^ 2 * L2 := by
    simpa only [mixed, L2] using prop121_mixed_eq_l2 lambda f phi
  have hmixed : alpha ^ 2 * (N : Real) ^ (2 * p + 4) ≤ mixed := by
    calc
      alpha ^ 2 * (N : Real) ^ (2 * p + 4) =
          (N : Real) ^ 2 *
            (alpha ^ 2 * (N : Real) ^ (2 * p + 2)) := by ring
      _ ≤ (N : Real) ^ 2 * L2 :=
        mul_le_mul_of_nonneg_left hL2 (by positivity)
      _ = mixed := hmixed_eq.symm
  have hfourthA : fourthA ≤ (N : Real) ^ (2 * p + 4) := by
    simpa only [fourthA] using prop121_fourthA_le f hf
  have hmixed_nonneg : 0 ≤ mixed := by positivity
  have hfourthBuv_nonneg : 0 ≤ fourthBuv := by positivity
  have hmixed_sq :
      (alpha ^ 2 * (N : Real) ^ (2 * p + 4)) ^ 2 ≤ mixed ^ 2 := by gcongr
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
                    simultaneouslyAdditiveWeight lambda phi := by ring
              _ = _ := by rw [show p + (p + 1) = 2 * p + 1 by omega]
  apply le_of_mul_le_mul_left _ hN2p1
  calc
    (N : Real) ^ (2 * p + 1) * (alpha ^ 4 * (N : Real) ^ 3) =
        alpha ^ 4 * (N : Real) ^ (2 * p + 4) := by
          calc
            _ = alpha ^ 4 * (N : Real) ^ ((2 * p + 1) + 3) := by ring
            _ = _ := by rw [show (2 * p + 1) + 3 = 2 * p + 4 by omega]
    _ ≤ fourthBuv := hfourthBuv
    _ = (N : Real) ^ (2 * p + 1) *
        simultaneouslyAdditiveWeight lambda phi := hfourthBuv_eq

end LeanProofs.GowersSzemeredi

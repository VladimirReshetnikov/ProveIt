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
  have hF (g : ZMod N → Complex) :
      fourier g r = ∑ s : ZMod N, exponential (-(s * r)) * g s := ZMod.dft_apply g r
  -- `‖ĝ r‖² = ĝ r * star (ĝ r)` is a double sum over `(s, t)`; substitute `t = s - u`
  rw [Complex.ofReal_pow, ← Complex.mul_conj', ← Complex.star_def, Finset.sum_comm, hF,
    star_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← (Equiv.subLeft s).sum_comp]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [show -(r * u) = -(s * r) + (s - u) * r by ring, exponential_add]
  simp only [difference, Equiv.subLeft_apply, star_mul, star_star, star_exponential, neg_neg,
    show s - u - k = s - k - u by ring]
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
  have henergy : 0 ≤ ∑ k : ZMod N, lambda k *
      ∏ i : Fin p, ‖fourier (difference (f i) k) (phi i k)‖ ^ 2 :=
    Finset.sum_nonneg fun k _ => mul_nonneg (hlambda k) (Finset.prod_nonneg fun _ _ => sq_nonneg _)
  rw [← Real.norm_of_nonneg henergy, ← Complex.norm_real, prop121_energy_expansion lambda f phi]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun u _ => (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun s _ => ?_))
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (prop121_outer_norm_le f hf u s)

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
  refine Finset.sum_congr rfl fun k _ => ?_
  have h (i : Fin p) : -v i - (k - s) = s - v i - k := by ring
  simp only [Equiv.subRight_apply, sub_neg_eq_add, sub_add_cancel, star_mul, star_prod,
    Complex.star_def, Complex.conj_ofReal, star_exponential, h, Finset.prod_mul_distrib]
  ring

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
  -- for fixed `u, v`: identity (5), the substitution `t = -s` and the correlation formula
  have h (u v : Fin p → ZMod N) : (∑ r : ZMod N, ‖fourier (prop121A f u v) r‖ ^ 2 *
      ‖fourier (prop121B lambda phi u) r‖ ^ 2) = (N : Real) * ∑ s : ZMod N,
        ‖∑ k : ZMod N, prop121InnerTerm lambda f phi u (fun i => s - v i) k‖ ^ 2 := by
    rw [lemma_2_1_holds N]
    congr 1
    simp_rw [← prop121_correlation_eq]
    exact (Fintype.sum_equiv (Equiv.neg (ZMod N)) _ _ fun _ => rfl).symm
  simp_rw [h, ← Finset.mul_sum]
  rw [pow_two, mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_comm]
  exact prop121_shift_sum fun x => ‖∑ k : ZMod N, prop121InnerTerm lambda f phi u x k‖ ^ 2

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
  have h (i : Fin p) : (phi i (q 0) - phi i (q 1) - phi i (q 2) + phi i (q 3)) * u i =
      phi i (q 0) * u i + -(phi i (q 2) * u i) + -(phi i (q 1) * u i) + phi i (q 3) * u i := by
    ring
  simp only [prop121B, star_mul, star_prod, Complex.star_def, Complex.conj_ofReal,
    star_exponential, h, exponential_add, Finset.prod_mul_distrib]
  push_cast
  ring

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
  have key : (∀ i, phi i (q 0) - phi i (q 1) - phi i (q 2) + phi i (q 3) = 0) ↔
      ∀ i, phi i (q 0) - phi i (q 1) = phi i (q 2) - phi i (q 3) :=
    forall_congr' fun i => ⟨fun h => by linear_combination h, fun h => by linear_combination h⟩
  simp_rw [prop121_b_product]
  rw [← Finset.mul_sum, prop121_vector_orthogonality]
  simp only [key]
  split_ifs <;> push_cast <;> ring

lemma prop121_fourthB_eq_weight {N p : Nat} [NeZero N]
    (lambda : ZMod N → Real) (phi : Fin p → ZMod N → ZMod N) :
    (∑ u : Fin p → ZMod N, ∑ r : ZMod N,
        ‖fourier (prop121B lambda phi u) r‖ ^ 4) =
      (N : Real) ^ (p + 1) * simultaneouslyAdditiveWeight lambda phi := by
  apply Complex.ofReal_injective
  -- expand each fourth moment by (2.6), then sum over `u` inside the additivity condition
  rw [Complex.ofReal_sum]
  simp_rw [identity_2_6_holds N, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_ite_irrel, Finset.sum_const_zero, prop121_sum_b_product, ← ite_and]
  rw [simultaneouslyAdditiveWeight, Complex.ofReal_mul, Complex.ofReal_sum, Finset.mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [IsSimultaneouslyAdditive]
  split_ifs <;> push_cast <;> ring

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
  let mixed : Real := ∑ u : Fin p → ZMod N, ∑ v : Fin p → ZMod N, ∑ r : ZMod N,
    ‖fourier (prop121A f u v) r‖ ^ 2 * ‖fourier (prop121B lambda phi u) r‖ ^ 2
  let fourthA : Real := ∑ u : Fin p → ZMod N, ∑ v : Fin p → ZMod N, ∑ r : ZMod N,
    ‖fourier (prop121A f u v) r‖ ^ 4
  let fourthB : Real := ∑ u : Fin p → ZMod N, ∑ _v : Fin p → ZMod N, ∑ r : ZMod N,
    ‖fourier (prop121B lambda phi u) r‖ ^ 4
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  -- with `M = N^(2p)`: `α M N ≤ L1`, and Cauchy--Schwarz `L1² ≤ M L2` gives `α² M N² ≤ L2`
  have hL1 : alpha * ((N : Real) ^ (2 * p) * N) ≤ L1 := by
    rw [← pow_succ]
    exact hlarge.trans (prop121_initial_bound lambda f phi hlambda hf)
  have hCauchy1 : L1 ^ 2 ≤ (N : Real) ^ (2 * p) * L2 :=
    prop121_l1_cauchy fun u s => ‖∑ k : ZMod N, prop121InnerTerm lambda f phi u s k‖
  have hL2 : alpha ^ 2 * ((N : Real) ^ (2 * p) * N ^ 2) ≤ L2 := le_of_mul_le_mul_left (by
    linarith [mul_self_le_mul_self (by positivity) hL1])
    (by positivity : (0 : Real) < (N : Real) ^ (2 * p))
  -- `mixed = N² L2`, and Cauchy--Schwarz `mixed² ≤ fourthA fourthB ≤ M N⁴ fourthB`
  have hmixed_eq : mixed = (N : Real) ^ 2 * L2 := prop121_mixed_eq_l2 lambda f phi
  have hmixed : alpha ^ 2 * ((N : Real) ^ (2 * p) * N ^ 4) ≤ mixed := by
    linarith [mul_le_mul_of_nonneg_left hL2 (sq_nonneg (N : Real))]
  have hfourthA : fourthA ≤ (N : Real) ^ (2 * p) * N ^ 4 := by
    rw [← pow_add]
    exact prop121_fourthA_le f hf
  have hglobal : mixed ^ 2 ≤ fourthA * fourthB := prop121_global_cauchy lambda f phi
  have hfourthB : alpha ^ 4 * ((N : Real) ^ (2 * p) * N ^ 4) ≤ fourthB :=
    le_of_mul_le_mul_left (by
      linarith [mul_self_le_mul_self (by positivity) hmixed,
        mul_le_mul_of_nonneg_right hfourthA (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg
          fun _ _ => Finset.sum_nonneg fun _ _ => pow_nonneg (norm_nonneg _) 4 :
            (0 : Real) ≤ fourthB)])
      (by positivity : (0 : Real) < (N : Real) ^ (2 * p) * N ^ 4)
  -- `fourthB = N^p N^(p+1) W = M N W`
  have hfourthB_eq :
      fourthB = (N : Real) ^ (2 * p) * N * simultaneouslyAdditiveWeight lambda phi :=
    (prop121_fourthB_with_v lambda phi).trans (by rw [prop121_fourthB_eq_weight]; ring)
  exact le_of_mul_le_mul_left (by linarith)
    (by positivity : (0 : Real) < (N : Real) ^ (2 * p) * N)

end LeanProofs.GowersSzemeredi

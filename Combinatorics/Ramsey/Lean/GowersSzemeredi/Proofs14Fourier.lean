import GowersSzemeredi.Sections14_15
import GowersSzemeredi.Proofs01_03
import GowersSzemeredi.Proofs12
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

attribute [simp] exponential_add

attribute [simp] star_exponential

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
          simp only [star_sum, star_mul, star_star, star_exponential,
            neg_neg]
          simp_rw [mul_sum, sum_mul]
          simp_rw [mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [Finset.sum_comm]
    _ = ∑ y : ZMod N, ∑ x : ZMod N, ∑ u : ZMod N, ∑ w : ZMod N,
        (exponential (-(y * r)) *
          (f (x + h, y) * star (f (x, y)))) *
        ((f (w, y - u) * star (f (w + h, y - u))) *
          exponential ((y - u) * r)) := by
            refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
            rw [← (Equiv.subLeft y).sum_comp]
            rfl
    _ = ∑ y : ZMod N, ∑ x : ZMod N, ∑ u : ZMod N, ∑ w : ZMod N,
        f (x + h, y) * star (f (x, y)) *
          star (f (w + h, y - u)) * f (w, y - u) *
            exponential (-(r * u)) := by
              refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ =>
                  Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => ?_
              have hphase :
                  exponential (-(y * r)) * exponential ((y - u) * r) =
                    exponential (-(r * u)) := by
                rw [← exponential_add]
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
  simp_rw [Complex.ofReal_mul, Complex.ofReal_prod, prop141_coeff_sq_expansion, Fintype.prod_sum,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun h _ => ?_
  simp only [prop141Outer, prop141InnerTerm]
  rw [mul_left_comm, ← Finset.prod_mul_distrib]
  exact congrArg _ (Finset.prod_congr rfl fun i _ => by ring)

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
  have h0 : 0 ≤ ∑ h : ZMod N, lambda h * ∏ i : Fin p,
      ‖fourier (firstCoordinateCorrelation (f i) h) (sigma i h)‖ ^ 2 :=
    Finset.sum_nonneg fun h _ => mul_nonneg (hlambda h) (by positivity)
  rw [← Real.norm_of_nonneg h0, ← Complex.norm_real, prop141_energy_expansion]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun u _ =>
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun w _ => ?_))))
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (prop141_outer_norm_le f hf y x u w)

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
  have h := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset ((Fin p → ZMod N) × (Fin p → ZMod N) × (Fin p → ZMod N) ×
      (Fin p → ZMod N))))
    (f := fun q => F q.1 q.2.1 q.2.2.1 q.2.2.2)
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, ZMod.card,
    Fintype.sum_prod_type] at h
  calc _ ≤ _ := h
    _ = _ := by push_cast; ring

private def prop141A {N p : Nat} (f : Fin p → Pair N → Complex)
    (y x u w : Fin p → ZMod N) (s : ZMod N) : Complex :=
  ∏ i, f i (s + x i, y i) * star (f i (s + w i, y i - u i))

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
    correlation (prop141A f y x u w) (prop121B lambda sigma u) s =
      ∑ h : ZMod N, prop141InnerTerm lambda f sigma y
        (fun i => s + x i) u (fun i => s + w i) h := by
  simp only [correlation]
  rw [← (prop141AddRightEquiv s).sum_comp]
  simp only [prop141AddRightEquiv_apply, add_sub_cancel_right]
  refine Finset.sum_congr rfl fun h _ => ?_
  simp only [prop141A, prop121B, prop141InnerTerm, star_mul, star_prod,
    Complex.star_def, Complex.conj_ofReal, star_exponential]
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
            refine Finset.prod_congr rfl fun i _ => ?_
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
          refine Finset.sum_congr rfl fun s _ => ?_
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
              refine Finset.sum_congr rfl fun x _ => ?_
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
              ‖fourier (prop121B lambda sigma u) r‖ ^ 2) =
      (N : Real) ^ 2 *
        ∑ y : Fin p → ZMod N, ∑ x : Fin p → ZMod N,
          ∑ u : Fin p → ZMod N, ∑ w : Fin p → ZMod N,
            ‖∑ h : ZMod N, prop141InnerTerm lambda f sigma y x u w h‖ ^ 2 := by
  let U := Fin p → ZMod N
  calc
    _ = ∑ y : U, ∑ x : U, ∑ u : U, ∑ w : U,
        (N : Real) * ∑ s : ZMod N,
          ‖correlation (prop141A f y x u w) (prop121B lambda sigma u) s‖ ^ 2 :=
      Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl
        fun u _ => Finset.sum_congr rfl fun w _ => lemma_2_1_holds N _ _
    _ = (N : Real) * ∑ y : U, ∑ x : U, ∑ u : U, ∑ w : U,
        ∑ s : ZMod N,
          ‖∑ h : ZMod N, prop141InnerTerm lambda f sigma y
            (fun i => s + x i) u (fun i => s + w i) h‖ ^ 2 := by
      simp_rw [← Finset.mul_sum, prop141_correlation_eq]
    _ = (N : Real) * ((N : Real) *
        ∑ y : U, ∑ x : U, ∑ u : U, ∑ w : U,
          ‖∑ h : ZMod N, prop141InnerTerm lambda f sigma y x u w h‖ ^ 2) := by
      congr 1
      calc
        _ = ∑ y : U, ∑ u : U, ∑ s : ZMod N, ∑ x : U, ∑ w : U,
              ‖∑ h : ZMod N, prop141InnerTerm lambda f sigma y
                (fun i => s + x i) u (fun i => s + w i) h‖ ^ 2 := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun u _ =>
            (Finset.sum_congr rfl fun x _ => Finset.sum_comm).trans Finset.sum_comm
        _ = ∑ y : U, ∑ u : U, (N : Real) * ∑ x : U, ∑ w : U,
              ‖∑ h : ZMod N, prop141InnerTerm lambda f sigma y x u w h‖ ^ 2 :=
          Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun u _ =>
            prop141_double_shift_sum (N := N) (p := p) (fun x w =>
              ‖∑ h : ZMod N, prop141InnerTerm lambda f sigma y x u w h‖ ^ 2)
        _ = _ := by
          simp_rw [← Finset.mul_sum]
          exact congrArg (fun t : Real => (N : Real) * t)
            (Finset.sum_congr rfl fun y _ => Finset.sum_comm)
    _ = _ := by
      simp only [pow_two, mul_assoc]
      rfl

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
          gcongr with y _ x _ u _ w _
          exact fourier_fourth_moment_le (prop141A f y x u w)
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
              ‖fourier (prop121B lambda sigma u) r‖ ^ 2) ^ 2 ≤
      (∑ y : Fin p → ZMod N, ∑ x : Fin p → ZMod N,
        ∑ u : Fin p → ZMod N, ∑ w : Fin p → ZMod N,
          ∑ r : ZMod N, ‖fourier (prop141A f y x u w) r‖ ^ 4) *
      ∑ _y : Fin p → ZMod N, ∑ _x : Fin p → ZMod N,
        ∑ u : Fin p → ZMod N, ∑ _w : Fin p → ZMod N,
          ∑ r : ZMod N, ‖fourier (prop121B lambda sigma u) r‖ ^ 4 := by
  let U := Fin p → ZMod N
  have h := Finset.sum_mul_sq_le_sq_mul_sq
    ((((Finset.univ : Finset U) ×ˢ (Finset.univ : Finset U)) ×ˢ
      ((Finset.univ : Finset U) ×ˢ (Finset.univ : Finset U))) ×ˢ
        (Finset.univ : Finset (ZMod N)))
    (fun z => ‖fourier
      (prop141A f z.1.1.1 z.1.1.2 z.1.2.1 z.1.2.2) z.2‖ ^ 2)
    (fun z => ‖fourier (prop121B lambda sigma z.1.2.1) z.2‖ ^ 2)
  simpa only [Finset.sum_product, ← pow_mul] using h

alias prop141_sum_exponential_mul := fejer_sum_exponential_mul

lemma prop141_prod_fin_four (a : Fin 4 → Real) :
    (∏ i, a i) = a 0 * a 1 * a 2 * a 3 := by
  rw [Fin.prod_univ_four]

private lemma prop141_weight_eq_energy {N p : Nat} [NeZero N]
    (lambda : ZMod N → Real) (sigma : Fin p → ZMod N → ZMod N) :
    simultaneouslyAdditiveWeight lambda sigma =
      weightedSimultaneousAdditiveEnergy Finset.univ lambda sigma := by
  unfold simultaneouslyAdditiveWeight weightedSimultaneousAdditiveEnergy
  refine Fintype.sum_equiv
    ({ toFun q := ![q 0, q 3, q 2, q 1]
       invFun q := ![q 0, q 3, q 2, q 1]
       left_inv q := by funext i; fin_cases i <;> rfl
       right_inv q := by funext i; fin_cases i <;> rfl } : (Fin 4 → ZMod N) ≃ (Fin 4 → ZMod N))
    _ _ fun q => ?_
  simp only [IsSimultaneouslyAdditive, IsAdditiveQuadruple, Finset.mem_univ, forall_const,
    true_and, sub_eq_sub_iff_add_eq_add, Fin.prod_univ_four, Equiv.coe_fn_mk, Matrix.cons_val]
  exact if_congr Iff.rfl (by ring) rfl

private lemma prop141_fourthB_total_eq_energy {N p : Nat} [NeZero N]
    (lambda : ZMod N → Real) (sigma : Fin p → ZMod N → ZMod N) :
    (∑ _y : Fin p → ZMod N, ∑ _x : Fin p → ZMod N,
        ∑ u : Fin p → ZMod N, ∑ _w : Fin p → ZMod N,
          ∑ r : ZMod N, ‖fourier (prop121B lambda sigma u) r‖ ^ 4) =
      (N : Real) ^ (4 * p + 1) *
        weightedSimultaneousAdditiveEnergy Finset.univ lambda sigma := by
  let U := Fin p → ZMod N
  have hcard : Fintype.card U = N ^ p := by simp [U]
  calc
    _ = ∑ y : U, ∑ u : U, ∑ _x : U, ∑ _w : U,
        ∑ r : ZMod N, ‖fourier (prop121B lambda sigma u) r‖ ^ 4 := by
          refine Finset.sum_congr rfl fun y _ => ?_
          exact Finset.sum_comm
    _ = ∑ u : U, ∑ _y : U, ∑ _x : U, ∑ _w : U,
        ∑ r : ZMod N, ‖fourier (prop121B lambda sigma u) r‖ ^ 4 :=
      Finset.sum_comm
    _ = (N : Real) ^ (3 * p) *
        ∑ u : U, ∑ r : ZMod N,
          ‖fourier (prop121B lambda sigma u) r‖ ^ 4 := by
            simp only [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
            push_cast
            simp_rw [← Finset.mul_sum]
            rw [show 3 * p = p + p + p by omega, pow_add, pow_add]
            ring
    _ = (N : Real) ^ (3 * p) *
        ((N : Real) ^ (p + 1) *
          simultaneouslyAdditiveWeight lambda sigma) := by
            rw [prop121_fourthB_eq_weight]
    _ = (N : Real) ^ (4 * p + 1) *
        weightedSimultaneousAdditiveEnergy Finset.univ lambda sigma := by
          rw [prop141_weight_eq_energy, show 4 * p + 1 = 3 * p + (p + 1) by omega, pow_add]
          ring

/-- Proposition 14.1 follows by expanding the squared Fourier coefficients,
applying Cauchy--Schwarz over the four vector variables, introducing a common
scalar shift, and using character orthogonality for the `Fin p` family. -/
theorem proposition_14_1_holds : proposition_14_1 := by
  intro N p _ lambda f sigma alpha hAlpha hlambda hf hlarge
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  -- the arithmetic of the Cauchy--Schwarz chain, with the five sums as variables
  have key (S1 S2 Sm SA SB E : Real) (h1 : alpha * (N : Real) ^ (4 * p + 1) ≤ S1)
      (h2 : S1 ^ 2 ≤ (N : Real) ^ (4 * p) * S2) (h3 : Sm = (N : Real) ^ 2 * S2)
      (h4 : Sm ^ 2 ≤ SA * SB) (h5 : SA ≤ (N : Real) ^ (4 * p + 4)) (hB : 0 ≤ SB)
      (h6 : SB = (N : Real) ^ (4 * p + 1) * E) : alpha ^ 4 * (N : Real) ^ 3 ≤ E := by
    have hS2 : alpha ^ 2 * (N : Real) ^ (4 * p + 2) ≤ S2 := le_of_mul_le_mul_left (calc
      (N : Real) ^ (4 * p) * (alpha ^ 2 * N ^ (4 * p + 2)) = (alpha * N ^ (4 * p + 1)) ^ 2 := by
        ring
      _ ≤ _ := (pow_le_pow_left₀ (by positivity) h1 2).trans h2) (pow_pos hN _)
    have hSm : alpha ^ 2 * (N : Real) ^ (4 * p + 4) ≤ Sm := calc
      _ = (N : Real) ^ 2 * (alpha ^ 2 * N ^ (4 * p + 2)) := by ring
      _ ≤ Sm := by rw [h3]; gcongr
    have hSB : alpha ^ 4 * (N : Real) ^ (4 * p + 4) ≤ SB := le_of_mul_le_mul_left (calc
      (N : Real) ^ (4 * p + 4) * (alpha ^ 4 * N ^ (4 * p + 4)) =
          (alpha ^ 2 * N ^ (4 * p + 4)) ^ 2 := by ring
      _ ≤ SA * SB := (pow_le_pow_left₀ (by positivity) hSm 2).trans h4
      _ ≤ (N : Real) ^ (4 * p + 4) * SB := by gcongr) (pow_pos hN _)
    apply le_of_mul_le_mul_left _ (pow_pos hN (4 * p + 1))
    calc _ = alpha ^ 4 * (N : Real) ^ (4 * p + 4) := by ring
      _ ≤ SB := hSB
      _ = _ := h6
  exact key _ _ _ _ _ _ (hlarge.trans (prop141_initial_bound lambda f sigma hlambda hf))
    (prop141_l1_cauchy _) (prop141_mixed_eq_l2 lambda f sigma)
    (prop141_global_cauchy lambda f sigma) (prop141_fourthA_le f hf) (by positivity)
    (prop141_fourthB_total_eq_energy lambda sigma)

end LeanProofs.GowersSzemeredi

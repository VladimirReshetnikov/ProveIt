import GowersSzemeredi.Sections12_13
import GowersSzemeredi.Proofs01_03
import GowersSzemeredi.Proofs06PhiAdditiveFourier
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

attribute [simp] exponential_add

attribute [simp] star_exponential

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
  have hF (g : ZMod N → Complex) :
      fourier g r = ∑ s : ZMod N, exponential (-(s * r)) * g s := ZMod.dft_apply g r
  -- `‖ĝ r‖² = ĝ r * star (ĝ r)` is a double sum over `(x, t)`; substitute `t = x - u`
  rw [Complex.ofReal_pow, ← Complex.mul_conj', ← Complex.star_def, hF, star_sum,
    Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← (Equiv.subLeft x).sum_comp, Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [show -(u * r) = -(x * r) + (x - u) * r by ring, exponential_add]
  simp only [verticalCorrelation, prop131Outer, Equiv.subLeft_apply, star_mul, star_sum,
    star_star, star_exponential, neg_neg, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y' _ => Finset.sum_congr rfl fun y _ => ?_
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
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y' _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
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
  have henergy : 0 ≤ ∑ h ∈ B, ‖fourier (verticalCorrelation f h) (sigma h)‖ ^ 2 := by
    positivity
  rw [← Real.norm_of_nonneg henergy, ← Complex.norm_real, prop131_energy_expansion f B sigma]
  refine (norm_sum_le _ _).trans <| Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans <|
    Finset.sum_le_sum fun y' _ => (norm_sum_le _ _).trans <| Finset.sum_le_sum fun u _ =>
      (norm_sum_le _ _).trans <| Finset.sum_le_sum fun y _ => ?_
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (prop131_outer_norm_le f hf u x y y')

private lemma prop131_l1_cauchy {N : Nat} [NeZero N]
    (F : ZMod N → ZMod N → ZMod N → ZMod N → Real) :
    (∑ x : ZMod N, ∑ y' : ZMod N, ∑ u : ZMod N, ∑ y : ZMod N,
        F x y' u y) ^ 2 ≤
      (N : Real) ^ 4 *
        ∑ x : ZMod N, ∑ y' : ZMod N, ∑ u : ZMod N, ∑ y : ZMod N,
          (F x y' u y) ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset (ZMod N × ZMod N × ZMod N × ZMod N)))
    (f := fun q => F q.1 q.2.1 q.2.2.1 q.2.2.2)
  simp only [Finset.card_univ, Fintype.card_prod, ZMod.card, Fintype.sum_prod_type] at h
  calc _ ≤ _ := h
    _ = _ := by push_cast; ring

private def prop131A {N : Nat} (f : Pair N → Complex)
    (u x w h : ZMod N) : Complex :=
  f (x, w + h) * star (f (x - u, h))

attribute [simp] lemma78_indicator_star

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
    correlation (prop131A f u x w) (prop61G B sigma u) y =
      ∑ h ∈ B, prop131InnerTerm f sigma u x y (w + y) h := by
  simp only [correlation]
  rw [← (prop131AddRightEquiv y).sum_comp]
  simp only [prop131AddRightEquiv_apply, add_sub_cancel_right]
  unfold prop131A prop61G prop131InnerTerm
  simp only [star_mul, lemma78_indicator_star, star_exponential]
  simp only [indicator, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  rw [show (Finset.univ.filter fun h : ZMod N => h ∈ B) = B by
    ext h
    simp]
  refine Finset.sum_congr rfl fun h _ => ?_
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
      refine Finset.sum_congr rfl fun y _ => ?_
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
          ‖fourier (prop61G B sigma u) r‖ ^ 2) =
      (N : Real) *
        ∑ x : ZMod N, ∑ y' : ZMod N, ∑ u : ZMod N, ∑ y : ZMod N,
          ‖∑ h ∈ B, prop131InnerTerm f sigma u x y y' h‖ ^ 2 := by
  calc
    _ = ∑ u : ZMod N, ∑ x : ZMod N, ∑ w : ZMod N,
        (N : Real) * ∑ y : ZMod N,
          ‖correlation (prop131A f u x w) (prop61G B sigma u) y‖ ^ 2 :=
      Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun x _ =>
        Finset.sum_congr rfl fun w _ => lemma_2_1_holds N _ _
    _ = (N : Real) * ∑ u : ZMod N, ∑ x : ZMod N, ∑ w : ZMod N, ∑ y : ZMod N,
          ‖∑ h ∈ B, prop131InnerTerm f sigma u x y (w + y) h‖ ^ 2 := by
      simp_rw [← Finset.mul_sum, prop131_correlation_eq]
    _ = _ := by
      congr 1
      rw [Finset.sum_comm]
      refine (Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun u _ =>
        (prop131_shift_pair_sum (N := N) fun y y' =>
          ‖∑ h ∈ B, prop131InnerTerm f sigma u x y y' h‖ ^ 2).symm).trans ?_
      exact Finset.sum_congr rfl fun x _ => Finset.sum_comm

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
          gcongr with u _ x _ w _
          exact fourier_fourth_moment_le (prop131A f u x w)
            (prop131A_disc f hf u x w)
    _ = (N : Real) ^ 7 := by simp; ring

private lemma prop131_fourthG_eq_count {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (sigma : ZMod N → ZMod N) :
    (∑ u : ZMod N, ∑ _x : ZMod N, ∑ _w : ZMod N, ∑ r : ZMod N,
        ‖fourier (prop61G B sigma u) r‖ ^ 4) =
      (N : Real) ^ 4 * phiAdditiveCount B sigma := by
  calc
    _ = (N : Real) ^ 2 *
        ∑ u : ZMod N, ∑ r : ZMod N,
          ‖fourier (prop61G B sigma u) r‖ ^ 4 := by
            simp only [Finset.sum_const, Finset.card_univ, ZMod.card,
              nsmul_eq_mul]
            simp_rw [← Finset.mul_sum]
            ring
    _ = (N : Real) ^ 2 *
        ((N : Real) ^ 2 * phiAdditiveCount B sigma) := by
          rw [prop61_g_fourth_eq_count]
    _ = (N : Real) ^ 4 * phiAdditiveCount B sigma := by ring

private lemma prop131_global_cauchy {N : Nat} [NeZero N]
    (f : Pair N → Complex) (B : Finset (ZMod N))
    (sigma : ZMod N → ZMod N) :
    (∑ u : ZMod N, ∑ x : ZMod N, ∑ w : ZMod N, ∑ r : ZMod N,
        ‖fourier (prop131A f u x w) r‖ ^ 2 *
          ‖fourier (prop61G B sigma u) r‖ ^ 2) ^ 2 ≤
      (∑ u : ZMod N, ∑ x : ZMod N, ∑ w : ZMod N, ∑ r : ZMod N,
        ‖fourier (prop131A f u x w) r‖ ^ 4) *
      ∑ u : ZMod N, ∑ _x : ZMod N, ∑ _w : ZMod N, ∑ r : ZMod N,
        ‖fourier (prop61G B sigma u) r‖ ^ 4 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq
    ((((Finset.univ : Finset (ZMod N)) ×ˢ (Finset.univ : Finset (ZMod N))) ×ˢ
      (Finset.univ : Finset (ZMod N))) ×ˢ (Finset.univ : Finset (ZMod N)))
    (fun z => ‖fourier (prop131A f z.1.1.1 z.1.1.2 z.1.2) z.2‖ ^ 2)
    (fun z => ‖fourier (prop61G B sigma z.1.1.1) z.2‖ ^ 2)
  simpa only [Finset.sum_product, ← pow_mul] using h

/-- Lemma 13.1 follows from two Cauchy--Schwarz inequalities, the Fourier
correlation identity, and character orthogonality. -/
theorem lemma_13_1_holds : lemma_13_1 := by
  intro N _ f B sigma alpha hAlpha hf hlarge
  let L1 : Real := ∑ x : ZMod N, ∑ y' : ZMod N, ∑ u : ZMod N, ∑ y : ZMod N,
    ‖∑ h ∈ B, prop131InnerTerm f sigma u x y y' h‖
  let L2 : Real := ∑ x : ZMod N, ∑ y' : ZMod N, ∑ u : ZMod N, ∑ y : ZMod N,
    ‖∑ h ∈ B, prop131InnerTerm f sigma u x y y' h‖ ^ 2
  let mixed : Real := ∑ u : ZMod N, ∑ x : ZMod N, ∑ w : ZMod N, ∑ r : ZMod N,
    ‖fourier (prop131A f u x w) r‖ ^ 2 * ‖fourier (prop61G B sigma u) r‖ ^ 2
  let fourthA : Real := ∑ u : ZMod N, ∑ x : ZMod N, ∑ w : ZMod N, ∑ r : ZMod N,
    ‖fourier (prop131A f u x w) r‖ ^ 4
  let fourthG : Real := ∑ u : ZMod N, ∑ _x : ZMod N, ∑ _w : ZMod N, ∑ r : ZMod N,
    ‖fourier (prop61G B sigma u) r‖ ^ 4
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  -- `α N⁵ ≤ L1`; Cauchy--Schwarz gives `L1² ≤ N⁴ L2`, hence `α² N⁶ ≤ L2`
  have hL1 : alpha * (N : Real) ^ 5 ≤ L1 := hlarge.trans (prop131_initial_bound f B sigma hf)
  have hCauchy1 : L1 ^ 2 ≤ (N : Real) ^ 4 * L2 :=
    prop131_l1_cauchy fun x y' u y => ‖∑ h ∈ B, prop131InnerTerm f sigma u x y y' h‖
  have hL2 : alpha ^ 2 * (N : Real) ^ 6 ≤ L2 := le_of_mul_le_mul_left (by
    linarith [mul_self_le_mul_self (by positivity) hL1]) (by positivity : (0 : Real) < N ^ 4)
  -- `mixed = N L2 ≥ α² N⁷`; Cauchy--Schwarz gives `mixed² ≤ fourthA fourthG ≤ N⁷ fourthG`
  have hmixed_eq : mixed = (N : Real) * L2 := prop131_mixed_eq_l2 f B sigma
  have hmixed : alpha ^ 2 * (N : Real) ^ 7 ≤ mixed := by
    linarith [mul_le_mul_of_nonneg_left hL2 hN.le]
  have hfourthA : fourthA ≤ (N : Real) ^ 7 := prop131_fourthA_le f hf
  have hglobal : mixed ^ 2 ≤ fourthA * fourthG := prop131_global_cauchy f B sigma
  have hfourthG : alpha ^ 4 * (N : Real) ^ 7 ≤ fourthG := le_of_mul_le_mul_left (by
    linarith [mul_self_le_mul_self (by positivity) hmixed,
      mul_le_mul_of_nonneg_right hfourthA (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg
        fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
          pow_nonneg (norm_nonneg _) 4 : (0 : Real) ≤ fourthG)])
    (by positivity : (0 : Real) < N ^ 7)
  have hfourthG_eq : fourthG = (N : Real) ^ 4 * phiAdditiveCount B sigma :=
    prop131_fourthG_eq_count B sigma
  exact le_of_mul_le_mul_left (by linarith) (by positivity : (0 : Real) < N ^ 4)

private def prop132Indicator {N : Nat} (A : Finset (Pair N)) :
    Pair N → Complex :=
  fun z => if z ∈ A then 1 else 0

private lemma prop132_indicator_disc {N : Nat} (A : Finset (Pair N)) :
    DiscValued (prop132Indicator A) := by
  intro z
  simp only [prop132Indicator]
  split_ifs <;> simp

private lemma prop132_fiber_count_eq {N : Nat} [NeZero N]
    (A : Finset (Pair N)) (h x : ZMod N) :
    verticalEdgeFiberCount A h x =
      ((Finset.univ : Finset (ZMod N)).filter fun y =>
        (x, y) ∈ A ∧ (x, y + h) ∈ A).card := by
  unfold verticalEdgeFiberCount verticalEdgeDomain
  apply Finset.card_bij (fun z _ => z.2)
  · rintro ⟨zx, zy⟩ hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    rcases hz with ⟨⟨hzA, hzAh⟩, hzx⟩
    subst zx
    exact ⟨hzA, hzAh⟩
  · rintro ⟨ax, ay⟩ ha ⟨bx, byy⟩ hb hab
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    rcases ha with ⟨_, hax⟩
    rcases hb with ⟨_, hbx⟩
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

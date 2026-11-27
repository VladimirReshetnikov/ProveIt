import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Rat.Floor

/-!
# Rounded rational boxes for complex values

The executable endpoints use exact rational arithmetic. Multiplication rounds
outward to a fixed decimal grid to keep later finite certificates small.
-/

namespace GRHArticle.SingularModuli

structure RationalInterval where
  lo : ℚ
  hi : ℚ

namespace RationalInterval

def Contains (A : RationalInterval) (x : ℝ) : Prop := (A.lo : ℝ) ≤ x ∧ x ≤ (A.hi : ℝ)

def point (q : ℚ) : RationalInterval := ⟨q, q⟩

def roundingScale : ℚ := 10 ^ 56

def rounded (a b : ℚ) : RationalInterval :=
  ⟨(⌊a * roundingScale⌋ : ℤ) / roundingScale, (⌈b * roundingScale⌉ : ℤ) / roundingScale⟩

def add (A B : RationalInterval) : RationalInterval := ⟨A.lo + B.lo, A.hi + B.hi⟩

def neg (A : RationalInterval) : RationalInterval := ⟨-A.hi, -A.lo⟩

def sub (A B : RationalInterval) : RationalInterval := A.add B.neg

def mul (A B : RationalInterval) : RationalInterval :=
  rounded (min (min (A.lo * B.lo) (A.lo * B.hi)) (min (A.hi * B.lo) (A.hi * B.hi)))
    (max (max (A.lo * B.lo) (A.lo * B.hi)) (max (A.hi * B.lo) (A.hi * B.hi)))

def invPos (A : RationalInterval) : RationalInterval := rounded A.hi⁻¹ A.lo⁻¹

def pow (A : RationalInterval) : ℕ → RationalInterval
  | 0 => point 1
  | n + 1 => (A.pow n).mul A

def widen (A : RationalInterval) (e : ℚ) : RationalInterval := ⟨A.lo - e, A.hi + e⟩

theorem contains_point (q : ℚ) : (point q).Contains q := ⟨le_rfl, le_rfl⟩

theorem contains_rounded {a b : ℚ} {x : ℝ} (ha : (a : ℝ) ≤ x) (hb : x ≤ (b : ℝ)) :
    (rounded a b).Contains x := by
  have hscale : 0 < (roundingScale : ℝ) := by norm_num [roundingScale]
  have hlo : (⌊a * roundingScale⌋ : ℝ) ≤ (a : ℝ) * (roundingScale : ℝ) := by
    exact_mod_cast (Int.floor_le (a * roundingScale))
  have hhi : (b : ℝ) * (roundingScale : ℝ) ≤ (⌈b * roundingScale⌉ : ℝ) := by
    exact_mod_cast (Int.le_ceil (b * roundingScale))
  constructor
  · simpa only [rounded, Rat.cast_div, Rat.cast_intCast] using
      (div_le_iff₀ hscale).2 (hlo.trans (mul_le_mul_of_nonneg_right ha hscale.le))
  · simpa only [rounded, Rat.cast_div, Rat.cast_intCast] using
      (le_div_iff₀ hscale).2 ((mul_le_mul_of_nonneg_right hb hscale.le).trans hhi)

theorem contains_add {A B : RationalInterval} {x y : ℝ}
    (hx : A.Contains x) (hy : B.Contains y) : (A.add B).Contains (x + y) := by
  simpa only [Contains, add, Rat.cast_add] using
    And.intro (add_le_add hx.1 hy.1) (add_le_add hx.2 hy.2)

theorem contains_neg {A : RationalInterval} {x : ℝ} (hx : A.Contains x) :
    A.neg.Contains (-x) := by
  simpa only [Contains, neg, Rat.cast_neg] using And.intro (neg_le_neg hx.2) (neg_le_neg hx.1)

theorem contains_sub {A B : RationalInterval} {x y : ℝ}
    (hx : A.Contains x) (hy : B.Contains y) : (A.sub B).Contains (x - y) := by
  simpa only [sub, sub_eq_add_neg] using contains_add hx (contains_neg hy)

private theorem mul_between (k : ℝ) {a b x : ℝ} (ha : a ≤ x) (hb : x ≤ b) :
    min (k * a) (k * b) ≤ k * x ∧ k * x ≤ max (k * a) (k * b) := by
  rcases le_total 0 k with hk | hk
  · exact ⟨(min_le_left ..).trans (mul_le_mul_of_nonneg_left ha hk),
      (mul_le_mul_of_nonneg_left hb hk).trans (le_max_right ..)⟩
  · exact ⟨(min_le_right ..).trans (mul_le_mul_of_nonpos_left hb hk),
      (mul_le_mul_of_nonpos_left ha hk).trans (le_max_left ..)⟩

theorem contains_mul {A B : RationalInterval} {x y : ℝ}
    (hx : A.Contains x) (hy : B.Contains y) : (A.mul B).Contains (x * y) := by
  have ha := mul_between (A.lo : ℝ) hy.1 hy.2
  have hb := mul_between (A.hi : ℝ) hy.1 hy.2
  have hyx := mul_between y hx.1 hx.2
  rw [mul_comm y (A.lo : ℝ), mul_comm y (A.hi : ℝ), mul_comm y x] at hyx
  apply contains_rounded
  · push_cast
    exact (le_min ((min_le_left ..).trans ha.1) ((min_le_right ..).trans hb.1)).trans hyx.1
  · push_cast
    exact hyx.2.trans (max_le (ha.2.trans (le_max_left ..)) (hb.2.trans (le_max_right ..)))

theorem contains_pow {A : RationalInterval} {x : ℝ} (hx : A.Contains x) (n : ℕ) :
    (A.pow n).Contains (x ^ n) := by
  induction n with
  | zero => simpa only [pow, pow_zero, Rat.cast_one] using contains_point 1
  | succ n ih => simpa only [pow, pow_succ] using contains_mul ih hx

theorem contains_invPos {A : RationalInterval} {x : ℝ} (hA : 0 < A.lo)
    (hx : A.Contains x) : A.invPos.Contains x⁻¹ := by
  have hp : 0 < (A.lo : ℝ) := by exact_mod_cast hA
  apply contains_rounded
  · rw [Rat.cast_inv]
    exact inv_anti₀ (hp.trans_le hx.1) hx.2
  · rw [Rat.cast_inv]
    exact inv_anti₀ hp hx.1

theorem contains_widen {A : RationalInterval} {x y : ℝ} {e : ℚ}
    (hx : A.Contains x) (hxy : |y - x| ≤ (e : ℝ)) : (A.widen e).Contains y := by
  obtain ⟨hl, hu⟩ := abs_le.mp hxy
  dsimp only [Contains, widen]
  push_cast
  exact ⟨by linarith only [hx.1, hl], by linarith only [hx.2, hu]⟩

end RationalInterval

structure RationalComplexBox where
  re : RationalInterval
  im : RationalInterval

namespace RationalComplexBox

def Contains (A : RationalComplexBox) (z : ℂ) : Prop := A.re.Contains z.re ∧ A.im.Contains z.im

def real (A : RationalInterval) : RationalComplexBox := ⟨A, RationalInterval.point 0⟩

def point (r i : ℚ) : RationalComplexBox := ⟨RationalInterval.point r, RationalInterval.point i⟩

def add (A B : RationalComplexBox) : RationalComplexBox := ⟨A.re.add B.re, A.im.add B.im⟩

def neg (A : RationalComplexBox) : RationalComplexBox := ⟨A.re.neg, A.im.neg⟩

def sub (A B : RationalComplexBox) : RationalComplexBox := A.add B.neg

def mul (A B : RationalComplexBox) : RationalComplexBox :=
  ⟨(A.re.mul B.re).sub (A.im.mul B.im), (A.re.mul B.im).add (A.im.mul B.re)⟩

def normSq (A : RationalComplexBox) : RationalInterval := (A.re.mul A.re).add (A.im.mul A.im)

def inv (A : RationalComplexBox) : RationalComplexBox :=
  ⟨A.re.mul A.normSq.invPos, A.im.neg.mul A.normSq.invPos⟩

def widen (A : RationalComplexBox) (e : ℚ) : RationalComplexBox := ⟨A.re.widen e, A.im.widen e⟩

def pow (A : RationalComplexBox) : ℕ → RationalComplexBox
  | 0 => point 1 0
  | n + 1 => (A.pow n).mul A

theorem contains_real {A : RationalInterval} {x : ℝ} (hx : A.Contains x) : (real A).Contains x :=
  ⟨hx, by simpa only [real, Complex.ofReal_im, Rat.cast_zero] using RationalInterval.contains_point 0⟩

theorem contains_point (r i : ℚ) : (point r i).Contains ⟨r, i⟩ :=
  ⟨RationalInterval.contains_point r, RationalInterval.contains_point i⟩

theorem contains_add {A B : RationalComplexBox} {z w : ℂ}
    (hz : A.Contains z) (hw : B.Contains w) : (A.add B).Contains (z + w) :=
  ⟨RationalInterval.contains_add hz.1 hw.1, RationalInterval.contains_add hz.2 hw.2⟩

theorem contains_neg {A : RationalComplexBox} {z : ℂ} (hz : A.Contains z) :
    A.neg.Contains (-z) := ⟨RationalInterval.contains_neg hz.1, RationalInterval.contains_neg hz.2⟩

theorem contains_sub {A B : RationalComplexBox} {z w : ℂ}
    (hz : A.Contains z) (hw : B.Contains w) : (A.sub B).Contains (z - w) := by
  simpa only [sub, sub_eq_add_neg] using contains_add hz (contains_neg hw)

theorem contains_mul {A B : RationalComplexBox} {z w : ℂ}
    (hz : A.Contains z) (hw : B.Contains w) : (A.mul B).Contains (z * w) :=
  ⟨RationalInterval.contains_sub (RationalInterval.contains_mul hz.1 hw.1)
    (RationalInterval.contains_mul hz.2 hw.2),
   RationalInterval.contains_add (RationalInterval.contains_mul hz.1 hw.2)
    (RationalInterval.contains_mul hz.2 hw.1)⟩

theorem contains_pow {A : RationalComplexBox} {z : ℂ} (hz : A.Contains z) (n : ℕ) :
    (A.pow n).Contains (z ^ n) := by
  induction n with
  | zero => simp [pow, Contains, point, RationalInterval.Contains, RationalInterval.point]
  | succ n ih => simpa only [pow, pow_succ] using contains_mul ih hz

theorem contains_inv {A : RationalComplexBox} {z : ℂ} (hA : 0 < A.normSq.lo)
    (hz : A.Contains z) : A.inv.Contains z⁻¹ := by
  have hnorm : A.normSq.Contains (Complex.normSq z) := by
    rw [Complex.normSq_apply]
    exact RationalInterval.contains_add (RationalInterval.contains_mul hz.1 hz.1)
      (RationalInterval.contains_mul hz.2 hz.2)
  have h := RationalInterval.contains_invPos hA hnorm
  exact ⟨by simpa only [inv, Complex.inv_re, div_eq_mul_inv] using RationalInterval.contains_mul hz.1 h,
    by simpa only [inv, Complex.inv_im, div_eq_mul_inv] using
      RationalInterval.contains_mul (RationalInterval.contains_neg hz.2) h⟩

theorem contains_widen {A : RationalComplexBox} {z w : ℂ} {e : ℚ}
    (hz : A.Contains z) (hzw : ‖w - z‖ ≤ (e : ℝ)) : (A.widen e).Contains w :=
  ⟨RationalInterval.contains_widen hz.1 ((Complex.abs_re_le_norm (w - z)).trans hzw),
    RationalInterval.contains_widen hz.2 ((Complex.abs_im_le_norm (w - z)).trans hzw)⟩

end RationalComplexBox
end GRHArticle.SingularModuli

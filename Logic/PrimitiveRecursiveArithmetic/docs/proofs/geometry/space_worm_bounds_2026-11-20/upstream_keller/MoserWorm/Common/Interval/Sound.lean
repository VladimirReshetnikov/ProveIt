/-
Copyright (c) 2026 Ethan Keller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Keller
-/
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import MoserWorm.Common.Interval.Basic

/-!
Real semantics and soundness of dyadic intervals. `mem_iff_val` expresses
membership using endpoint values; `Basic` contains only computation.
-/

namespace MoserWorm
namespace DIval

/-- The real number a mantissa denotes. -/
noncomputable def val (m : Int) : ℝ := (m : ℝ) / 2 ^ dfxS

/-- Enclosure: `x` lies in the interval `I`. -/
def mem (I : DIval) (x : ℝ) : Prop :=
  (I.lo : ℝ) ≤ x * 2 ^ dfxS ∧ x * 2 ^ dfxS ≤ (I.hi : ℝ)

instance : Membership ℝ DIval := ⟨fun I x => I.mem x⟩

/-- Unfolding lemma for the membership relation. -/
theorem mem_def {I : DIval} {x : ℝ} :
    x ∈ I ↔ (I.lo : ℝ) ≤ x * 2 ^ dfxS ∧ x * 2 ^ dfxS ≤ (I.hi : ℝ) := Iff.rfl

/-- Membership in terms of the real endpoint values. -/
theorem mem_iff_val {I : DIval} {x : ℝ} :
    x ∈ I ↔ val I.lo ≤ x ∧ x ≤ val I.hi := by
  have h2pos : (0 : ℝ) < 2 ^ dfxS := by positivity
  simp only [mem_def, val, div_le_iff₀ h2pos, le_div_iff₀ h2pos]

theorem mem_add {a b : DIval} {x y : ℝ} (ha : x ∈ a) (hb : y ∈ b) :
    (x + y) ∈ a.add b := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  constructor <;> · simp only [add, add_mul]; push_cast; linarith

theorem mem_sub {a b : DIval} {x y : ℝ} (ha : x ∈ a) (hb : y ∈ b) :
    (x - y) ∈ a.sub b := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  constructor <;> · simp only [sub, sub_mul]; push_cast; linarith

theorem mem_neg {a : DIval} {x : ℝ} (ha : x ∈ a) : (-x) ∈ a.neg := by
  obtain ⟨h1, h2⟩ := ha
  constructor <;> · simp only [neg, neg_mul]; push_cast; linarith

/-! ### Shift helpers -/

/-- `fshr` rounds downward: `fshr m s ≤ m / 2^s` (as reals, cleared of the
denominator). -/
private lemma fshr_le (m : Int) (s : Nat) : (fshr m s : ℝ) * 2 ^ s ≤ (m : ℝ) := by
  have h : (0 : Int) < 2 ^ s := by positivity
  have h2 := Int.ediv_mul_le m (b := 2 ^ s) h.ne'
  rw [fshr, Int.fdiv_eq_ediv_of_nonneg _ h.le]
  exact_mod_cast h2

/-- `cshr` rounds upward: `m / 2^s ≤ cshr m s` (as reals, cleared of the
denominator). -/
private lemma le_cshr (m : Int) (s : Nat) : (m : ℝ) ≤ (cshr m s : ℝ) * 2 ^ s := by
  have h := fshr_le (-m) s
  simp only [cshr]
  push_cast at h ⊢
  linarith

/-! ### Pointwise and lattice operations -/

/-- Point-interval soundness: `pt m` contains the real `m · 2^-56`. -/
theorem mem_pt (m : Int) : (m : ℝ) / 2 ^ dfxS ∈ pt m := by
  have h : (m : ℝ) / 2 ^ dfxS * 2 ^ dfxS = (m : ℝ) := by
    field_simp
  constructor <;> simp [pt, h]

/-- `ofInt k` contains the integer `k` exactly. -/
theorem mem_ofInt (k : Int) : (k : ℝ) ∈ ofInt k := by
  have h : (k : ℝ) * 2 ^ dfxS = ((k * dfxOne : Int) : ℝ) := by
    push_cast [dfxOne, dfxS]
    norm_num
  constructor <;> simp [ofInt, pt, h]

/-- `min` soundness. -/
theorem mem_min {a b : DIval} {x y : ℝ} (ha : x ∈ a) (hb : y ∈ b) :
    Min.min x y ∈ a.min b := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  have hxy : Min.min x y * 2 ^ dfxS = Min.min (x * 2 ^ dfxS) (y * 2 ^ dfxS) := by
    rcases le_total x y with h | h
    · rw [min_eq_left h, min_eq_left (mul_le_mul_of_nonneg_right h (by positivity))]
    · rw [min_eq_right h, min_eq_right (mul_le_mul_of_nonneg_right h (by positivity))]
  constructor <;> simp only [DIval.min] <;> push_cast <;> rw [hxy]
  · exact le_min (min_le_of_left_le ha1) (min_le_of_right_le hb1)
  · exact le_min (min_le_of_left_le ha2) (min_le_of_right_le hb2)

/-- `max` soundness. -/
theorem mem_max {a b : DIval} {x y : ℝ} (ha : x ∈ a) (hb : y ∈ b) :
    Max.max x y ∈ a.max b := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  have hxy : Max.max x y * 2 ^ dfxS = Max.max (x * 2 ^ dfxS) (y * 2 ^ dfxS) := by
    rcases le_total x y with h | h
    · rw [max_eq_right h, max_eq_right (mul_le_mul_of_nonneg_right h (by positivity))]
    · rw [max_eq_left h, max_eq_left (mul_le_mul_of_nonneg_right h (by positivity))]
  constructor <;> simp only [DIval.max] <;> push_cast <;> rw [hxy]
  · exact max_le_max ha1 hb1
  · exact max_le_max ha2 hb2

/-- The lower endpoint of `abs` is nonnegative. -/
private lemma abs_lo_nonneg (a : DIval) : 0 ≤ a.abs.lo := by
  simp only [DIval.abs, DIval.neg]
  split_ifs with h1 h2
  · exact h1
  · change 0 ≤ -a.hi
    omega
  · exact le_rfl

/-- `abs` soundness: `|x| ∈ a.abs`. -/
theorem mem_abs {a : DIval} {x : ℝ} (ha : x ∈ a) : |x| ∈ a.abs := by
  obtain ⟨h1, h2⟩ := ha
  have h2pos : (0 : ℝ) < 2 ^ dfxS := by positivity
  have habs : |x| * 2 ^ dfxS = |x * 2 ^ dfxS| := by
    rw [abs_mul, abs_of_pos h2pos]
  simp only [DIval.abs]
  split_ifs with hp hn
  · have hx : (0 : ℝ) ≤ x * 2 ^ dfxS :=
      le_trans (by exact_mod_cast hp) h1
    constructor <;> rw [habs, abs_of_nonneg hx] <;> assumption
  · have hx : x * 2 ^ dfxS ≤ 0 :=
      h2.trans (by exact_mod_cast hn)
    constructor <;> simp only [DIval.neg] <;> push_cast <;>
      rw [habs, abs_of_nonpos hx] <;> linarith
  · constructor
    · rw [habs]; simp [abs_nonneg]
    · rw [habs]
      push_cast
      rcases abs_cases (x * 2 ^ dfxS) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he]
      · exact le_max_of_le_right h2
      · exact le_max_of_le_left (by linarith)

/-- Hull soundness (left injection). -/
theorem mem_hull_left {a b : DIval} {x : ℝ} (ha : x ∈ a) : x ∈ a.hull b := by
  obtain ⟨h1, h2⟩ := ha
  constructor <;> simp only [hull] <;> push_cast
  · exact le_trans (min_le_left _ _) h1
  · exact le_trans h2 (le_max_left _ _)

/-- Hull soundness (right injection). -/
theorem mem_hull_right {a b : DIval} {y : ℝ} (hb : y ∈ b) : y ∈ a.hull b := by
  obtain ⟨h1, h2⟩ := hb
  constructor <;> simp only [hull] <;> push_cast
  · exact le_trans (min_le_right _ _) h1
  · exact le_trans h2 (le_max_right _ _)

/-- `pos` soundness: the positive part `max x 0` lies in `a.pos`. -/
theorem mem_pos {a : DIval} {x : ℝ} (ha : x ∈ a) : Max.max x 0 ∈ a.pos := by
  obtain ⟨h1, h2⟩ := ha
  have hxy : Max.max x 0 * 2 ^ dfxS = Max.max (x * 2 ^ dfxS) 0 := by
    rcases le_total x 0 with h | h
    · have hz : x * 2 ^ dfxS ≤ 0 := by
        have := mul_le_mul_of_nonneg_right h (show (0 : ℝ) ≤ 2 ^ dfxS by positivity)
        simpa using this
      rw [max_eq_right h, zero_mul, max_eq_right hz]
    · rw [max_eq_left h, max_eq_left (mul_nonneg h (by positivity))]
  constructor <;> simp only [pos] <;> push_cast <;> rw [hxy]
  · exact max_le_max h1 le_rfl
  · exact max_le_max h2 le_rfl

/-- `half` soundness: `x / 2 ∈ a.half`. -/
theorem mem_half {a : DIval} {x : ℝ} (ha : x ∈ a) : x / 2 ∈ a.half := by
  obtain ⟨h1, h2⟩ := ha
  have h2' : x / 2 * 2 ^ dfxS * 2 = x * 2 ^ dfxS := by ring
  constructor <;> simp only [half]
  · refine le_of_mul_le_mul_right ?_ (by norm_num : (0 : ℝ) < 2)
    calc (fshr a.lo 1 : ℝ) * 2 ≤ (a.lo : ℝ) := by
          have := fshr_le a.lo 1; norm_num at this ⊢; linarith
      _ ≤ x / 2 * 2 ^ dfxS * 2 := by rw [h2']; exact h1
  · refine le_of_mul_le_mul_right ?_ (by norm_num : (0 : ℝ) < 2)
    calc x / 2 * 2 ^ dfxS * 2 = x * 2 ^ dfxS := h2'
      _ ≤ (a.hi : ℝ) := h2
      _ ≤ (cshr a.hi 1 : ℝ) * 2 := by
          have := le_cshr a.hi 1; norm_num at this ⊢; linarith

/-- `clamp1` soundness: clamping is sound on values in `[-1, 1]`. -/
theorem mem_clamp1 {a : DIval} {x : ℝ} (ha : x ∈ a) (hx : |x| ≤ 1) :
    x ∈ a.clamp1 := by
  obtain ⟨h1, h2⟩ := ha
  obtain ⟨hxl, hxr⟩ := abs_le.mp hx
  have h2pos : (0 : ℝ) < 2 ^ dfxS := by positivity
  constructor <;> simp only [clamp1] <;> push_cast [dfxOne, dfxS] <;> norm_num
  · constructor
    · exact_mod_cast h1
    · nlinarith
  · constructor
    · exact_mod_cast h2
    · nlinarith

/-! ### Multiplication and squaring -/

/-- For `w` of unknown sign and `p ≤ c ≤ q`, `w·c` is below one of the two
endpoint products. -/
private lemma mul_le_max_ends {w p q c : ℝ} (h1 : p ≤ c) (h2 : c ≤ q) :
    w * c ≤ Max.max (w * p) (w * q) := by
  rcases le_total 0 w with hw | hw
  · exact le_max_of_le_right (mul_le_mul_of_nonneg_left h2 hw)
  · exact le_max_of_le_left (mul_le_mul_of_nonpos_left h1 hw)

/-- For `w` of unknown sign and `p ≤ c ≤ q`, `w·c` is above one of the two
endpoint products. -/
private lemma min_ends_le_mul {w p q c : ℝ} (h1 : p ≤ c) (h2 : c ≤ q) :
    Min.min (w * p) (w * q) ≤ w * c := by
  rcases le_total 0 w with hw | hw
  · exact min_le_of_left_le (mul_le_mul_of_nonneg_left h1 hw)
  · exact min_le_of_right_le (mul_le_mul_of_nonpos_left h2 hw)

/-- A product of two reals confined to boxes lies between the min and the max
of the four corner products. -/
private lemma corner_bounds {A1 A2 B1 B2 u v : ℝ}
    (ha1 : A1 ≤ u) (ha2 : u ≤ A2) (hb1 : B1 ≤ v) (hb2 : v ≤ B2) :
    Min.min (Min.min (A1 * B1) (A1 * B2)) (Min.min (A2 * B1) (A2 * B2)) ≤ u * v ∧
    u * v ≤ Max.max (Max.max (A1 * B1) (A1 * B2)) (Max.max (A2 * B1) (A2 * B2)) := by
  have e1 : A1 * B1 = B1 * A1 := mul_comm _ _
  have e2 : A2 * B1 = B1 * A2 := mul_comm _ _
  have e3 : A1 * B2 = B2 * A1 := mul_comm _ _
  have e4 : A2 * B2 = B2 * A2 := mul_comm _ _
  constructor
  · calc Min.min (Min.min (A1 * B1) (A1 * B2)) (Min.min (A2 * B1) (A2 * B2))
        = Min.min (Min.min (A1 * B1) (A2 * B1)) (Min.min (A1 * B2) (A2 * B2)) :=
          min_min_min_comm _ _ _ _
      _ ≤ Min.min (u * B1) (u * B2) := by
          refine min_le_min ?_ ?_
          · rw [e1, e2, mul_comm u B1]; exact min_ends_le_mul ha1 ha2
          · rw [e3, e4, mul_comm u B2]; exact min_ends_le_mul ha1 ha2
      _ ≤ u * v := min_ends_le_mul hb1 hb2
  · calc u * v ≤ Max.max (u * B1) (u * B2) := mul_le_max_ends hb1 hb2
      _ ≤ Max.max (Max.max (A1 * B1) (A2 * B1)) (Max.max (A1 * B2) (A2 * B2)) := by
          refine max_le_max ?_ ?_
          · rw [e1, e2, mul_comm u B1]; exact mul_le_max_ends ha1 ha2
          · rw [e3, e4, mul_comm u B2]; exact mul_le_max_ends ha1 ha2
      _ = Max.max (Max.max (A1 * B1) (A1 * B2)) (Max.max (A2 * B1) (A2 * B2)) :=
          max_max_max_comm _ _ _ _

/-- `mul` soundness. -/
theorem mem_mul {a b : DIval} {x y : ℝ} (ha : x ∈ a) (hb : y ∈ b) :
    x * y ∈ a.mul b := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨hmn, hmx⟩ := corner_bounds ha1 ha2 hb1 hb2
  have h2pos : (0 : ℝ) < 2 ^ dfxS := by positivity
  have hprod : x * 2 ^ dfxS * (y * 2 ^ dfxS) = x * y * 2 ^ dfxS * 2 ^ dfxS := by ring
  rw [hprod] at hmn hmx
  constructor <;> simp only [DIval.mul]
  · refine le_of_mul_le_mul_right ?_ h2pos
    calc (fshr (Min.min (Min.min (a.lo * b.lo) (a.lo * b.hi))
            (Min.min (a.hi * b.lo) (a.hi * b.hi))) dfxS : ℝ) * 2 ^ dfxS
        ≤ ((Min.min (Min.min (a.lo * b.lo) (a.lo * b.hi))
            (Min.min (a.hi * b.lo) (a.hi * b.hi)) : Int) : ℝ) := fshr_le _ _
      _ ≤ x * y * 2 ^ dfxS * 2 ^ dfxS := by push_cast; exact hmn
  · refine le_of_mul_le_mul_right ?_ h2pos
    calc x * y * 2 ^ dfxS * 2 ^ dfxS
        ≤ ((Max.max (Max.max (a.lo * b.lo) (a.lo * b.hi))
            (Max.max (a.hi * b.lo) (a.hi * b.hi)) : Int) : ℝ) := by push_cast; exact hmx
      _ ≤ (cshr (Max.max (Max.max (a.lo * b.lo) (a.lo * b.hi))
            (Max.max (a.hi * b.lo) (a.hi * b.hi))) dfxS : ℝ) * 2 ^ dfxS := le_cshr _ _

/-- `sq` soundness: `x² ∈ a.sq`. -/
theorem mem_sq {a : DIval} {x : ℝ} (ha : x ∈ a) : x ^ 2 ∈ a.sq := by
  obtain ⟨h1, h2⟩ := mem_abs ha
  have hlo : (0 : ℝ) ≤ (a.abs.lo : ℝ) := by exact_mod_cast abs_lo_nonneg a
  have h2pos : (0 : ℝ) < 2 ^ dfxS := by positivity
  have hu : (0 : ℝ) ≤ |x| * 2 ^ dfxS := by positivity
  have hval : |x| * 2 ^ dfxS * (|x| * 2 ^ dfxS) = x ^ 2 * 2 ^ dfxS * 2 ^ dfxS := by
    calc |x| * 2 ^ dfxS * (|x| * 2 ^ dfxS) = |x| ^ 2 * (2 ^ dfxS * 2 ^ dfxS) := by ring
      _ = x ^ 2 * 2 ^ dfxS * 2 ^ dfxS := by rw [sq_abs]; ring
  constructor <;> simp only [DIval.sq]
  · refine le_of_mul_le_mul_right ?_ h2pos
    calc (fshr (a.abs.lo * a.abs.lo) dfxS : ℝ) * 2 ^ dfxS
        ≤ ((a.abs.lo * a.abs.lo : Int) : ℝ) := fshr_le _ _
      _ ≤ x ^ 2 * 2 ^ dfxS * 2 ^ dfxS := by rw [← hval]; push_cast; nlinarith
  · refine le_of_mul_le_mul_right ?_ h2pos
    calc x ^ 2 * 2 ^ dfxS * 2 ^ dfxS
        ≤ ((a.abs.hi * a.abs.hi : Int) : ℝ) := by rw [← hval]; push_cast; nlinarith
      _ ≤ (cshr (a.abs.hi * a.abs.hi) dfxS : ℝ) * 2 ^ dfxS := le_cshr _ _

/-! ### Square root -/

/-- Structural unfolding of `sqrtI`. -/
private lemma sqrtI_eq (a : DIval) : a.sqrtI =
    ⟨(Nat.sqrt ((Max.max a.lo 0).toNat <<< dfxS) : Int),
     if Nat.sqrt ((Max.max a.hi 0).toNat <<< dfxS) *
        Nat.sqrt ((Max.max a.hi 0).toNat <<< dfxS) =
        (Max.max a.hi 0).toNat <<< dfxS
     then (Nat.sqrt ((Max.max a.hi 0).toNat <<< dfxS) : Int)
     else (Nat.sqrt ((Max.max a.hi 0).toNat <<< dfxS) : Int) + 1⟩ := rfl

/-- `sqrtI` soundness, clamped form: for any `x ∈ a`, the square root of the
positive part `max x 0` lies in `a.sqrtI`. -/
theorem mem_sqrtI_max {a : DIval} {x : ℝ} (ha : x ∈ a) :
    Real.sqrt (Max.max x 0) ∈ a.sqrtI := by
  obtain ⟨h1, h2⟩ := ha
  have h2pos : (0 : ℝ) < 2 ^ dfxS := by positivity
  -- the scaled argument
  have hkey : Real.sqrt (Max.max x 0) * 2 ^ dfxS =
      Real.sqrt (Max.max (x * 2 ^ dfxS) 0 * 2 ^ dfxS) := by
    have hmm : Max.max (x * 2 ^ dfxS) 0 * 2 ^ dfxS =
        Max.max x 0 * (2 ^ dfxS * 2 ^ dfxS) := by
      rcases le_total x 0 with h | h
      · have hz : x * 2 ^ dfxS ≤ 0 := by
          have := mul_le_mul_of_nonneg_right h (show (0 : ℝ) ≤ 2 ^ dfxS by positivity)
          simpa using this
        rw [max_eq_right h, max_eq_right hz]; ring
      · rw [max_eq_left h, max_eq_left (mul_nonneg h h2pos.le)]; ring
    rw [hmm, Real.sqrt_mul (le_max_right x 0), Real.sqrt_mul_self h2pos.le]
  -- lower endpoint
  have hLcast : (((Max.max a.lo 0).toNat : ℕ) : ℝ) = Max.max (a.lo : ℝ) 0 := by
    have h0 : ((Max.max a.lo 0).toNat : ℤ) = Max.max a.lo 0 :=
      Int.toNat_of_nonneg (le_max_right a.lo 0)
    have h1 : (((Max.max a.lo 0).toNat : ℤ) : ℝ) = ((Max.max a.lo 0 : ℤ) : ℝ) := by
      rw [h0]
    push_cast at h1
    exact h1
  have hHcast : (((Max.max a.hi 0).toNat : ℕ) : ℝ) = Max.max (a.hi : ℝ) 0 := by
    have h0 : ((Max.max a.hi 0).toNat : ℤ) = Max.max a.hi 0 :=
      Int.toNat_of_nonneg (le_max_right a.hi 0)
    have h1 : (((Max.max a.hi 0).toNat : ℤ) : ℝ) = ((Max.max a.hi 0 : ℤ) : ℝ) := by
      rw [h0]
    push_cast at h1
    exact h1
  -- shifted arguments and their casts
  have hLshift : (((Max.max a.lo 0).toNat <<< dfxS : ℕ) : ℝ) =
      Max.max (a.lo : ℝ) 0 * 2 ^ dfxS := by
    rw [Nat.shiftLeft_eq]
    push_cast
    rw [hLcast]
  have hHshift : (((Max.max a.hi 0).toNat <<< dfxS : ℕ) : ℝ) =
      Max.max (a.hi : ℝ) 0 * 2 ^ dfxS := by
    rw [Nat.shiftLeft_eq]
    push_cast
    rw [hHcast]
  -- lower endpoint
  have hlow : ((Nat.sqrt ((Max.max a.lo 0).toNat <<< dfxS) : ℕ) : ℝ) ≤
      Real.sqrt (Max.max (x * 2 ^ dfxS) 0 * 2 ^ dfxS) := by
    refine le_trans Real.nat_sqrt_le_real_sqrt (Real.sqrt_le_sqrt ?_)
    rw [hLshift]
    exact mul_le_mul_of_nonneg_right (max_le_max h1 le_rfl) h2pos.le
  -- upper bound against the un-rounded root
  have hup : Real.sqrt (Max.max (x * 2 ^ dfxS) 0 * 2 ^ dfxS) ≤
      Real.sqrt (((Max.max a.hi 0).toNat <<< dfxS : ℕ) : ℝ) := by
    refine Real.sqrt_le_sqrt ?_
    rw [hHshift]
    exact mul_le_mul_of_nonneg_right (max_le_max h2 le_rfl) h2pos.le
  rw [sqrtI_eq]
  set L : ℕ := (Max.max a.lo 0).toNat <<< dfxS with hLdef
  set N : ℕ := (Max.max a.hi 0).toNat <<< dfxS with hNdef
  constructor
  · -- the `.lo` component
    rw [hkey]
    exact_mod_cast hlow
  · -- the `.hi` component: split on whether the root is exact
    rw [hkey]
    split_ifs with hexact
    · have hroot : Real.sqrt ((N : ℕ) : ℝ) = ((Nat.sqrt N : ℕ) : ℝ) := by
        have hc : ((N : ℕ) : ℝ) = ((Nat.sqrt N : ℕ) : ℝ) * ((Nat.sqrt N : ℕ) : ℝ) := by
          rw [← Nat.cast_mul, hexact]
        rw [hc]
        exact Real.sqrt_mul_self (Nat.cast_nonneg _)
      push_cast
      rw [← hroot]
      exact hup
    · push_cast
      exact hup.trans Real.real_sqrt_le_nat_sqrt_succ

/-- `sqrtI` soundness on nonnegative inputs. -/
theorem mem_sqrtI {a : DIval} {x : ℝ} (ha : x ∈ a) (h0 : 0 ≤ x) :
    Real.sqrt x ∈ a.sqrtI := by
  have := mem_sqrtI_max ha
  rwa [max_eq_left h0] at this

/-- `norm2` soundness: `√(x² + y²) ∈ norm2 a b`. -/
theorem mem_norm2 {a b : DIval} {x y : ℝ} (hx : x ∈ a) (hy : y ∈ b) :
    Real.sqrt (x ^ 2 + y ^ 2) ∈ norm2 a b :=
  mem_sqrtI (mem_add (mem_sq hx) (mem_sq hy)) (by positivity)

/-! ### π -/

/-- `piI` encloses π. -/
theorem mem_piI : Real.pi ∈ piI := by
  have hgt := Real.pi_gt_d20
  have hlt := Real.pi_lt_d20
  have h2 : (2 : ℝ) ^ dfxS = 72057594037927936 := by norm_num [dfxS]
  constructor <;> simp only [piI, piLo] <;> rw [h2] <;> push_cast <;> nlinarith

/-- `piHalfI` encloses π/2. -/
theorem mem_piHalfI : Real.pi / 2 ∈ piHalfI := by
  have hgt := Real.pi_gt_d20
  have hlt := Real.pi_lt_d20
  have h2 : (2 : ℝ) ^ dfxS = 72057594037927936 := by norm_num [dfxS]
  constructor <;> simp only [piHalfI, pi2Lo] <;> rw [h2] <;> push_cast <;> nlinarith

/-- `⟨pi4Lo, pi4Lo + 1⟩` encloses π/4. -/
theorem mem_piQuarter : Real.pi / 4 ∈ (⟨pi4Lo, pi4Lo + 1⟩ : DIval) := by
  have hgt := Real.pi_gt_d20
  have hlt := Real.pi_lt_d20
  have h2 : (2 : ℝ) ^ dfxS = 72057594037927936 := by norm_num [dfxS]
  constructor <;> simp only [pi4Lo] <;> rw [h2] <;> push_cast <;> nlinarith

/-! ### The alternating Horner scheme -/

/-- Real reference value of the alternating Horner scheme:
`hornerAltR u [r₀, r₁, …] = r₀ - u·(r₁ - u·(…))`. -/
noncomputable def hornerAltR (u : ℝ) : List ℝ → ℝ
  | [] => 0
  | r :: rest => r - u * hornerAltR u rest

/-- `hornerAlt` soundness: if `u ∈ x2` and each real coefficient `rᵢ` lies in
the mantissa enclosure `[cᵢ, cᵢ + 1]`, the Horner value is enclosed. -/
private theorem mem_hornerAlt {x2 : DIval} {u : ℝ} (hu : u ∈ x2) :
    ∀ (cs : List Int) (rs : List ℝ),
      List.Forall₂ (fun c r => r ∈ (⟨c, c + 1⟩ : DIval)) cs rs →
      hornerAltR u rs ∈ hornerAlt x2 cs := by
  intro cs
  induction cs with
  | nil =>
    intro rs h
    cases h
    constructor <;> simp [hornerAlt, hornerAltR, pt]
  | cons c cs' ih =>
    intro rs h
    cases h with
    | cons hcr htail =>
      rename_i r rs'
      cases cs' with
      | nil =>
        cases htail
        have hr : hornerAltR u [r] = r := by simp [hornerAltR]
        rw [hr]
        exact hcr
      | cons c' cs'' =>
        cases htail with
        | cons hcr' htail' =>
          rename_i r' rs''
          have hv : hornerAltR u (r :: r' :: rs'') =
              r - u * hornerAltR u (r' :: rs'') := rfl
          have hi : hornerAlt x2 (c :: c' :: cs'') =
              DIval.sub ⟨c, c + 1⟩ (DIval.mul x2 (hornerAlt x2 (c' :: cs''))) := rfl
          rw [hv, hi]
          exact mem_sub hcr (mem_mul hu (ih _ (List.Forall₂.cons hcr' htail')))

/-- A mantissa coefficient enclosure `[c, c + 1]` contains `r` iff the scaled
value sits between the endpoints. -/
private lemma mem_coeff {c : Int} {r : ℝ} (h1 : (c : ℝ) ≤ r * 2 ^ dfxS)
    (h2 : r * 2 ^ dfxS ≤ (c : ℝ) + 1) : r ∈ (⟨c, c + 1⟩ : DIval) :=
  ⟨h1, by push_cast; linarith⟩

/-- Real coefficients `1/k!`, `k = 3, 5, …, 17`, matching `sinCoeffs`. -/
private noncomputable def sinR : List ℝ :=
  [(6 : ℝ)⁻¹, (120 : ℝ)⁻¹, (5040 : ℝ)⁻¹, (362880 : ℝ)⁻¹, (39916800 : ℝ)⁻¹,
   (6227020800 : ℝ)⁻¹, (1307674368000 : ℝ)⁻¹, (355687428096000 : ℝ)⁻¹]

/-- Real coefficients `1/k!`, `k = 2, 4, …, 18`, matching `cosCoeffs`. -/
private noncomputable def cosR : List ℝ :=
  [(2 : ℝ)⁻¹, (24 : ℝ)⁻¹, (720 : ℝ)⁻¹, (40320 : ℝ)⁻¹, (3628800 : ℝ)⁻¹,
   (479001600 : ℝ)⁻¹, (87178291200 : ℝ)⁻¹, (20922789888000 : ℝ)⁻¹,
   (6402373705728000 : ℝ)⁻¹]

/-- The integer sin coefficients enclose the real ones. -/
private lemma sinCoeffs_forall₂ :
    List.Forall₂ (fun c r => r ∈ (⟨c, c + 1⟩ : DIval)) sinCoeffs sinR := by
  simp only [sinCoeffs, sinR]
  exact .cons (mem_coeff (by norm_num [dfxS]) (by norm_num [dfxS]))
    (.cons (mem_coeff (by norm_num [dfxS]) (by norm_num [dfxS]))
    (.cons (mem_coeff (by norm_num [dfxS]) (by norm_num [dfxS]))
    (.cons (mem_coeff (by norm_num [dfxS]) (by norm_num [dfxS]))
    (.cons (mem_coeff (by norm_num [dfxS]) (by norm_num [dfxS]))
    (.cons (mem_coeff (by norm_num [dfxS]) (by norm_num [dfxS]))
    (.cons (mem_coeff (by norm_num [dfxS]) (by norm_num [dfxS]))
    (.cons (mem_coeff (by norm_num [dfxS]) (by norm_num [dfxS])) .nil)))))))

/-- The integer cos coefficients enclose the real ones. -/
private lemma cosCoeffs_forall₂ :
    List.Forall₂ (fun c r => r ∈ (⟨c, c + 1⟩ : DIval)) cosCoeffs cosR := by
  simp only [cosCoeffs, cosR]
  exact .cons (mem_coeff (by norm_num [dfxS]) (by norm_num [dfxS]))
    (.cons (mem_coeff (by norm_num [dfxS]) (by norm_num [dfxS]))
    (.cons (mem_coeff (by norm_num [dfxS]) (by norm_num [dfxS]))
    (.cons (mem_coeff (by norm_num [dfxS]) (by norm_num [dfxS]))
    (.cons (mem_coeff (by norm_num [dfxS]) (by norm_num [dfxS]))
    (.cons (mem_coeff (by norm_num [dfxS]) (by norm_num [dfxS]))
    (.cons (mem_coeff (by norm_num [dfxS]) (by norm_num [dfxS]))
    (.cons (mem_coeff (by norm_num [dfxS]) (by norm_num [dfxS]))
    (.cons (mem_coeff (by norm_num [dfxS]) (by norm_num [dfxS])) .nil))))))))

/-! ### Taylor tail bounds for sin and cos -/

/-- Factorials grow at least geometrically along even steps:
`m! · 2ⁿ ≤ (2n + m)!` (cf. `Nat.factorial_mul_pow_le_factorial`). -/
private lemma factorial_le_two_pow_mul {m : ℕ} (hm : 1 ≤ m) (n : ℕ) :
    m.factorial * 2 ^ n ≤ (2 * n + m).factorial :=
  calc m.factorial * 2 ^ n
      ≤ m.factorial * (m + 1) ^ n :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) n)
    _ ≤ (m + n).factorial := Nat.factorial_mul_pow_le_factorial
    _ ≤ (2 * n + m).factorial := Nat.factorial_le (by omega)

/-- Tail bound for an alternating-series enclosure: the whole tail beyond
index `k` is bounded by twice the first omitted term's crude bound
`|x|^(2k+p) / (2k+p)!`. -/
private lemma abs_tail_le {x : ℝ} (hx1 : |x| ≤ 1) {f : ℕ → ℝ} {S : ℝ} (k p : ℕ)
    (hkp : 1 ≤ 2 * k + p) (hsum : HasSum f S)
    (habs : ∀ n, |f n| = |x| ^ (2 * n + p) / ((2 * n + p).factorial : ℝ)) :
    |S - ∑ n ∈ Finset.range k, f n| ≤
      2 * (|x| ^ (2 * k + p) / ((2 * k + p).factorial : ℝ)) := by
  set B : ℝ := |x| ^ (2 * k + p) / ((2 * k + p).factorial : ℝ) with hB
  have hshift : HasSum (fun n => f (n + k)) (S - ∑ n ∈ Finset.range k, f n) :=
    (hasSum_nat_add_iff' k).mpr hsum
  have hterm : ∀ n : ℕ, |f (n + k)| ≤ B * (1 / 2) ^ n := by
    intro n
    have hidx : 2 * (n + k) + p = 2 * n + (2 * k + p) := by ring
    have hfac : ((2 * k + p).factorial : ℝ) * 2 ^ n ≤
        ((2 * n + (2 * k + p)).factorial : ℝ) := by
      exact_mod_cast factorial_le_two_pow_mul hkp n
    have hpow : |x| ^ (2 * n + (2 * k + p)) ≤ |x| ^ (2 * k + p) := by
      rw [pow_add]
      have h1 : |x| ^ (2 * n) ≤ 1 := pow_le_one₀ (abs_nonneg x) hx1
      nlinarith [pow_nonneg (abs_nonneg x) (2 * k + p),
        pow_nonneg (abs_nonneg x) (2 * n)]
    have hstep : |x| ^ (2 * n + (2 * k + p)) /
        ((2 * n + (2 * k + p)).factorial : ℝ) ≤
        |x| ^ (2 * k + p) / (((2 * k + p).factorial : ℝ) * 2 ^ n) :=
      div_le_div₀ (by positivity) hpow (by positivity) hfac
    calc |f (n + k)| = |x| ^ (2 * n + (2 * k + p)) /
          ((2 * n + (2 * k + p)).factorial : ℝ) := by rw [habs (n + k), hidx]
      _ ≤ |x| ^ (2 * k + p) / (((2 * k + p).factorial : ℝ) * 2 ^ n) := hstep
      _ = B * (1 / 2) ^ n := by
          rw [hB, div_pow, one_pow, div_mul_div_comm, mul_one]
  have hgeo : HasSum (fun n : ℕ => B * (1 / 2) ^ n) (B * 2) := by
    have h := hasSum_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    have h2 : ((1 : ℝ) - 1 / 2)⁻¹ = 2 := by norm_num
    rw [h2] at h
    exact h.mul_left B
  have hup : S - ∑ n ∈ Finset.range k, f n ≤ B * 2 :=
    hasSum_le (fun n => (le_abs_self _).trans (hterm n)) hshift hgeo
  have hdn : -(B * 2) ≤ S - ∑ n ∈ Finset.range k, f n :=
    hasSum_le (fun n => (neg_le_neg (hterm n)).trans (neg_abs_le _)) hgeo.neg hshift
  have := abs_le.mpr ⟨hdn, hup⟩
  linarith [this]

/-- The absolute value of a sin-series term. -/
private lemma abs_sin_term (x : ℝ) (n : ℕ) :
    |(-1 : ℝ) ^ n * x ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)| =
      |x| ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) := by
  rw [abs_div, abs_mul, abs_pow, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    Nat.abs_cast]

/-- The absolute value of a cos-series term. -/
private lemma abs_cos_term (x : ℝ) (n : ℕ) :
    |(-1 : ℝ) ^ n * x ^ (2 * n) / ((2 * n).factorial : ℝ)| =
      |x| ^ (2 * n) / ((2 * n).factorial : ℝ) := by
  rw [abs_div, abs_mul, abs_pow, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    Nat.abs_cast]

-- (pi4Lo + 64 + 1) / 2^56 < 0.786 < π/4 + 2⁻⁷; any constant strictly
-- between works.
/-- Truncation error of the degree-17 sin polynomial on `|x| ≤ 0.786`:
below one output ulp. -/
private lemma sin_tail_bound {x : ℝ} (hx : |x| ≤ 0.786) :
    |Real.sin x - ∑ n ∈ Finset.range 9,
        (-1 : ℝ) ^ n * x ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)| ≤
      ((2 : ℝ) ^ dfxS)⁻¹ := by
  have hx1 : |x| ≤ 1 := hx.trans (by norm_num)
  have h := abs_tail_le hx1 9 1 (by norm_num) (Real.hasSum_sin x) (abs_sin_term x)
  refine h.trans ?_
  have hxp : |x| ^ (2 * 9 + 1) ≤ (0.786 : ℝ) ^ 19 := by
    calc |x| ^ (2 * 9 + 1) = |x| ^ 19 := by norm_num
      _ ≤ (0.786 : ℝ) ^ 19 := pow_le_pow_left₀ (abs_nonneg x) hx 19
  have hfac : ((2 * 9 + 1).factorial : ℝ) = 121645100408832000 := by
    norm_num [Nat.factorial]
  rw [hfac]
  rw [show ((2 : ℝ) ^ dfxS)⁻¹ = (72057594037927936 : ℝ)⁻¹ by norm_num [dfxS]]
  nlinarith [hxp]

/-- Truncation error of the degree-18 cos polynomial on `|x| ≤ 0.786`:
below one output ulp. -/
private lemma cos_tail_bound {x : ℝ} (hx : |x| ≤ 0.786) :
    |Real.cos x - ∑ n ∈ Finset.range 10,
        (-1 : ℝ) ^ n * x ^ (2 * n) / ((2 * n).factorial : ℝ)| ≤
      ((2 : ℝ) ^ dfxS)⁻¹ := by
  have hx1 : |x| ≤ 1 := hx.trans (by norm_num)
  have h := abs_tail_le hx1 10 0 (by norm_num) (Real.hasSum_cos x) (abs_cos_term x)
  refine h.trans ?_
  have hxp : |x| ^ (2 * 10 + 0) ≤ (0.786 : ℝ) ^ 20 := by
    calc |x| ^ (2 * 10 + 0) = |x| ^ 20 := by norm_num
      _ ≤ (0.786 : ℝ) ^ 20 := pow_le_pow_left₀ (abs_nonneg x) hx 20
  have hfac : ((2 * 10 + 0).factorial : ℝ) = 2432902008176640000 := by
    norm_num [Nat.factorial]
  rw [hfac]
  rw [show ((2 : ℝ) ^ dfxS)⁻¹ = (72057594037927936 : ℝ)⁻¹ by norm_num [dfxS]]
  nlinarith [hxp]

/-- The degree-17 sin Taylor sum in Horner form. -/
private lemma sum_sin_poly (x : ℝ) :
    ∑ n ∈ Finset.range 9,
        (-1 : ℝ) ^ n * x ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) =
      x * (1 - x ^ 2 * hornerAltR (x ^ 2) sinR) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hornerAltR, sinR]
  norm_num [Nat.factorial]
  ring

/-- The degree-18 cos Taylor sum in Horner form. -/
private lemma sum_cos_poly (x : ℝ) :
    ∑ n ∈ Finset.range 10,
        (-1 : ℝ) ^ n * x ^ (2 * n) / ((2 * n).factorial : ℝ) =
      1 - x ^ 2 * hornerAltR (x ^ 2) cosR := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hornerAltR, cosR]
  norm_num [Nat.factorial]
  ring

/-! ### Trig cores -/

/-- `ofInt 1` contains the real number `1`. -/
private lemma one_mem_ofInt : (1 : ℝ) ∈ ofInt 1 := by
  simpa using mem_ofInt 1

/-- Values of intervals within the validated mantissa range `±(pi4Lo + 64)`
are bounded by `0.786` in absolute value. -/
private lemma abs_le_of_mem_range {X : DIval} {x : ℝ} (hx : x ∈ X)
    (hlo : -(pi4Lo + 64) ≤ X.lo) (hhi : X.hi ≤ pi4Lo + 64) : |x| ≤ 0.786 := by
  obtain ⟨h1, h2⟩ := hx
  have h2pos : (0 : ℝ) < 2 ^ dfxS := by positivity
  have hlo' : (-56593902016227586 : ℝ) ≤ x * 2 ^ dfxS := by
    refine le_trans ?_ h1
    have h : (-56593902016227586 : ℝ) = ((-(pi4Lo + 64) : Int) : ℝ) := by
      norm_num [pi4Lo]
    rw [h]
    exact_mod_cast hlo
  have hhi' : x * 2 ^ dfxS ≤ (56593902016227586 : ℝ) := by
    refine le_trans h2 ?_
    have h : (56593902016227586 : ℝ) = ((pi4Lo + 64 : Int) : ℝ) := by
      norm_num [pi4Lo]
    rw [h]
    exact_mod_cast hhi
  rw [abs_le]
  constructor
  · refine le_of_mul_le_mul_right ?_ h2pos
    calc (-0.786 : ℝ) * 2 ^ dfxS ≤ -56593902016227586 := by norm_num [dfxS]
      _ ≤ x * 2 ^ dfxS := hlo'
  · refine le_of_mul_le_mul_right ?_ h2pos
    calc x * 2 ^ dfxS ≤ 56593902016227586 := hhi'
      _ ≤ 0.786 * 2 ^ dfxS := by norm_num [dfxS]

/-- `sinCore` soundness: on the validated mantissa range, `sin x ∈ sinCore X`
for every `x ∈ X`. -/
theorem mem_sinCore {X : DIval} {x : ℝ} (hx : x ∈ X)
    (hlo : -(pi4Lo + 64) ≤ X.lo) (hhi : X.hi ≤ pi4Lo + 64) :
    Real.sin x ∈ sinCore X := by
  have hxb := abs_le_of_mem_range hx hlo hhi
  have hpoly : x * (1 - x ^ 2 * hornerAltR (x ^ 2) sinR) ∈
      DIval.mul X (DIval.sub (ofInt 1)
        (DIval.mul (DIval.sq X) (hornerAlt (DIval.sq X) sinCoeffs))) :=
    mem_mul hx (mem_sub one_mem_ofInt (mem_mul (mem_sq hx)
      (mem_hornerAlt (mem_sq hx) sinCoeffs sinR sinCoeffs_forall₂)))
  obtain ⟨hp1, hp2⟩ := hpoly
  have htail := sin_tail_bound hxb
  rw [sum_sin_poly] at htail
  obtain ⟨ht1, ht2⟩ := abs_le.mp htail
  have h2pos : (0 : ℝ) < 2 ^ dfxS := by positivity
  have hcancel : ((2 : ℝ) ^ dfxS)⁻¹ * 2 ^ dfxS = 1 := inv_mul_cancel₀ h2pos.ne'
  have hd1 := mul_le_mul_of_nonneg_right ht1 h2pos.le
  rw [neg_mul, hcancel, sub_mul] at hd1
  have hd2 := mul_le_mul_of_nonneg_right ht2 h2pos.le
  rw [hcancel, sub_mul] at hd2
  constructor <;> simp only [sinCore] <;> push_cast
  · linarith [hp1, hd1]
  · linarith [hp2, hd2]

/-- `cosCore` soundness: on the validated mantissa range, `cos x ∈ cosCore X`
for every `x ∈ X`. -/
theorem mem_cosCore {X : DIval} {x : ℝ} (hx : x ∈ X)
    (hlo : -(pi4Lo + 64) ≤ X.lo) (hhi : X.hi ≤ pi4Lo + 64) :
    Real.cos x ∈ cosCore X := by
  have hxb := abs_le_of_mem_range hx hlo hhi
  have hpoly : (1 : ℝ) - x ^ 2 * hornerAltR (x ^ 2) cosR ∈
      DIval.sub (ofInt 1)
        (DIval.mul (DIval.sq X) (hornerAlt (DIval.sq X) cosCoeffs)) :=
    mem_sub one_mem_ofInt (mem_mul (mem_sq hx)
      (mem_hornerAlt (mem_sq hx) cosCoeffs cosR cosCoeffs_forall₂))
  obtain ⟨hp1, hp2⟩ := hpoly
  have htail := cos_tail_bound hxb
  rw [sum_cos_poly] at htail
  obtain ⟨ht1, ht2⟩ := abs_le.mp htail
  have h2pos : (0 : ℝ) < 2 ^ dfxS := by positivity
  have hcancel : ((2 : ℝ) ^ dfxS)⁻¹ * 2 ^ dfxS = 1 := inv_mul_cancel₀ h2pos.ne'
  have hd1 := mul_le_mul_of_nonneg_right ht1 h2pos.le
  rw [neg_mul, hcancel, sub_mul] at hd1
  have hd2 := mul_le_mul_of_nonneg_right ht2 h2pos.le
  rw [hcancel, sub_mul] at hd2
  constructor <;> simp only [cosCore] <;> push_cast
  · linarith [hp1, hd1]
  · linarith [hp2, hd2]

/-! ### Argument reduction and `sincos` -/

/-- `mul (ofInt k) ⟨m, m+1⟩` computed exactly for `0 ≤ k`, `0 ≤ m`. -/
private lemma mul_ofInt_nonneg {k m : Int} (hk : 0 ≤ k) (_hm : 0 ≤ m) :
    DIval.mul (ofInt k) ⟨m, m + 1⟩ = ⟨k * m, k * (m + 1)⟩ := by
  have h2 : ((2 : Int) ^ dfxS) ≠ 0 := by norm_num
  have hone : dfxOne = (2 : Int) ^ dfxS := by norm_num [dfxOne, dfxS]
  have e1 : k * dfxOne * m = k * m * 2 ^ dfxS := by rw [hone]; ring
  have e2 : k * dfxOne * (m + 1) = k * (m + 1) * 2 ^ dfxS := by rw [hone]; ring
  have hle : k * m * 2 ^ dfxS ≤ k * (m + 1) * 2 ^ dfxS := by
    have hkm : k * m ≤ k * (m + 1) := by nlinarith
    exact mul_le_mul_of_nonneg_right hkm (by positivity)
  simp only [DIval.mul, ofInt, pt, e1, e2, min_self, max_self,
    min_eq_left hle, max_eq_right hle]
  simp only [DIval.mk.injEq]
  constructor
  · rw [hone, Int.mul_fdiv_cancel _ h2]
  · rw [hone, ← neg_mul, Int.mul_fdiv_cancel _ h2, neg_neg]

/-- `mul (ofInt k) ⟨m, m+1⟩` computed exactly for `k < 0`, `0 ≤ m`. -/
private lemma mul_ofInt_neg {k m : Int} (hk : k < 0) (_hm : 0 ≤ m) :
    DIval.mul (ofInt k) ⟨m, m + 1⟩ = ⟨k * (m + 1), k * m⟩ := by
  have h2 : ((2 : Int) ^ dfxS) ≠ 0 := by norm_num
  have hone : dfxOne = (2 : Int) ^ dfxS := by norm_num [dfxOne, dfxS]
  have e1 : k * dfxOne * m = k * m * 2 ^ dfxS := by rw [hone]; ring
  have e2 : k * dfxOne * (m + 1) = k * (m + 1) * 2 ^ dfxS := by rw [hone]; ring
  have hle : k * (m + 1) * 2 ^ dfxS ≤ k * m * 2 ^ dfxS := by
    have hkm : k * (m + 1) ≤ k * m := by nlinarith
    exact mul_le_mul_of_nonneg_right hkm (by positivity)
  simp only [DIval.mul, ofInt, pt, e1, e2, min_self, max_self,
    min_eq_right hle, max_eq_left hle]
  simp only [DIval.mk.injEq]
  constructor
  · rw [hone, Int.mul_fdiv_cancel _ h2]
  · rw [hone, ← neg_mul, Int.mul_fdiv_cancel _ h2, neg_neg]

/-- Exact endpoints of the residual interval `t - k·(π/2)`. -/
private lemma kpi2Residual_eq (t k : Int) :
    kpi2Residual t k = if 0 ≤ k then ⟨t - k * (pi2Lo + 1), t - k * pi2Lo⟩
      else (⟨t - k * pi2Lo, t - k * (pi2Lo + 1)⟩ : DIval) := by
  rcases (by omega : 0 ≤ k ∨ k < 0) with hk | hk
  · rw [if_pos hk]
    simp only [kpi2Residual]
    rw [mul_ofInt_nonneg hk (by norm_num [pi2Lo])]
    simp only [DIval.sub, pt]
  · rw [if_neg (not_le.mpr hk)]
    simp only [kpi2Residual]
    rw [mul_ofInt_neg hk (by norm_num [pi2Lo])]
    simp only [DIval.sub, pt]

/-- One `adjustK` step is the identity when the residual is already in range. -/
private lemma adjustK_of_in_range (t : Int) (fuel : Nat) (k : Int)
    (h1 : ¬((kpi2Residual t k).hi > pi4Lo + 64))
    (h2 : ¬((kpi2Residual t k).lo < -(pi4Lo + 64))) :
    adjustK t (fuel + 1) k = k := by
  simp only [adjustK]
  rw [if_neg h1, if_neg h2]

/-- For `|t| ≤ 64·2^56`, the initial quadrant estimate `k₀` already puts the
residual in the validated core range, so `adjustK` returns it unchanged. -/
lemma sincos_range {t : Int} (ht : |t| ≤ 64 * dfxOne) :
    adjustK t 8 ((t + pi4Lo).fdiv pi2Lo) = (t + pi4Lo).fdiv pi2Lo ∧
    -(pi4Lo + 64) ≤ (kpi2Residual t ((t + pi4Lo).fdiv pi2Lo)).lo ∧
    (kpi2Residual t ((t + pi4Lo).fdiv pi2Lo)).hi ≤ pi4Lo + 64 := by
  obtain ⟨ht1, ht2⟩ := abs_le.mp ht
  have hone : dfxOne = 72057594037927936 := rfl
  have hpi2 : pi2Lo = 113187804032455044 := rfl
  have hpi4 : pi4Lo = 56593902016227522 := rfl
  rw [hone] at ht1 ht2
  set k0 := (t + pi4Lo).fdiv pi2Lo with hk0def
  have hk0 : k0 = (t + 56593902016227522) / 113187804032455044 := by
    rw [hk0def, Int.fdiv_eq_ediv_of_nonneg _ (by norm_num [pi2Lo]), hpi2, hpi4]
  have hbounds : -(pi4Lo + 64) ≤ (kpi2Residual t k0).lo ∧
      (kpi2Residual t k0).hi ≤ pi4Lo + 64 := by
    rcases (by omega : 0 ≤ k0 ∨ k0 < 0) with hsgn | hsgn
    · have he : kpi2Residual t k0 = ⟨t - k0 * (pi2Lo + 1), t - k0 * pi2Lo⟩ := by
        rw [kpi2Residual_eq, if_pos hsgn]
      rw [he]
      constructor
      · change -(pi4Lo + 64) ≤ t - k0 * (pi2Lo + 1)
        rw [hpi2, hpi4]
        omega
      · change t - k0 * pi2Lo ≤ pi4Lo + 64
        rw [hpi2, hpi4]
        omega
    · have he : kpi2Residual t k0 = ⟨t - k0 * pi2Lo, t - k0 * (pi2Lo + 1)⟩ := by
        rw [kpi2Residual_eq, if_neg (not_le.mpr hsgn)]
      rw [he]
      constructor
      · change -(pi4Lo + 64) ≤ t - k0 * pi2Lo
        rw [hpi2, hpi4]
        omega
      · change t - k0 * (pi2Lo + 1) ≤ pi4Lo + 64
        rw [hpi2, hpi4]
        omega
  exact ⟨adjustK_of_in_range t 7 k0 (not_lt.mpr hbounds.2) (not_lt.mpr hbounds.1),
    hbounds.1, hbounds.2⟩

/-- Reduce a sin argument shift by an integer multiple of π/2 modulo 4. -/
private lemma sin_shift (r : ℝ) (k : ℤ) :
    Real.sin (r + (k : ℝ) * (Real.pi / 2)) =
      Real.sin (r + ((k % 4 : ℤ) : ℝ) * (Real.pi / 2)) := by
  have h : (k : ℝ) = 4 * ((k / 4 : ℤ) : ℝ) + ((k % 4 : ℤ) : ℝ) := by
    exact_mod_cast congrArg (fun n : ℤ => (n : ℝ)) (Int.mul_ediv_add_emod k 4).symm
  have harg : r + (k : ℝ) * (Real.pi / 2) =
      (r + ((k % 4 : ℤ) : ℝ) * (Real.pi / 2)) + ((k / 4 : ℤ) : ℝ) * (2 * Real.pi) := by
    rw [h]; ring
  rw [harg, Real.sin_add_int_mul_two_pi]

/-- Reduce a cos argument shift by an integer multiple of π/2 modulo 4. -/
private lemma cos_shift (r : ℝ) (k : ℤ) :
    Real.cos (r + (k : ℝ) * (Real.pi / 2)) =
      Real.cos (r + ((k % 4 : ℤ) : ℝ) * (Real.pi / 2)) := by
  have h : (k : ℝ) = 4 * ((k / 4 : ℤ) : ℝ) + ((k % 4 : ℤ) : ℝ) := by
    exact_mod_cast congrArg (fun n : ℤ => (n : ℝ)) (Int.mul_ediv_add_emod k 4).symm
  have harg : r + (k : ℝ) * (Real.pi / 2) =
      (r + ((k % 4 : ℤ) : ℝ) * (Real.pi / 2)) + ((k / 4 : ℤ) : ℝ) * (2 * Real.pi) := by
    rw [h]; ring
  rw [harg, Real.cos_add_int_mul_two_pi]

/-- `sincos` soundness: for `|t| ≤ 64·2^56`, `sincos t` encloses the sine and
cosine of the angle `t·2^-56`. -/
theorem mem_sincos {t : Int} (ht : |t| ≤ 64 * dfxOne) :
    Real.sin ((t : ℝ) / 2 ^ dfxS) ∈ (sincos t).1 ∧
    Real.cos ((t : ℝ) / 2 ^ dfxS) ∈ (sincos t).2 := by
  obtain ⟨hadj, hblo, hbhi⟩ := sincos_range ht
  set k0 := (t + pi4Lo).fdiv pi2Lo with hk0def
  set θ : ℝ := (t : ℝ) / 2 ^ dfxS with hθ
  set r : ℝ := θ - (k0 : ℝ) * (Real.pi / 2) with hr
  set X := kpi2Residual t k0 with hX
  have hres : r ∈ X :=
    mem_sub (mem_pt t) (mem_mul (mem_ofInt k0) mem_piHalfI)
  have hsin : Real.sin r ∈ sinCore X := mem_sinCore hres hblo hbhi
  have hcos : Real.cos r ∈ cosCore X := mem_cosCore hres hblo hbhi
  have hθeq : θ = r + (k0 : ℝ) * (Real.pi / 2) := by rw [hr]; ring
  have hj0 : 0 ≤ k0 % 4 := Int.emod_nonneg k0 (by norm_num)
  have hj4 : k0 % 4 < 4 := Int.emod_lt_of_pos k0 (by norm_num)
  have hcases : k0 % 4 = 0 ∨ k0 % 4 = 1 ∨ k0 % 4 = 2 ∨ k0 % 4 = 3 := by omega
  rcases hcases with hc | hc | hc | hc
  · -- quadrant 0: (sin, cos) = (sin r, cos r)
    have htn : (k0 % 4).toNat = 0 := by rw [hc]; rfl
    have hsc : sincos t = (clamp1 (sinCore X), clamp1 (cosCore X)) := by
      simp only [sincos]
      rw [← hk0def, hadj, ← hX, htn]
      rfl
    have hs : Real.sin θ = Real.sin r := by
      rw [hθeq, sin_shift, hc]
      norm_num
    have hco : Real.cos θ = Real.cos r := by
      rw [hθeq, cos_shift, hc]
      norm_num
    rw [hsc, hs, hco]
    exact ⟨mem_clamp1 hsin (Real.abs_sin_le_one r),
      mem_clamp1 hcos (Real.abs_cos_le_one r)⟩
  · -- quadrant 1: (sin, cos) = (cos r, -sin r)
    have htn : (k0 % 4).toNat = 1 := by rw [hc]; rfl
    have hsc : sincos t = (clamp1 (cosCore X), clamp1 ((sinCore X).neg)) := by
      simp only [sincos]
      rw [← hk0def, hadj, ← hX, htn]
      rfl
    have harg : r + ((1 : ℤ) : ℝ) * (Real.pi / 2) = r + Real.pi / 2 := by
      push_cast; ring
    have hs : Real.sin θ = Real.cos r := by
      rw [hθeq, sin_shift, hc, harg, Real.sin_add_pi_div_two]
    have hco : Real.cos θ = -Real.sin r := by
      rw [hθeq, cos_shift, hc, harg, Real.cos_add_pi_div_two]
    rw [hsc, hs, hco]
    refine ⟨mem_clamp1 hcos (Real.abs_cos_le_one r), mem_clamp1 (mem_neg hsin) ?_⟩
    rw [abs_neg]
    exact Real.abs_sin_le_one r
  · -- quadrant 2: (sin, cos) = (-sin r, -cos r)
    have htn : (k0 % 4).toNat = 2 := by rw [hc]; rfl
    have hsc : sincos t = (clamp1 ((sinCore X).neg), clamp1 ((cosCore X).neg)) := by
      simp only [sincos]
      rw [← hk0def, hadj, ← hX, htn]
      rfl
    have harg : r + ((2 : ℤ) : ℝ) * (Real.pi / 2) = r + Real.pi := by
      push_cast; ring
    have hs : Real.sin θ = -Real.sin r := by
      rw [hθeq, sin_shift, hc, harg, Real.sin_add_pi]
    have hco : Real.cos θ = -Real.cos r := by
      rw [hθeq, cos_shift, hc, harg, Real.cos_add_pi]
    rw [hsc, hs, hco]
    refine ⟨mem_clamp1 (mem_neg hsin) ?_, mem_clamp1 (mem_neg hcos) ?_⟩
    · rw [abs_neg]; exact Real.abs_sin_le_one r
    · rw [abs_neg]; exact Real.abs_cos_le_one r
  · -- quadrant 3: (sin, cos) = (-cos r, sin r)
    have htn : (k0 % 4).toNat = 3 := by rw [hc]; rfl
    have hsc : sincos t = (clamp1 ((cosCore X).neg), clamp1 (sinCore X)) := by
      simp only [sincos]
      rw [← hk0def, hadj, ← hX, htn]
      rfl
    have harg : r + ((3 : ℤ) : ℝ) * (Real.pi / 2) = (r + Real.pi) + Real.pi / 2 := by
      push_cast; ring
    have hs : Real.sin θ = -Real.cos r := by
      rw [hθeq, sin_shift, hc, harg, Real.sin_add_pi_div_two, Real.cos_add_pi]
    have hco : Real.cos θ = Real.sin r := by
      rw [hθeq, cos_shift, hc, harg, Real.cos_add_pi_div_two, Real.sin_add_pi, neg_neg]
    rw [hsc, hs, hco]
    refine ⟨mem_clamp1 (mem_neg hcos) ?_, mem_clamp1 hsin (Real.abs_sin_le_one r)⟩
    rw [abs_neg]
    exact Real.abs_cos_le_one r

/-- `sincosIv` soundness: for any real angle `θ` enclosed by an interval `t`
within the `±64` range, `sincosIv t` encloses `(sin θ, cos θ)`. -/
theorem mem_sincosIv {t : DIval} {θ : ℝ} (hθ : θ ∈ t)
    (hlo : -(64 * dfxOne) ≤ t.lo) (hhi : t.hi ≤ 64 * dfxOne) :
    Real.sin θ ∈ (sincosIv t).1 ∧ Real.cos θ ∈ (sincosIv t).2 := by
  obtain ⟨h1, h2⟩ := hθ
  have h2pos : (0 : ℝ) < 2 ^ dfxS := by positivity
  have hone : dfxOne = 72057594037927936 := rfl
  have hlohi : t.lo ≤ t.hi := by
    have : (t.lo : ℝ) ≤ (t.hi : ℝ) := le_trans h1 h2
    exact_mod_cast this
  set m := t.lo + (t.hi - t.lo) / 2 with hm
  have hmlo : t.lo ≤ m := by omega
  have hmhi : m ≤ t.hi := by omega
  have hmabs : |m| ≤ 64 * dfxOne := by
    rw [hone] at hlo hhi ⊢
    rw [abs_le]
    omega
  obtain ⟨hsm, hcm⟩ := mem_sincos hmabs
  set μ : ℝ := (m : ℝ) / 2 ^ dfxS with hμ
  set rad := Max.max (t.hi - m) (m - t.lo) with hrad
  rcases hsc : sincos m with ⟨sm, cm⟩
  rw [hsc] at hsm hcm
  obtain ⟨hsm1, hsm2⟩ := hsm
  obtain ⟨hcm1, hcm2⟩ := hcm
  have hgoal : sincosIv t =
      (clamp1 ⟨sm.lo - rad, sm.hi + rad⟩, clamp1 ⟨cm.lo - rad, cm.hi + rad⟩) := by
    simp only [sincosIv]
    rw [← hm, ← hrad, hsc]
  -- distance from the midpoint mantissa
  have hradc : (rad : ℝ) = Max.max ((t.hi : ℝ) - (m : ℝ)) ((m : ℝ) - (t.lo : ℝ)) := by
    rw [hrad]
    push_cast
    ring_nf
  have hd : |θ * 2 ^ dfxS - (m : ℝ)| ≤ (rad : ℝ) := by
    rw [abs_sub_le_iff, hradc]
    constructor
    · exact le_max_of_le_left (by linarith)
    · exact le_max_of_le_right (by linarith)
  have hμm : μ * 2 ^ dfxS = (m : ℝ) := by
    rw [hμ]
    field_simp
  have habsmul : |θ - μ| * 2 ^ dfxS = |θ * 2 ^ dfxS - (m : ℝ)| := by
    rw [← hμm, ← sub_mul, abs_mul, abs_of_pos h2pos]
  -- Lipschitz transfer to sin and cos
  have hsL : |(Real.sin θ - Real.sin μ) * 2 ^ dfxS| ≤ (rad : ℝ) := by
    rw [abs_mul, abs_of_pos h2pos]
    calc |Real.sin θ - Real.sin μ| * 2 ^ dfxS
        ≤ |θ - μ| * 2 ^ dfxS :=
          mul_le_mul_of_nonneg_right (Real.abs_sin_sub_sin_le θ μ) h2pos.le
      _ = |θ * 2 ^ dfxS - (m : ℝ)| := habsmul
      _ ≤ (rad : ℝ) := hd
  have hcL : |(Real.cos θ - Real.cos μ) * 2 ^ dfxS| ≤ (rad : ℝ) := by
    rw [abs_mul, abs_of_pos h2pos]
    calc |Real.cos θ - Real.cos μ| * 2 ^ dfxS
        ≤ |θ - μ| * 2 ^ dfxS :=
          mul_le_mul_of_nonneg_right (Real.abs_cos_sub_cos_le θ μ) h2pos.le
      _ = |θ * 2 ^ dfxS - (m : ℝ)| := habsmul
      _ ≤ (rad : ℝ) := hd
  obtain ⟨hsA, hsB⟩ := abs_le.mp hsL
  obtain ⟨hcA, hcB⟩ := abs_le.mp hcL
  rw [hgoal]
  refine ⟨mem_clamp1 ⟨?_, ?_⟩ (Real.abs_sin_le_one θ),
    mem_clamp1 ⟨?_, ?_⟩ (Real.abs_cos_le_one θ)⟩
  · change ((sm.lo - rad : ℤ) : ℝ) ≤ Real.sin θ * 2 ^ dfxS
    push_cast
    nlinarith [hsm1, hsA]
  · change Real.sin θ * 2 ^ dfxS ≤ ((sm.hi + rad : ℤ) : ℝ)
    push_cast
    nlinarith [hsm2, hsB]
  · change ((cm.lo - rad : ℤ) : ℝ) ≤ Real.cos θ * 2 ^ dfxS
    push_cast
    nlinarith [hcm1, hcA]
  · change Real.cos θ * 2 ^ dfxS ≤ ((cm.hi + rad : ℤ) : ℝ)
    push_cast
    nlinarith [hcm2, hcB]

end DIval
end MoserWorm

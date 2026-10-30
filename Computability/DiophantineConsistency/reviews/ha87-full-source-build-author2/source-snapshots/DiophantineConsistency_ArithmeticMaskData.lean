import DiophantineConsistency.CurrentMaskData2011
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Matrix-free ℕ facts about the two standard 94517-bit masks, importable next
to Foundation. The low mask is identified with an explicit radix-`2^47` digit
list symbolically (a telescoping geometric identity, no evaluation of the
numeral); digit lookups and digit populations are finite facts about the 2011
standard digits. -/

namespace DiophantineConsistency.ArithmeticMaskData

open CurrentMasks2011

set_option Elab.async false

/-- The base-`b` repunit with `n` digits. -/
def G (b n : ℕ) : ℕ := Nat.ofDigits b (List.replicate n 1)

theorem G_succ (b n : ℕ) : G b (n+1) = 1 + b * G b n := by
  simp [G, List.replicate_succ, Nat.ofDigits_cons]

theorem G_zero (b : ℕ) : G b 0 = 0 := by simp [G]

theorem G_one (b : ℕ) : G b 1 = 1 := by simp [G]

theorem G_succ' (b n : ℕ) : G b (n+1) = G b n + b^n := by
  induction n with
  | zero => simp [G_succ, G_zero]
  | succ n ih =>
    conv_lhs => rw [G_succ, ih]
    conv_rhs => rw [G_succ, pow_succ]
    ring

theorem G_geom (b t n : ℕ) (hb : t + 2 = b) : (t+1) * G b n + 1 = b^n := by
  induction n with
  | zero => simp [G_zero]
  | succ n ih =>
    calc (t+1) * G b (n+1) + 1 = b * ((t+1) * G b n + 1) := by rw [G_succ, ← hb]; ring
      _ = b^(n+1) := by rw [ih, pow_succ, mul_comm]

theorem ofDigits_replicate_append (b n a : ℕ) (l : List ℕ) :
    Nat.ofDigits b (List.replicate n a ++ l) = a * G b n + b^n * Nat.ofDigits b l := by
  induction n with
  | zero => simp [G_zero]
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, Nat.ofDigits_cons, ih, G_succ, pow_succ]
    ring

theorem sum_range_pow (b n : ℕ) : (∑ j ∈ Finset.range n, b^j) = G b n := by
  induction n with
  | zero => simp [G_zero]
  | succ n ih => rw [Finset.sum_range_succ, ih, G_succ']

theorem sum_Ico_pow (b a n : ℕ) : (∑ j ∈ Finset.Ico a (a+n), b^j) = b^a * G b n := by
  rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left, ← sum_range_pow, Finset.mul_sum]
  simp only [pow_add]

theorem support_value :
    (∑ j ∈ lowSupport, radix^j) = G radix 951 + radix^960 * G radix 26 + radix^1004 := by
  have h1 := lowSupport_range_Ico_disjoint
  have h2 := lowSupport_marker_disjoint
  rw [lowSupport_def, Finset.sum_union h2, Finset.sum_union h1, Finset.sum_singleton,
    sum_range_pow, show (986:ℕ) = 960 + 26 by rfl, sum_Ico_pow]

/-- The low digit list with digit values `t` (support) and `t+1` (elsewhere). -/
def lowList (t : ℕ) : List ℕ :=
  List.replicate 951 t ++ (List.replicate 9 (t+1) ++
    (List.replicate 26 t ++ (List.replicate 18 (t+1) ++
      (List.replicate 1 t ++ (List.replicate 1006 (t+1) ++ [])))))

theorem lowList_identity (b t : ℕ) (hb : t + 2 = b) :
    Nat.ofDigits b (lowList t) + (G b 951 + b^960 * G b 26 + b^1004) + 1 = b^2011 := by
  simp only [lowList, ofDigits_replicate_append, Nat.ofDigits_nil, G_one]
  have h951 := G_geom b t 951 hb
  have h9 := G_geom b t 9 hb
  have h26 := G_geom b t 26 hb
  have h18 := G_geom b t 18 hb
  have h1006 := G_geom b t 1006 hb
  rw [show b^960 = b^951 * b^9 by ring, show b^1004 = b^951 * b^9 * b^26 * b^18 by ring,
    show b^2011 = b^951 * b^9 * b^26 * b^18 * b^1 * b^1006 by ring,
    ← h951, ← h9, ← h26, ← h18, ← h1006, pow_one, ← hb]
  ring

theorem radix_eq : radix = 2^47 := rfl

/-- The low mask digits: `2^47-2` on the support, `2^47-1` elsewhere. -/
def lowDigits : List ℕ := lowList (radix - 2)

theorem radix_pred : radix - 2 + 1 = radix - 1 := by norm_num [radix_eq]

theorem lowPort_ofDigits : lowPort = Nat.ofDigits radix lowDigits := by
  have hc := lowList_identity radix (radix - 2) (by norm_num [radix_eq])
  unfold lowPort LowMaskCoding.mask LowMaskCoding.supportValue
  rw [support_value]
  unfold lowDigits
  generalize G radix 951 + radix^960 * G radix 26 + radix^1004 = s at hc ⊢
  generalize Nat.ofDigits radix (lowList (radix - 2)) = x at hc ⊢
  generalize radix ^ 2011 = p at hc ⊢
  omega

theorem lowDigits_length : lowDigits.length = 2011 := by
  simp only [lowDigits, lowList, List.length_append, List.length_replicate, List.length_nil]

theorem getD_replicate_append (n a : ℕ) (l : List ℕ) (j d : ℕ) :
    (List.replicate n a ++ l).getD j d = if j < n then a else l.getD (j - n) d := by
  induction n generalizing j with
  | zero => simp
  | succ n ih =>
    cases j with
    | zero => simp [List.replicate_succ]
    | succ j =>
      simp only [List.replicate_succ, List.cons_append, List.getD_cons_succ, ih]
      split_ifs <;> first | rfl | omega | (congr 1; omega)

theorem lowDigits_getD (j : ℕ) (hj : j < 2011) :
    lowDigits.getD j 0 =
      if j < 951 ∨ (960 ≤ j ∧ j < 986) ∨ j = 1004 then radix - 2 else radix - 1 := by
  rw [← radix_pred]
  unfold lowDigits lowList
  simp only [getD_replicate_append, List.getD_nil]
  split_ifs <;> omega

theorem lowDigits_lt {x : ℕ} (hx : x ∈ lowDigits) : x < 2^47 := by
  simp only [lowDigits, lowList, List.mem_append, List.mem_replicate, List.not_mem_nil,
    or_false] at hx
  rw [radix_eq] at hx
  norm_num at hx ⊢
  omega

theorem highDigits_lt' {x : ℕ} (hx : x ∈ highDigits) : x < 2^47 := by
  simp only [highDigits, highPrefix, List.mem_append, List.mem_cons, List.mem_replicate,
    List.not_mem_nil, or_false] at hx
  norm_num at hx ⊢
  omega

theorem highDigits_length : highDigits.length = 2011 := by
  simp only [highDigits, highPrefix, List.length_append, List.length_replicate, List.length_nil,
    List.length_cons]

theorem highDigits_zero : highDigits.getD 0 0 = 4 := rfl

theorem highPort_ofDigits : highPort = Nat.ofDigits (2^47) highDigits := rfl

/-- Popcount with explicit fuel (structural). -/
def pcF : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f+1, n => n % 2 + pcF f (n / 2)

theorem low_population : (lowDigits.map (pcF 47)).sum = 93539 := by
  decide +kernel

theorem high_population : (highDigits.map (pcF 47)).sum = 978 := by
  decide +kernel

theorem digit_population :
    (lowDigits.map (pcF 47)).sum + (highDigits.map (pcF 47)).sum = 94517 := by
  rw [low_population, high_population]

end DiophantineConsistency.ArithmeticMaskData

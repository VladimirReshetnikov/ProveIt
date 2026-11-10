import DiophantineConsistency.Adm942.Adm942Kernel
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Radix-`2^47` column sums for the admissible942 local normalization

Generic arithmetic for `Adm942LocalNormalization`, with no numeral of the
size of `K`, `B` or the masks ever evaluated.

* `gs c n = Σ_{q<n} c q · ρ^q` is a radix sum whose "digits" `c q` may exceed
  `ρ = 2^47` (column sums of a product before carrying). If every column is at
  most `2^53` and the column just below `p` leaves room for the carry
  (`c (p-1) + 128 ≤ ρ`), then the actual radix digit `dig X p = X / ρ^p % ρ`
  of `X = gs c n` is the column `c p` itself (`dig_gs`): the whole carry
  arriving from below is less than `128`.
* `and_zero_of_dig`: two numbers whose radix digits are pairwise disjoint have
  `&&& = 0`; `dig_ofDigits` reads the digits of a digit list.
* `highDigit_cases`: the shape of every high-mask digit (one linear
  `decide +kernel` walk over the 4027-digit list).
* `colK cd q`: the column `q` of `K · Σ_f cd f ρ^f`, as a sum over the kernel
  terms (`K_mul`), with its value at every column the proof reads
  (`colK_low`, `colK_1991`, `colK_1992`, `colK_2997`, `colK_2998`,
  `colK_4003`, `colK_pad`, `colK_high`) and the mass bound `colK_le`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000

namespace Adm942LocalColumns
open DiophantineConsistency
open Adm942MaskData (radix radix_eq InSupport)
open scoped BigOperators

theorem radix_pos : 0 < radix := by rw [radix_eq]; norm_num

theorem radix_pow (e : ℕ) : radix ^ e = 2 ^ (47 * e) := by
  rw [radix_eq, ← pow_mul]

theorem radix_pow_pos (e : ℕ) : 0 < radix ^ e := pow_pos radix_pos e

/-! ## Radix sums with unbounded columns -/

/-- `Σ_{q<n} c q · ρ^q`. -/
def gs (c : ℕ → ℕ) (n : ℕ) : ℕ := ∑ q ∈ Finset.range n, c q * radix ^ q

theorem gs_zero (c : ℕ → ℕ) : gs c 0 = 0 := by
  simp only [gs, Finset.range_zero, Finset.sum_empty]

theorem gs_succ (c : ℕ → ℕ) (n : ℕ) : gs c (n + 1) = gs c n + c n * radix ^ n := by
  unfold gs; rw [Finset.sum_range_succ]

/-- Columns of at most `2^53` sum to less than `128` units of the next place. -/
theorem gs_lt_128 (c : ℕ → ℕ) : ∀ n : ℕ, (∀ q < n, c q ≤ 2 ^ 53) → gs c n < 128 * radix ^ n
  | 0, _ => by rw [gs_zero]; norm_num
  | n + 1, h => by
    have ih := gs_lt_128 c n (fun q hq => h q (by omega))
    have hc : c n * radix ^ n ≤ 2 ^ 53 * radix ^ n := Nat.mul_le_mul_right _ (h n (by omega))
    rw [gs_succ, pow_succ, show radix ^ n * radix = 140737488355328 * radix ^ n by
      rw [radix_eq]; ring]
    generalize radix ^ n = t at ih hc ⊢
    generalize c n * t = u at ih hc ⊢
    norm_num at hc ⊢
    omega

/-- The part below `p` of a radix sum stays below `ρ^p` when the column under
`p` leaves room for the carry. -/
theorem gs_lt_pow (c : ℕ → ℕ) (p : ℕ) (hp : 1 ≤ p) (hc : ∀ q < p, c q ≤ 2 ^ 53)
    (hlast : c (p - 1) + 128 ≤ radix) : gs c p < radix ^ p := by
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hlast
  have h1 := gs_lt_128 c k (fun q hq => hc q (by omega))
  have h2 : (c k + 128) * radix ^ k ≤ radix * radix ^ k := Nat.mul_le_mul_right _ hlast
  rw [gs_succ, pow_succ, mul_comm (radix ^ k) radix]
  rw [add_mul] at h2
  generalize radix ^ k = t at h1 h2 ⊢
  generalize c k * t = u at h1 h2 ⊢
  generalize radix * t = v at h1 h2 ⊢
  omega

theorem gs_split (c : ℕ → ℕ) (p m : ℕ) :
    gs c (p + 1 + m) = gs c p + radix ^ p * (c p + radix * gs (fun q => c (p + 1 + q)) m) := by
  unfold gs
  rw [Finset.sum_range_add, Finset.sum_range_succ, mul_add, Finset.mul_sum, Finset.mul_sum]
  have h : ∀ x ∈ Finset.range m, c (p + 1 + x) * radix ^ (p + 1 + x) =
      radix ^ p * (radix * (c (p + 1 + x) * radix ^ x)) := fun x _ => by
    rw [pow_add, pow_add, pow_one]; ring
  rw [Finset.sum_congr rfl h]
  ring

/-- Zero columns do not change a radix sum. -/
theorem gs_extend (c : ℕ → ℕ) (n m : ℕ) (h : ∀ q, n ≤ q → q < n + m → c q = 0) :
    gs c (n + m) = gs c n := by
  unfold gs
  rw [Finset.sum_range_add, Finset.sum_eq_zero (s := Finset.range m) (fun x hx => by
    rw [h (n + x) (by omega) (by have := Finset.mem_range.mp hx; omega), zero_mul]), add_zero]

theorem gs_extend' (c : ℕ → ℕ) (n N : ℕ) (hn : n ≤ N) (h : ∀ q, n ≤ q → q < N → c q = 0) :
    gs c N = gs c n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact gs_extend c n m h

/-- Split a radix sum at the place `p`. -/
theorem gs_split' (c : ℕ → ℕ) (p m : ℕ) :
    gs c (p + m) = gs c p + radix ^ p * gs (fun q => c (p + q)) m := by
  unfold gs
  rw [Finset.sum_range_add, Finset.mul_sum]
  refine congrArg (_ + ·) (Finset.sum_congr rfl (fun x _ => ?_))
  rw [pow_add]; ring

theorem gs_add (c d : ℕ → ℕ) (n : ℕ) : gs c n + gs d n = gs (fun q => c q + d q) n := by
  unfold gs
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun q _ => by ring)

theorem gs_congr (c d : ℕ → ℕ) (n : ℕ) (h : ∀ q < n, c q = d q) : gs c n = gs d n := by
  unfold gs
  exact Finset.sum_congr rfl (fun q hq => by rw [h q (Finset.mem_range.mp hq)])

/-- A radix sum whose columns vanish from `T` on is below `ρ^T`. -/
theorem gs_lt_top (c : ℕ → ℕ) (T m : ℕ) (hT : 1 ≤ T) (hc : ∀ q < T, c q ≤ 2 ^ 53)
    (hlast : c (T - 1) + 128 ≤ radix) (hz : ∀ q, T ≤ q → q < T + m → c q = 0) :
    gs c (T + m) < radix ^ T := by
  rw [gs_extend c T m hz]
  exact gs_lt_pow c T hT hc hlast

/-! ## Radix digits -/

/-- The radix-`2^47` digit of `X` at place `p`. -/
def dig (X p : ℕ) : ℕ := X / radix ^ p % radix

theorem dig_of_decomp (A d H p : ℕ) (hA : A < radix ^ p) (hd : d < radix) :
    dig (A + radix ^ p * (d + radix * H)) p = d := by
  unfold dig
  rw [Nat.add_mul_div_left _ _ (radix_pow_pos p), Nat.div_eq_of_lt hA, zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd]

/-- **The actual digit is the column.** -/
theorem dig_gs (c : ℕ → ℕ) (n p : ℕ) (hp : p < n) (hc : ∀ q < p, c q ≤ 2 ^ 53)
    (hlast : 1 ≤ p → c (p - 1) + 128 ≤ radix) (hcp : c p < radix) :
    dig (gs c n) p = c p := by
  obtain ⟨m, rfl⟩ : ∃ m, n = p + 1 + m := ⟨n - p - 1, by omega⟩
  rw [gs_split]
  apply dig_of_decomp _ _ _ _ _ hcp
  rcases Nat.eq_zero_or_pos p with h | h
  · subst h; rw [gs_zero, pow_zero]; norm_num
  · exact gs_lt_pow c p h hc (hlast h)

theorem dig_eq_zero_of_lt (X p : ℕ) (h : X < radix ^ p) : dig X p = 0 := by
  unfold dig; rw [Nat.div_eq_of_lt h, Nat.zero_mod]

theorem testBit_dig (x i : ℕ) : Nat.testBit x i = Nat.testBit (dig x (i / 47)) (i % 47) := by
  unfold dig
  rw [radix_pow, radix_eq, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  have h1 : i % 47 < 47 := Nat.mod_lt i (by norm_num)
  have h2 : i % 47 + 47 * (i / 47) = i := Nat.mod_add_div i 47
  simp only [h1, decide_true, Bool.true_and, h2]

/-- Digitwise disjoint numbers have disjoint bits. -/
theorem and_zero_of_dig (X M : ℕ) (h : ∀ p, dig X p &&& dig M p = 0) : X &&& M = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.zero_testBit, testBit_dig X i, testBit_dig M i, ← Nat.testBit_and,
    h, Nat.zero_testBit]

/-- The digits of a digit list. -/
theorem dig_ofDigits : ∀ (L : List ℕ) (p : ℕ), (∀ x ∈ L, x < radix) →
    dig (Nat.ofDigits radix L) p = L.getD p 0
  | [], p, _ => by simp only [dig, Nat.ofDigits, Nat.zero_div, Nat.zero_mod, List.getD_nil]
  | d :: L, p, h => by
    have hd : d < radix := h d (by simp)
    have ih := fun p => dig_ofDigits L p (fun x hx => h x (by simp [hx]))
    rw [Nat.ofDigits_cons]
    cases p with
    | zero =>
      simp only [dig, pow_zero, Nat.div_one, List.getD_cons_zero]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd]
    | succ p =>
      rw [List.getD_cons_succ, ← ih p]
      unfold dig
      rw [pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ radix_pos,
        Nat.div_eq_of_lt hd, zero_add]

/-! ## The high mask digits -/

/-- The admissible shape of one high-mask digit. -/
def hiOk (p d : ℕ) : Bool :=
  d == 0 || (p == 0 && d == 4) ||
  (((decide (960 ≤ p) && decide (p < 969)) || (decide (987 ≤ p) && decide (p < 995)) ||
    p == 1005) && d == 1) ||
  ((p == 1992 || p == 2998) && d == Adm942MaskData.mu) || decide (4004 ≤ p)

/-- A linear walk over a digit list. -/
def hiChk : ℕ → List ℕ → Bool
  | _, [] => true
  | i, d :: L => hiOk i d && hiChk (i + 1) L

theorem hiChk_spec : ∀ (L : List ℕ) (i : ℕ), hiChk i L = true →
    ∀ p, hiOk (i + p) (L.getD p 0) = true
  | [], i, _, p => by simp [hiOk]
  | d :: L, i, h, p => by
    simp only [hiChk, Bool.and_eq_true] at h
    cases p with
    | zero => simpa using h.1
    | succ p =>
      have := hiChk_spec L (i + 1) h.2 p
      rw [List.getD_cons_succ, show i + (p + 1) = i + 1 + p by omega]
      exact this

theorem hiChk_high : hiChk 0 Adm942MaskData.highDigits = true := by decide +kernel

/-- **The high-mask digits**: zero, the origin `4`, a copy test `1`, a clause
band `μ`, or a padding place `≥ 4004`. -/
theorem highDigit_cases (p : ℕ) :
    Adm942MaskData.highDigits.getD p 0 = 0 ∨ (p = 0 ∧ Adm942MaskData.highDigits.getD p 0 = 4) ∨
    (((960 ≤ p ∧ p < 969) ∨ (987 ≤ p ∧ p < 995) ∨ p = 1005) ∧
      Adm942MaskData.highDigits.getD p 0 = 1) ∨
    ((p = 1992 ∨ p = 2998) ∧ Adm942MaskData.highDigits.getD p 0 = Adm942MaskData.mu) ∨
    4004 ≤ p := by
  have h := hiChk_spec _ 0 hiChk_high p
  rw [zero_add] at h
  generalize Adm942MaskData.highDigits.getD p 0 = d at h ⊢
  simp only [hiOk, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  omega

theorem highPort_dig (p : ℕ) :
    dig Adm942MaskData.highPort p = Adm942MaskData.highDigits.getD p 0 := by
  rw [Adm942MaskData.highPort]
  exact dig_ofDigits _ p (fun x hx => by rw [radix_eq]; exact Adm942MaskData.highDigits_lt' hx)

/-! ## The columns of the kernel product -/

open Adm942Kernel (Term Entry exponent coefficient position)

/-- Column `q` of `K · Σ_f cd f ρ^f`. -/
def colK (cd : ℕ → ℕ) (q : ℕ) : ℕ :=
  ∑ t : Term, if exponent t ≤ q then coefficient t * cd (q - exponent t) else 0

theorem shift_sum (cd : ℕ → ℕ) (hcd : ∀ f, 1006 ≤ f → cd f = 0) (a e : ℕ) (he : e ≤ 4036) :
    (∑ q ∈ Finset.range 5042, (if e ≤ q then a * cd (q - e) else 0) * radix ^ q) =
      ∑ f ∈ Finset.range 1006, a * radix ^ e * (cd f * radix ^ f) := by
  obtain ⟨r, hr⟩ : ∃ r, 5042 = e + (1006 + r) := ⟨4036 - e, by omega⟩
  rw [hr, Finset.sum_range_add, Finset.sum_eq_zero (fun x hx => by
    rw [if_neg (by have := Finset.mem_range.mp hx; omega), zero_mul]), zero_add,
    Finset.sum_range_add, Finset.sum_eq_zero (s := Finset.range r) (fun x _ => by
      rw [if_pos (by omega), Nat.add_sub_cancel_left, hcd (1006 + x) (by omega), mul_zero,
        zero_mul]), add_zero]
  refine Finset.sum_congr rfl (fun f _ => ?_)
  rw [if_pos (by omega), Nat.add_sub_cancel_left, pow_add]
  ring

/-- **The kernel product as a column sum.** -/
theorem K_mul (cd : ℕ → ℕ) (hcd : ∀ f, 1006 ≤ f → cd f = 0) :
    Adm942Kernel.K * gs cd 1006 = gs (colK cd) 5042 := by
  unfold Adm942Kernel.K Adm942Kernel.rawWord gs colK
  rw [Finset.sum_mul_sum]
  simp only [Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [shift_sum cd hcd _ _ (Adm942Kernel.exponent_le t)]

theorem colK_le (cd : ℕ → ℕ) (hcd : ∀ f, cd f ≤ 1) (q : ℕ) : colK cd q ≤ 7659829036801887 := by
  rw [← Adm942Kernel.coefficient_mass]
  unfold colK
  refine Finset.sum_le_sum (fun t _ => ?_)
  split_ifs
  · calc coefficient t * cd (q - exponent t) ≤ coefficient t * 1 :=
          Nat.mul_le_mul_left _ (hcd _)
      _ = coefficient t := mul_one _
  · exact Nat.zero_le _

local notation "wt" => CurrentKernel2011.weight

/-- The five families of kernel terms. -/
theorem colK_split (cd : ℕ → ℕ) (q : ℕ) :
    colK cd q = (if 18 ≤ q then cd (q - 18) else 0) + (if 1005 ≤ q then cd (q - 1005) else 0) +
      (if 4036 ≤ q then cd (q - 4036) else 0) +
      ((∑ e : Entry, if 1992 - position e ≤ q then wt e * cd (q - (1992 - position e)) else 0) +
       (∑ e : Entry, if 2998 - position e ≤ q then wt e * cd (q - (2998 - position e)) else 0)) := by
  unfold colK
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fin.sum_univ_three]
  simp only [exponent, coefficient, one_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

theorem pos_le (e : Entry) : position e ≤ 985 := Adm942Kernel.position_le e

/-- Below the reflected bands only the bare `18` and `1005` copies act. -/
theorem colK_low (cd : ℕ → ℕ) (q : ℕ) (hq : q ≤ 1006) :
    colK cd q = (if 18 ≤ q then cd (q - 18) else 0) + (if 1005 ≤ q then cd (q - 1005) else 0) := by
  rw [colK_split, if_neg (show ¬ 4036 ≤ q by omega),
    Finset.sum_eq_zero (fun e _ => if_neg (by have := pos_le e; omega)),
    Finset.sum_eq_zero (fun e _ => if_neg (by have := pos_le e; omega))]
  simp only [add_zero]

/-- Column `1992`: the lower clause. -/
theorem colK_1992 (cd : ℕ → ℕ) (hz : ∀ f, ¬ InSupport f → cd f = 0) :
    colK cd 1992 = ∑ e : Entry, wt e * cd (position e) := by
  rw [colK_split, if_pos (by norm_num), if_pos (by norm_num), if_neg (by norm_num),
    hz _ (by unfold InSupport; omega), hz _ (by unfold InSupport; omega),
    Finset.sum_eq_zero (s := Finset.univ) (f := fun e : Entry =>
      if 2998 - position e ≤ 1992 then wt e * cd (1992 - (2998 - position e)) else 0)
      (fun e _ => if_neg (by have := pos_le e; omega))]
  simp only [zero_add, add_zero]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  have := pos_le e
  rw [if_pos (by omega), show 1992 - (1992 - position e) = position e by omega]

/-- Column `1991`, the predecessor of the lower clause. -/
theorem colK_1991 (cd : ℕ → ℕ) (hz : ∀ f, ¬ InSupport f → cd f = 0) :
    colK cd 1991 = ∑ e : Entry, if 1 ≤ position e then wt e * cd (position e - 1) else 0 := by
  rw [colK_split, if_pos (by norm_num), if_pos (by norm_num), if_neg (by norm_num),
    hz _ (by unfold InSupport; omega), hz _ (by unfold InSupport; omega),
    Finset.sum_eq_zero (s := Finset.univ) (f := fun e : Entry =>
      if 2998 - position e ≤ 1991 then wt e * cd (1991 - (2998 - position e)) else 0)
      (fun e _ => if_neg (by have := pos_le e; omega))]
  simp only [zero_add, add_zero]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  have := pos_le e
  by_cases h : 1 ≤ position e
  · rw [if_pos (by omega), if_pos h, show 1991 - (1992 - position e) = position e - 1 by omega]
  · rw [if_neg (by omega), if_neg h]

/-- Column `2998`: the upper clause. -/
theorem colK_2998 (cd : ℕ → ℕ) (hz : ∀ f, ¬ InSupport f → cd f = 0) :
    colK cd 2998 = ∑ e : Entry, wt e * cd (position e) := by
  rw [colK_split, if_pos (by norm_num), if_pos (by norm_num), if_neg (by norm_num),
    hz _ (by unfold InSupport; omega), hz _ (by unfold InSupport; omega),
    Finset.sum_eq_zero (s := Finset.univ) (f := fun e : Entry =>
      if 1992 - position e ≤ 2998 then wt e * cd (2998 - (1992 - position e)) else 0)
      (fun e _ => by
        have := pos_le e
        rw [if_pos (by omega), hz _ (by unfold InSupport; omega), mul_zero])]
  simp only [zero_add]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  have := pos_le e
  rw [if_pos (by omega), show 2998 - (2998 - position e) = position e by omega]

/-- Column `2997`: the predecessor of the upper clause, with the foreign pair `1005 − 0`. -/
theorem colK_2997 (cd : ℕ → ℕ) (hz : ∀ f, ¬ InSupport f → cd f = 0) :
    colK cd 2997 = (∑ e : Entry, wt e * cd (1005 + position e)) +
      ∑ e : Entry, if 1 ≤ position e then wt e * cd (position e - 1) else 0 := by
  rw [colK_split, if_pos (by norm_num), if_pos (by norm_num), if_neg (by norm_num),
    hz _ (by unfold InSupport; omega), hz _ (by unfold InSupport; omega)]
  simp only [zero_add]
  refine congrArg₂ (· + ·) ?_ ?_
  · refine Finset.sum_congr rfl (fun e _ => ?_)
    have := pos_le e
    rw [if_pos (by omega), show 2997 - (1992 - position e) = 1005 + position e by omega]
  · refine Finset.sum_congr rfl (fun e _ => ?_)
    have := pos_le e
    by_cases h : 1 ≤ position e
    · rw [if_pos (by omega), if_pos h, show 2997 - (2998 - position e) = position e - 1 by omega]
    · rw [if_neg (by omega), if_neg h]

/-- Column `4003`, the last product column. -/
theorem colK_4003 (cd : ℕ → ℕ) (hz : ∀ f, ¬ InSupport f → cd f = 0) :
    colK cd 4003 = ∑ e : Entry, wt e * cd (1005 + position e) := by
  rw [colK_split, if_pos (by norm_num), if_pos (by norm_num), if_neg (by norm_num),
    hz _ (by unfold InSupport; omega), hz _ (by unfold InSupport; omega),
    Finset.sum_eq_zero (s := Finset.univ) (f := fun e : Entry =>
      if 1992 - position e ≤ 4003 then wt e * cd (4003 - (1992 - position e)) else 0)
      (fun e _ => by
        have := pos_le e
        rw [if_pos (by omega), hz _ (by unfold InSupport; omega), mul_zero])]
  simp only [zero_add]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  have := pos_le e
  rw [if_pos (by omega), show 4003 - (2998 - position e) = 1005 + position e by omega]

/-- The padding columns `4004 ≤ q < 4027` vanish. -/
theorem colK_pad (cd : ℕ → ℕ) (hz : ∀ f, ¬ InSupport f → cd f = 0) (q : ℕ) (h1 : 4004 ≤ q)
    (h2 : q < 4027) : colK cd q = 0 := by
  rw [colK_split, if_pos (by omega), if_pos (by omega), if_neg (by omega),
    hz _ (by unfold InSupport; omega), hz _ (by unfold InSupport; omega),
    Finset.sum_eq_zero (fun e _ => by
      have := pos_le e
      rw [if_pos (by omega), hz _ (by unfold InSupport; omega), mul_zero]),
    Finset.sum_eq_zero (fun e _ => by
      have := pos_le e
      rw [if_pos (by omega), hz _ (by unfold InSupport; omega), mul_zero])]
  simp only [add_zero]

/-- Above `B` only the spatial copy `ρ^(L+9)` acts. -/
theorem colK_high (cd : ℕ → ℕ) (hz : ∀ f, ¬ InSupport f → cd f = 0) (q : ℕ) (h1 : 4027 ≤ q) :
    colK cd q = if 4036 ≤ q then cd (q - 4036) else 0 := by
  rw [colK_split, if_pos (by omega), if_pos (by omega),
    hz _ (by unfold InSupport; omega), hz _ (by unfold InSupport; omega),
    Finset.sum_eq_zero (fun e _ => by
      have := pos_le e
      rw [if_pos (by omega), hz _ (by unfold InSupport; omega), mul_zero]),
    Finset.sum_eq_zero (fun e _ => by
      have := pos_le e
      rw [if_pos (by omega), hz _ (by unfold InSupport; omega), mul_zero])]
  simp only [zero_add, add_zero]

/-- The foreign pair: only the Start selector sits at `1005 − 1005`. -/
theorem foreign_sum (cd : ℕ → ℕ) (hz : ∀ f, ¬ InSupport f → cd f = 0) :
    (∑ e : Entry, wt e * cd (1005 + position e)) = wt (Sum.inl 0) * cd 1005 := by
  rw [Finset.sum_eq_single (Sum.inl 0)]
  · rfl
  · intro e _ he
    have hp : position e ≠ 0 := fun h0 =>
      he (Adm942Kernel.position_injective (by rw [h0]; rfl))
    have := pos_le e
    rw [hz _ (by unfold InSupport; omega), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

end Adm942LocalColumns

#print axioms Adm942LocalColumns.dig_gs
#print axioms Adm942LocalColumns.and_zero_of_dig
#print axioms Adm942LocalColumns.highDigit_cases
#print axioms Adm942LocalColumns.K_mul
#print axioms Adm942LocalColumns.colK_le
#print axioms Adm942LocalColumns.colK_2997
#print axioms Adm942LocalColumns.foreign_sum

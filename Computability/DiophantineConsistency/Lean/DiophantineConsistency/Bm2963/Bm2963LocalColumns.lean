import DiophantineConsistency.Bm2963.Bm2963Kernel
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Radix-`2^47` column sums for the block-mask2963 local normalization

Generic arithmetic for `Bm2963LocalNormalization`, with no numeral of the
size of `K`, `B` or the masks ever evaluated: the block-mask2963 counterpart of
`Adm942LocalColumns`.

* `gs c n = Σ_{q<n} c q · ρ^q` is a radix sum whose "digits" `c q` may exceed
  `ρ = 2^47` (column sums of a product before carrying). If every column is at
  most `2^53` and the column just below `p` leaves room for the carry
  (`c (p-1) + 128 ≤ ρ`), then the actual radix digit `dig X p = X / ρ^p % ρ`
  of `X = gs c n` is the column `c p` itself (`dig_gs`): the whole carry
  arriving from below is less than `128`.
* `and_zero_of_dig`: two numbers whose radix digits are pairwise disjoint have
  `&&& = 0`; `dig_ofDigits` reads the digits of a digit list.
* `highDigit_cases`: the shape of every high-mask digit (one linear
  `decide +kernel` walk over the 2963-digit list): zero, the origin/padding
  digit `4` at `0..916`, a copy test `1`, or the clause digit `μ` at `1956`.
* `colK cd q`: the column `q` of `K · Σ_f cd f ρ^f`, as a sum over the kernel
  terms (`K_mul`), with its value at every column the proof reads
  (`colK_low` for `q ≤ 970`, `colK_lowband` for `971 ≤ q ≤ 1005`, where the
  single band contributes label weights only, `colK_1955`, `colK_1956`,
  `colK_2961`, `colK_2962`, `colK_high`) and the mass bound `colK_le`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000

namespace Bm2963LocalColumns
open DiophantineConsistency
open Bm2963MaskData (radix radix_eq InSupport)
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
  d == 0 || (decide (p ≤ 916) && d == 4) ||
  (((decide (960 ≤ p) && decide (p < 969)) || (decide (987 ≤ p) && decide (p < 995)) ||
    p == 1005) && d == 1) ||
  (p == 1956 && d == Bm2963MaskData.mu)

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

theorem hiChk_high : hiChk 0 Bm2963MaskData.highDigits = true := by decide +kernel

/-- **The high-mask digits**: zero, the origin/padding `4` at `0..916`, a copy
test `1`, or the clause digit `μ` at `1956`. -/
theorem highDigit_cases (p : ℕ) :
    Bm2963MaskData.highDigits.getD p 0 = 0 ∨
    (p ≤ 916 ∧ Bm2963MaskData.highDigits.getD p 0 = 4) ∨
    (((960 ≤ p ∧ p < 969) ∨ (987 ≤ p ∧ p < 995) ∨ p = 1005) ∧
      Bm2963MaskData.highDigits.getD p 0 = 1) ∨
    (p = 1956 ∧ Bm2963MaskData.highDigits.getD p 0 = Bm2963MaskData.mu) := by
  have h := hiChk_spec _ 0 hiChk_high p
  rw [zero_add] at h
  generalize Bm2963MaskData.highDigits.getD p 0 = d at h ⊢
  simp only [hiOk, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  omega

theorem highPort_dig (p : ℕ) :
    dig Bm2963MaskData.highPort p = Bm2963MaskData.highDigits.getD p 0 := by
  rw [Bm2963MaskData.highPort]
  exact dig_ofDigits _ p (fun x hx => by rw [radix_eq]; exact Bm2963MaskData.highDigits_lt' hx)

/-! ## The columns of the kernel product -/

open Bm2963Kernel (Term Entry exponent coefficient position)

/-- Column `q` of `K · Σ_f cd f ρ^f`. -/
def colK (cd : ℕ → ℕ) (q : ℕ) : ℕ :=
  ∑ t : Term, if exponent t ≤ q then coefficient t * cd (q - exponent t) else 0

theorem shift_sum (cd : ℕ → ℕ) (hcd : ∀ f, 1006 ≤ f → cd f = 0) (a e : ℕ) (he : e ≤ 2972) :
    (∑ q ∈ Finset.range 3978, (if e ≤ q then a * cd (q - e) else 0) * radix ^ q) =
      ∑ f ∈ Finset.range 1006, a * radix ^ e * (cd f * radix ^ f) := by
  obtain ⟨r, hr⟩ : ∃ r, 3978 = e + (1006 + r) := ⟨2972 - e, by omega⟩
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
    Bm2963Kernel.K * gs cd 1006 = gs (colK cd) 3978 := by
  unfold Bm2963Kernel.K Bm2963Kernel.rawWord gs colK
  rw [Finset.sum_mul_sum]
  simp only [Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [shift_sum cd hcd _ _ (Bm2963Kernel.exponent_le t)]

theorem colK_le (cd : ℕ → ℕ) (hcd : ∀ f, cd f ≤ 1) (q : ℕ) : colK cd q ≤ 3829914518400945 := by
  rw [← Bm2963Kernel.coefficient_mass]
  unfold colK
  refine Finset.sum_le_sum (fun t _ => ?_)
  split_ifs
  · calc coefficient t * cd (q - exponent t) ≤ coefficient t * 1 :=
          Nat.mul_le_mul_left _ (hcd _)
      _ = coefficient t := mul_one _
  · exact Nat.zero_le _

local notation "wt" => CurrentKernel2011.weight

/-- The four families of kernel terms. -/
theorem colK_split (cd : ℕ → ℕ) (q : ℕ) :
    colK cd q = (if 18 ≤ q then cd (q - 18) else 0) + (if 1005 ≤ q then cd (q - 1005) else 0) +
      (if 2972 ≤ q then cd (q - 2972) else 0) +
      (∑ e : Entry, if 1956 - position e ≤ q then wt e * cd (q - (1956 - position e)) else 0) := by
  unfold colK
  rw [Fintype.sum_sum_type, Fin.sum_univ_three]
  simp only [exponent, coefficient, one_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

theorem pos_le (e : Entry) : position e ≤ 985 := Bm2963Kernel.position_le e

/-- Below the reflected band only the bare `18` and `1005` copies act. -/
theorem colK_low (cd : ℕ → ℕ) (q : ℕ) (hq : q ≤ 970) :
    colK cd q = (if 18 ≤ q then cd (q - 18) else 0) + (if 1005 ≤ q then cd (q - 1005) else 0) := by
  rw [colK_split, if_neg (show ¬ 2972 ≤ q by omega),
    Finset.sum_eq_zero (fun e _ => if_neg (by have := pos_le e; omega))]
  simp only [add_zero]

/-- The band part of a column. -/
def bandK (cd : ℕ → ℕ) (q : ℕ) : ℕ :=
  ∑ e : Entry, if 1956 - position e ≤ q then wt e * cd (q - (1956 - position e)) else 0

/-- Fields `971..1005` also see the band, through label entries only. -/
theorem colK_lowband (cd : ℕ → ℕ) (q : ℕ) (hq : q ≤ 1005) :
    colK cd q = (if 18 ≤ q then cd (q - 18) else 0) + (if 1005 ≤ q then cd (q - 1005) else 0) +
      bandK cd q := by
  rw [colK_split, if_neg (show ¬ 2972 ≤ q by omega), add_zero]
  rfl

/-- Only label entries reach the fields up to `1005`, and every label weight is even. -/
theorem label_even (l : Fin 8 ⊕ (Fin 9 ⊕ (Fin 8 ⊕ Fin 9))) : wt (Sum.inr l) % 2 = 0 := by
  rcases l with j | j | j | j <;> simp only [CurrentKernel2011.weight] <;>
    exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by omega))

/-- The 34 label weights sum to `2^44 − 1024`. -/
theorem label_mass :
    (∑ l : Fin 8 ⊕ (Fin 9 ⊕ (Fin 8 ⊕ Fin 9)), wt (Sum.inr l)) = 17592186043392 := by
  have h := ArithmeticMaskKernel.entry_mass
  have hs := ArithmeticMaskKernel.selector_mass
  rw [Fintype.sum_sum_type] at h
  have e : (∑ i : Fin 942, wt (Sum.inl i)) = ∑ i : Fin 942, WangTiles942.selectorWeight
      (WangTiles942.tile i) :=
    Finset.sum_congr rfl (fun i _ => rfl)
  rw [e, hs] at h
  exact Nat.add_left_cancel (h.trans (by norm_num : (3829914518400942 : ℕ) =
    3812322332357550 + 17592186043392))

theorem bandK_low (cd : ℕ → ℕ) (hcd : ∀ f, cd f ≤ 1) (q : ℕ) (hq : q ≤ 1005) :
    bandK cd q % 2 = 0 ∧ bandK cd q ≤ 17592186043392 := by
  have hsel : ∀ i : Fin 942, (if 1956 - position (Sum.inl i) ≤ q then
      wt (Sum.inl i) * cd (q - (1956 - position (Sum.inl i))) else 0) = 0 := fun i =>
    if_neg (by
      have := i.isLt
      show ¬ 1956 - i.val ≤ q
      omega)
  unfold bandK
  rw [Fintype.sum_sum_type, Finset.sum_congr rfl (fun i _ => hsel i), Finset.sum_const_zero,
    zero_add]
  constructor
  · rw [Finset.sum_nat_mod, Finset.sum_eq_zero (fun l _ => by
      try dsimp only
      split_ifs
      · rw [Nat.mul_mod, label_even l, zero_mul, Nat.zero_mod]
      · rfl), Nat.zero_mod]
  · rw [← label_mass]
    refine Finset.sum_le_sum (fun l _ => ?_)
    try dsimp only
    split_ifs
    · calc wt (Sum.inr l) * cd _ ≤ wt (Sum.inr l) * 1 := Nat.mul_le_mul_left _ (hcd _)
        _ = wt (Sum.inr l) := mul_one _
    · exact Nat.zero_le _

/-- Column `1956`: the clause. -/
theorem colK_1956 (cd : ℕ → ℕ) (hz : ∀ f, ¬ InSupport f → cd f = 0) :
    colK cd 1956 = ∑ e : Entry, wt e * cd (position e) := by
  rw [colK_split, if_pos (by norm_num), if_pos (by norm_num), if_neg (by norm_num),
    hz _ (by unfold InSupport; omega), hz _ (by unfold InSupport; omega)]
  simp only [zero_add, add_zero]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  have := pos_le e
  rw [if_pos (by omega), show 1956 - (1956 - position e) = position e by omega]

/-- Column `1955`, the predecessor of the clause: the bare `1005` copy reads
`x_950` (south bit `8`). -/
theorem colK_1955 (cd : ℕ → ℕ) (hz : ∀ f, ¬ InSupport f → cd f = 0) :
    colK cd 1955 = cd 950 +
      ∑ e : Entry, if 1 ≤ position e then wt e * cd (position e - 1) else 0 := by
  rw [colK_split, if_pos (by norm_num : 18 ≤ 1955), if_pos (by norm_num : 1005 ≤ 1955),
    if_neg (by norm_num : ¬ 2972 ≤ 1955), show 1955 - 1005 = 950 from rfl,
    hz (1955 - 18) (by unfold InSupport; omega)]
  simp only [zero_add, add_zero]
  refine congrArg (cd 950 + ·) (Finset.sum_congr rfl (fun e _ => ?_))
  have := pos_le e
  by_cases h : 1 ≤ position e
  · rw [if_pos (by omega), if_pos h, show 1955 - (1956 - position e) = position e - 1 by omega]
  · rw [if_neg (by omega), if_neg h]

/-- Column `2961`, the last product column below `B`. -/
theorem colK_2961 (cd : ℕ → ℕ) (hz : ∀ f, ¬ InSupport f → cd f = 0) :
    colK cd 2961 = ∑ e : Entry, wt e * cd (1005 + position e) := by
  rw [colK_split, if_pos (by norm_num), if_pos (by norm_num), if_neg (by norm_num),
    hz _ (by unfold InSupport; omega), hz _ (by unfold InSupport; omega)]
  simp only [zero_add]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  have := pos_le e
  rw [if_pos (by omega), show 2961 - (1956 - position e) = 1005 + position e by omega]

/-- Column `2962` vanishes. -/
theorem colK_2962 (cd : ℕ → ℕ) (hz : ∀ f, ¬ InSupport f → cd f = 0) : colK cd 2962 = 0 := by
  rw [colK_split, if_pos (by norm_num), if_pos (by norm_num), if_neg (by norm_num),
    hz _ (by unfold InSupport; omega), hz _ (by unfold InSupport; omega),
    Finset.sum_eq_zero (fun e _ => by
      have := pos_le e
      rw [if_pos (by omega), hz _ (by unfold InSupport; omega), mul_zero])]
  all_goals simp only [add_zero]

/-- Above `B` only the spatial copy `ρ^(L+9)` acts. -/
theorem colK_high (cd : ℕ → ℕ) (hz : ∀ f, ¬ InSupport f → cd f = 0) (q : ℕ) (h1 : 2963 ≤ q) :
    colK cd q = if 2972 ≤ q then cd (q - 2972) else 0 := by
  rw [colK_split, if_pos (by omega), if_pos (by omega),
    hz _ (by unfold InSupport; omega), hz _ (by unfold InSupport; omega),
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
      he (Bm2963Kernel.position_injective (by rw [h0]; rfl))
    have := pos_le e
    rw [hz _ (by unfold InSupport; omega), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

end Bm2963LocalColumns

#print axioms Bm2963LocalColumns.dig_gs
#print axioms Bm2963LocalColumns.and_zero_of_dig
#print axioms Bm2963LocalColumns.highDigit_cases
#print axioms Bm2963LocalColumns.K_mul
#print axioms Bm2963LocalColumns.colK_le
#print axioms Bm2963LocalColumns.bandK_low
#print axioms Bm2963LocalColumns.colK_1955
#print axioms Bm2963LocalColumns.foreign_sum

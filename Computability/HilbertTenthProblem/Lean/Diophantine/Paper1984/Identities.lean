import Diophantine.Paper1984.Masking
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic

/-!
# Jones–Matijasevič 1984, §2: the identities (8), (9), (11) and (13)

> **(8)** `m = C(n,k)` iff there are `u, w, v` with `u = 2^n + 1`,
> `(u+1)^n = w u^(k+1) + m u^k + v`, `v < u^k` and `m < u`.
> **(9)** `rem(2^(x y²), 2^(x y) - x) = x^y` for `1 < y`.
> **(11)** `a & b = c ↔ c ≼ b ∧ b ≼ a + b - c`.
> **(13)** If `Q` is a power of two and `a, b < Q`, then
> `a ≼ b ∧ c ≼ d ↔ a + cQ ≼ b + dQ`.

The paper takes `u = 2^n + 1`; the argument only needs `2^n < u`, so
`choose_eq_iff_digits` states (8) for any such base, under the hypothesis `k ≤ n`.
The case `k > n` is outside the scope of that equivalence.
-/

namespace JM1984

open Finset

/-- The digits of `(u+1)^n` in base `u > 2^n` are the binomial coefficients: the
part below `u^k` and the part above are bounded as in (8). -/
theorem binomial_digits {n k u : ℕ} (hu : 2 ^ n < u) (hk : k ≤ n) :
    ∃ w v, (u + 1) ^ n = w * u ^ (k + 1) + n.choose k * u ^ k + v ∧ v < u ^ k := by
  have hu1 : 1 ≤ u := lt_of_le_of_lt (Nat.zero_le _) hu
  have h := add_pow u 1 n
  simp only [one_pow, mul_one, Nat.cast_id] at h
  -- (u+1)^n = Σ_{i<k} + C(n,k) u^k + Σ_{i>k}
  have hsplit : ∑ m ∈ range (n + 1), u ^ m * n.choose m =
      ∑ m ∈ range k, u ^ m * n.choose m + u ^ k * n.choose k
        + ∑ m ∈ Ico (k + 1) (n + 1), u ^ m * n.choose m := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le k) (by omega : k ≤ n + 1),
      Finset.sum_eq_sum_Ico_succ_bot (by omega : k < n + 1)]
    ring
  have hdvd : u ^ (k + 1) ∣ ∑ m ∈ Ico (k + 1) (n + 1), u ^ m * n.choose m := by
    apply Finset.dvd_sum
    intro m hm
    simp only [Finset.mem_Ico] at hm
    exact Dvd.dvd.mul_right (pow_dvd_pow u hm.1) _
  obtain ⟨w, hw⟩ := hdvd
  refine ⟨w, ∑ m ∈ range k, u ^ m * n.choose m, ?_, ?_⟩
  · rw [h, hsplit, hw]; ring
  · -- Σ_{i<k} C(n,i) u^i ≤ (Σ_{i<k} C(n,i)) u^(k-1) < 2^n u^(k-1) < u^k
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp
    calc ∑ m ∈ range k, u ^ m * n.choose m
        ≤ ∑ m ∈ range k, u ^ (k - 1) * n.choose m := by
          apply Finset.sum_le_sum
          intro m hm
          simp only [Finset.mem_range] at hm
          have hmk : m ≤ k - 1 := by omega
          exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hu1 hmk)
      _ = u ^ (k - 1) * ∑ m ∈ range k, n.choose m := by rw [Finset.mul_sum]
      _ ≤ u ^ (k - 1) * ∑ m ∈ range (n + 1), n.choose m := by
          apply Nat.mul_le_mul_left
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega : k ≤ n + 1))
            (fun _ _ _ => Nat.zero_le _)
      _ = u ^ (k - 1) * 2 ^ n := by rw [Nat.sum_range_choose]
      _ < u ^ (k - 1) * u := Nat.mul_lt_mul_of_pos_left hu (Nat.pow_pos hu1)
      _ = u ^ k := by rw [← pow_succ, Nat.sub_add_cancel hk0]

/-- Uniqueness of base-`u` digits: the identity in (8) determines `m` as `C(n,k)`. -/
theorem choose_eq_of_digits {n k u m w v : ℕ} (hu : 2 ^ n < u) (hk : k ≤ n)
    (h : (u + 1) ^ n = w * u ^ (k + 1) + m * u ^ k + v) (hv : v < u ^ k) (hm : m < u) :
    m = n.choose k := by
  obtain ⟨w', v', h', hv'⟩ := binomial_digits hu hk
  have hu1 : 0 < u := lt_of_le_of_lt (Nat.zero_le _) hu
  have hcn : n.choose k < u := lt_of_le_of_lt (Nat.choose_le_two_pow n k) hu
  have hu0 : 0 < u ^ k := Nat.pow_pos hu1
  -- both sides give the base-u digit at position k
  have e : (w * u + m) * u ^ k + v = (w' * u + n.choose k) * u ^ k + v' :=
    calc (w * u + m) * u ^ k + v = w * u ^ (k + 1) + m * u ^ k + v := by ring
      _ = (u + 1) ^ n := h.symm
      _ = w' * u ^ (k + 1) + n.choose k * u ^ k + v' := h'
      _ = (w' * u + n.choose k) * u ^ k + v' := by ring
  have hdig : w * u + m = w' * u + n.choose k := by
    have h1 : ((w * u + m) * u ^ k + v) / u ^ k = w * u + m := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hu0, Nat.div_eq_of_lt hv, Nat.zero_add]
    have h2 : ((w' * u + n.choose k) * u ^ k + v') / u ^ k = w' * u + n.choose k := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hu0, Nat.div_eq_of_lt hv', Nat.zero_add]
    rw [← h1, e, h2]
  have : (w * u + m) % u = (w' * u + n.choose k) % u := by rw [hdig]
  rwa [Nat.add_comm (w * u), Nat.add_comm (w' * u), Nat.add_mul_mod_self_right,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hcn] at this

/-- (8) of the 1984 paper, as an equivalence, for `k ≤ n` and any base `u > 2^n`
(the paper takes `u = 2^n + 1`). -/
theorem choose_eq_iff_digits {n k u m : ℕ} (hu : 2 ^ n < u) (hk : k ≤ n) :
    m = n.choose k ↔
      ∃ w v, (u + 1) ^ n = w * u ^ (k + 1) + m * u ^ k + v ∧ v < u ^ k ∧ m < u := by
  constructor
  · rintro rfl
    obtain ⟨w, v, h, hv⟩ := binomial_digits hu hk
    exact ⟨w, v, h, hv, lt_of_le_of_lt (Nat.choose_le_two_pow n k) hu⟩
  · rintro ⟨w, v, h, hv, hm⟩
    exact choose_eq_of_digits hu hk h hv hm

/-- `2x ≤ 2^x` for `x ≥ 1`. -/
theorem two_mul_le_two_pow {x : ℕ} (hx : 1 ≤ x) : 2 * x ≤ 2 ^ x := by
  induction x, hx using Nat.le_induction with
  | base => norm_num
  | succ x hx ih =>
    have : 2 ≤ 2 ^ x := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ x := Nat.pow_le_pow_right (by norm_num) hx
    rw [pow_succ]; omega

/-- (9): `rem(2^(x y²), 2^(x y) - x) = x^y` for `1 < y`. -/
theorem rem_two_pow_eq_pow {x y : ℕ} (hy : 1 < y) :
    2 ^ (x * y ^ 2) % (2 ^ (x * y) - x) = x ^ y := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp [Nat.zero_pow (by omega : 0 < y)]
  have hlt : x < 2 ^ (x * y) := by
    calc x < 2 ^ x := Nat.lt_two_pow_self
      _ ≤ 2 ^ (x * y) := Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_right x (by omega))
  have hmod : 2 ^ (x * y) ≡ x [MOD 2 ^ (x * y) - x] := by
    rw [Nat.ModEq.comm, Nat.modEq_iff_dvd' hlt.le]
  have hpow : 2 ^ (x * y ^ 2) ≡ x ^ y [MOD 2 ^ (x * y) - x] := by
    have : 2 ^ (x * y ^ 2) = (2 ^ (x * y)) ^ y := by rw [← pow_mul]; ring_nf
    rw [this]
    exact hmod.pow y
  -- x^y + x ≤ 2 x^y ≤ 2^y x^y = (2x)^y ≤ (2^x)^y = 2^(xy)
  have hxy : x ^ y + x < 2 ^ (x * y) := by
    have h1 : x ≤ x ^ y := Nat.le_self_pow (by omega) x
    have h2 : 2 * x ^ y < (2 * x) ^ y := by
      calc 2 * x ^ y < 2 ^ y * x ^ y := Nat.mul_lt_mul_of_pos_right (by
            calc 2 < 2 ^ 2 := by norm_num
              _ ≤ 2 ^ y := Nat.pow_le_pow_right (by norm_num) hy) (Nat.pow_pos hx)
        _ = (2 * x) ^ y := by rw [mul_pow]
    have h3 : (2 * x) ^ y ≤ (2 ^ x) ^ y := Nat.pow_le_pow_left (two_mul_le_two_pow hx) _
    have h4 : (2 ^ x) ^ y = 2 ^ (x * y) := by rw [← pow_mul]
    omega
  have hlt' : x ^ y < 2 ^ (x * y) - x := Nat.lt_sub_iff_add_lt.2 hxy
  rw [← Nat.mod_eq_of_lt hlt']
  exact hpow

/-- A mask-subset is numerically smaller. -/
theorem Mask.le {r s : ℕ} (h : r ≼ s) : r ≤ s := Nat.le_of_testBit h

/-- `&&&` is determined by the parities and the halves. -/
theorem land_eq_of_parity {a b c : ℕ} (h0 : (a % 2 = 1 ∧ b % 2 = 1) ↔ c % 2 = 1)
    (h1 : a / 2 &&& b / 2 = c / 2) : a &&& b = c := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases i with
  | zero =>
    rw [Nat.testBit_and]
    simp only [Nat.testBit_zero, ← Bool.decide_and]
    exact decide_eq_decide.2 h0
  | succ i =>
    rw [Nat.testBit_succ, Nat.and_div_two, h1, ← Nat.testBit_succ]

theorem land_mod_two_iff (a b : ℕ) : (a &&& b) % 2 = 1 ↔ (a % 2 = 1 ∧ b % 2 = 1) := by
  have := Nat.testBit_and a b 0
  simp only [Nat.testBit_zero, ← Bool.decide_and] at this
  exact decide_eq_decide.1 this

theorem lor_mod_two_iff (a b : ℕ) : (a ||| b) % 2 = 1 ↔ (a % 2 = 1 ∨ b % 2 = 1) := by
  have := Nat.testBit_or a b 0
  simp only [Nat.testBit_zero, ← Bool.decide_or] at this
  exact decide_eq_decide.1 this

/-- `a + b = (a & b) + (a | b)`. -/
theorem add_eq_land_add_lor (a b : ℕ) : a + b = (a &&& b) + (a ||| b) := by
  induction a using Nat.strong_induction_on generalizing b with
  | _ a ih =>
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp
    · have h := ih (a / 2) (by omega) (b / 2)
      have e1 := Nat.div_add_mod (a &&& b) 2
      have e2 := Nat.div_add_mod (a ||| b) 2
      rw [Nat.and_div_two] at e1
      rw [Nat.or_div_two] at e2
      have p1 := land_mod_two_iff a b
      have p2 := lor_mod_two_iff a b
      omega

/-- The hard half of (11): `c ≼ b` and `b ≼ a + b - c` force `c = a & b`
(a "no carries" argument, by induction on the binary digits). -/
theorem land_eq_of_mask {a b c : ℕ} (hcb : c ≼ b) (hb : b ≼ a + b - c) : a &&& b = c := by
  induction b using Nat.strong_induction_on generalizing a c with
  | _ b ih =>
    rcases Nat.eq_zero_or_pos b with rfl | hb0
    · rw [(mask_zero_iff c).1 hcb]; simp
    have hle : c ≤ b := hcb.le
    rw [mask_iff_div2] at hcb hb
    obtain ⟨hcb0, hcb1⟩ := hcb
    obtain ⟨hb0', hb1⟩ := hb
    -- the digit pattern a₀ = b₀ = 1, c₀ = 0 would make a + b - c even, contradicting b ≼ a + b - c
    have hex : ¬ (a % 2 = 1 ∧ b % 2 = 1 ∧ c % 2 = 0) := by
      rintro ⟨ha, hb', hc⟩
      have := hb0' hb'
      omega
    have hq : (a + b - c) / 2 = a / 2 + b / 2 - c / 2 := by omega
    rw [hq] at hb1
    have hrec := ih (b / 2) (by omega) hcb1 hb1
    apply land_eq_of_parity _ hrec
    constructor
    · rintro ⟨ha, hb'⟩
      by_contra hc
      exact hex ⟨ha, hb', by omega⟩
    · intro hc
      have hb' := hcb0 hc
      have := hb0' hb'
      exact ⟨by omega, hb'⟩

/-- (11): `a & b = c ↔ c ≼ b ∧ b ≼ a + b - c`. -/
theorem land_eq_iff_mask (a b c : ℕ) : a &&& b = c ↔ (c ≼ b ∧ b ≼ a + b - c) := by
  constructor
  · rintro rfl
    refine ⟨?_, ?_⟩
    · rw [mask_iff_land, Nat.and_assoc, Nat.and_self]
    · rw [add_eq_land_add_lor, Nat.add_sub_cancel_left]
      intro i hi
      simp [Nat.testBit_or, hi]
  · rintro ⟨hcb, hb⟩
    exact land_eq_of_mask hcb hb

/-- Bits of `x + y·2^k` for `x < 2^k`: the low `k` bits are those of `x`, the rest those of `y`. -/
theorem testBit_add_mul_two_pow {k x : ℕ} (hx : x < 2 ^ k) (y i : ℕ) :
    (x + y * 2 ^ k).testBit i = if i < k then x.testBit i else y.testBit (i - k) := by
  rw [show x + y * 2 ^ k = 2 ^ k * y + x by ring]
  exact Nat.testBit_two_pow_mul_add y hx i

/-- (13): combining two mask conditions with a power-of-two shift. -/
theorem mask_add_pow_two_mul {Q a b c d : ℕ} (hQ : ∃ k, Q = 2 ^ k) (ha : a < Q) (hb : b < Q) :
    (a ≼ b ∧ c ≼ d) ↔ a + c * Q ≼ b + d * Q := by
  obtain ⟨k, rfl⟩ := hQ
  constructor
  · rintro ⟨hab, hcd⟩ i h
    rw [testBit_add_mul_two_pow ha] at h
    rw [testBit_add_mul_two_pow hb]
    split_ifs at h ⊢ with hik
    · exact hab i h
    · exact hcd _ h
  · intro H
    refine ⟨fun i hi => ?_, fun j hj => ?_⟩
    · have hik : i < k := by
        by_contra hcon
        have : a.testBit i = false :=
          Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (by omega)))
        rw [this] at hi; exact Bool.false_ne_true hi
      have := H i (by rw [testBit_add_mul_two_pow ha, if_pos hik]; exact hi)
      rwa [testBit_add_mul_two_pow hb, if_pos hik] at this
    · have := H (j + k) (by
        rw [testBit_add_mul_two_pow ha, if_neg (by omega), Nat.add_sub_cancel]; exact hj)
      rwa [testBit_add_mul_two_pow hb, if_neg (by omega), Nat.add_sub_cancel] at this

end JM1984

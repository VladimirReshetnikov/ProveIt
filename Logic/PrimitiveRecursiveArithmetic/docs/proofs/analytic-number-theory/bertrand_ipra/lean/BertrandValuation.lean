import Std

/-! Integer estimates for the prime-power factors of the central binomial
coefficient. The proofs hold at any base at least two. -/

namespace Bertrand

def carry (n q : Nat) : Nat := (2*n)/q - 2*(n/q)

private theorem twice_div {n q : Nat} (hq : 0 < q) :
    (2*n)/q = 2*(n/q) + (2*(n%q))/q := by
  have split : 2*n = q*(2*(n/q)) + 2*(n%q) := calc
    2*n = 2*(q*(n/q) + n%q) := congrArg (2 * ·) (Nat.div_add_mod n q).symm
    _ = q*(2*(n/q)) + 2*(n%q) := by rw [Nat.mul_add]; ac_rfl
  calc
    (2*n)/q = (q*(2*(n/q)) + 2*(n%q))/q := congrArg (· / q) split
    _ = _ := Nat.mul_add_div hq _ _

theorem carry_eq {n q : Nat} (hq : 0 < q) : carry n q = (2*(n%q))/q := by
  unfold carry
  rw [twice_div hq, Nat.add_sub_cancel_left]

theorem carry_le_one {n q : Nat} (hq : 0 < q) : carry n q ≤ 1 := by
  rw [carry_eq hq]
  have bound : (2*(n%q))/q < 2 :=
    (Nat.div_lt_iff_lt_mul hq).mpr (by have h := Nat.mod_lt n hq; omega)
  omega

theorem carry_vanishes {n q : Nat} (hq : 2*n < q) : carry n q = 0 := by
  simp [carry, Nat.div_eq_of_lt hq]

/-- If p is between 2n/3 and n, the first-power carry is zero. -/
theorem carry_middle {n p : Nat} (hlo : 2*n/3 < p) (hhi : p ≤ n) :
    carry n p = 0 := by
  have h₁ : n/p = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have h₂ : (2*n)/p = 2 := Nat.div_eq_of_lt_le (by omega) (by omega)
  simp [carry, h₁, h₂]

/-- Sum of the first k Legendre summands. -/
def floorSum (n p : Nat) : Nat → Nat
  | 0 => 0
  | k+1 => floorSum n p k + n / p^(k+1)

/-- Sum of carries at levels j=1,...,k. -/
def carrySum (n p : Nat) : Nat → Nat
  | 0 => 0
  | k+1 => carrySum n p k + carry n (p^(k+1))

theorem floorSum_double (n p k : Nat) (hp : 0 < p) :
    floorSum (2*n) p k = 2*floorSum n p k + carrySum n p k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [floorSum, carrySum]
    have hq : 0 < p^(k+1) := Nat.pow_pos hp
    rw [carry_eq hq, twice_div hq, ih]
    omega

theorem carrySum_le (n p k : Nat) (hp : 0 < p) : carrySum n p k ≤ k := by
  induction k with
  | zero => exact Nat.le_refl 0
  | succ k ih =>
    unfold carrySum
    have h := carry_le_one (n := n) (q := p^(k+1)) (Nat.pow_pos hp)
    omega

/-- Partial product of the first k prime-power contributions is at most 2n. -/
theorem pow_carrySum_le {n p : Nat} (hn : 1 ≤ n) (hp : 2 ≤ p) (k : Nat) :
    p ^ carrySum n p k ≤ 2*n := by
  induction k with
  | zero => simp only [carrySum, Nat.pow_zero]; omega
  | succ k ih =>
    by_cases hq : p^(k+1) ≤ 2*n
    · exact Nat.le_trans (Nat.pow_le_pow_right (by omega) (carrySum_le n p (k+1) (by omega))) hq
    · simpa only [carrySum, carry_vanishes (Nat.lt_of_not_le hq), Nat.add_zero] using ih

private theorem high_power_inactive {n p k : Nat} (hp : 2 ≤ p) (hs : 2*n < p*p) :
    carry n (p^(k+2)) = 0 := by
  apply carry_vanishes
  have h₁ : p^2 ≤ p^(k+2) := Nat.pow_le_pow_right (by omega) (by omega)
  have h₂ : p^2 = p*p := by simp [Nat.pow_succ]
  omega

theorem only_first_carry {n p : Nat} (hp : 2 ≤ p) (hs : 2*n < p*p) (k : Nat) :
    carrySum n p (k+1) = carry n p := by
  induction k with
  | zero => simp [carrySum]
  | succ k ih =>
    change carrySum n p (k+1) + carry n (p^(k+2)) = carry n p
    rw [ih, high_power_inactive hp hs, Nat.add_zero]

def K (n p : Nat) : Nat := p ^ carrySum n p (2*n)

theorem K_le_two_mul {n p : Nat} (hn : 1 ≤ n) (hp : 2 ≤ p) : K n p ≤ 2*n :=
  pow_carrySum_le hn hp _

theorem K_le_base {n p : Nat} (hp : 2 ≤ p) (hs : 2*n < p*p) : K n p ≤ p := by
  unfold K
  cases (2*n) with
  | zero => simp [carrySum]; omega
  | succ k =>
    rw [only_first_carry hp hs]
    have h := Nat.pow_le_pow_right (n := p) (by omega) (carry_le_one (n := n) (q := p) (by omega))
    simpa only [Nat.pow_one] using h

theorem K_eq_one {n p : Nat} (hp : 2 ≤ p) (hs : 2*n < p*p)
    (hlo : 2*n/3 < p) (hhi : p ≤ n) : K n p = 1 := by
  unfold K
  cases (2*n) with
  | zero => simp [carrySum]
  | succ k => rw [only_first_carry hp hs, carry_middle hlo hhi, Nat.pow_zero]

end Bertrand

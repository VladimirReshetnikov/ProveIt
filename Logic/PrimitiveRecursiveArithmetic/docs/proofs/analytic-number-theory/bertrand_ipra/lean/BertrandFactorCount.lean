import BertrandProducts
import BertrandValuation

namespace Bertrand

/-- Number of divisibility tests that succeed among the first k powers of p. -/
def hits (m p : Nat) : Nat → Nat
  | 0 => 0
  | k+1 => hits m p k + (if p^(k+1) ∣ m then 1 else 0)

def atomFactor (m M p : Nat) := if primeB p then p^(hits m p M) else 1

def factFactor (m M p : Nat) := if primeB p then p^(floorSum m p M) else 1

/-- Division crosses a multiple exactly when its quotient increments.
The proof uses the quotient-remainder identity at m and arithmetic on naturals. -/
private theorem succ_quotient (m q : Nat) :
    (m+1)/q = m/q + (if q ∣ m+1 then 1 else 0) := by
  cases q with
  | zero => simp
  | succ b =>
    let q := b+1
    change (m+1)/q = m/q + (if q ∣ m+1 then 1 else 0)
    have hpos : 0 < q := Nat.zero_lt_succ _
    have rem := Nat.mod_lt m hpos
    have quo : (m/q)*q + m%q = m := by
      rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
    by_cases h : m%q+1 = q
    · have hmul : m+1 = (m/q+1)*q := by rw [Nat.add_mul, Nat.one_mul]; omega
      have hd : q ∣ m+1 := ⟨m/q+1, hmul.trans (Nat.mul_comm _ _)⟩
      rw [if_pos hd]
      exact Nat.div_eq_of_eq_mul_left hpos hmul
    · have hq : (m+1)/q = m/q := Nat.div_eq_of_lt_le (by omega) (by
        rw [Nat.add_mul, Nat.one_mul]; omega)
      have hnd : ¬ q ∣ m+1 := by
        intro hd
        have he := Nat.div_mul_cancel hd
        rw [hq] at he
        omega
      simpa only [if_neg hnd, Nat.add_zero] using hq

theorem floorSum_succ (m p k : Nat) : floorSum (m+1) p k = floorSum m p k + hits (m+1) p k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [floorSum, hits, ih, succ_quotient]
    omega

theorem factFactor_succ (m M p : Nat) :
    factFactor (m+1) M p = factFactor m M p * atomFactor (m+1) M p := by
  by_cases h : primeB p = true <;> simp [factFactor, atomFactor, h, floorSum_succ, Nat.pow_add]

end Bertrand

/- Lean 4.32.0. Constructive proof of Thue's overlap theorem.
   The defining recursion reads the low binary digit and recurs on the quotient.
   It can be evaluated as a bounded first-order table through the input index. -/
import Lean.Elab.Tactic.Omega

namespace ThueMorse

/-- Odd parity of the number of ones in the binary expansion. -/
def digitParity : Nat → Bool
  | 0 => false
  | n+1 =>
    if (n+1) % 2 = 0 then digitParity ((n+1)/2)
    else !(digitParity ((n+1)/2))
termination_by n => n
decreasing_by all_goals omega

theorem atEven (n : Nat) : digitParity (2*n) = digitParity n := by
  cases n with
  | zero => rfl
  | succ n =>
    rw [show 2*(n+1) = (2*n+1)+1 by omega, digitParity]
    simp [show ((2*n+1)+1) % 2 = 0 by omega, show ((2*n+1)+1)/2 = n+1 by omega]

theorem atOdd (n : Nat) : digitParity (2*n+1) = !digitParity n := by
  rw [digitParity]
  simp [show (2*n+1)/2 = n by omega]

/-- Equality of two length-(p+1) factors separated by p. For p>0 this
    describes a word of the form a x a x a. -/
def Overlap (s p : Nat) : Prop :=
  ∀ k, k ≤ p → digitParity (s+k) = digitParity (s+p+k)

private theorem disagreeEven (i : Nat) (hi : i % 2 = 0) :
    digitParity i ≠ digitParity (i+1) := by
  have he : 2*(i/2) = i := by omega
  rw [← he, atEven, atOdd]
  cases digitParity (i/2) <;> decide

/-- Equal adjacent bits cannot recur an odd distance later. -/
private theorem alternatingOfOddOverlap (s p : Nat) (odd : p%2 = 1)
    (h : Overlap s p) (k : Nat) (hk : k < p) :
    digitParity (s+(k+1)) = !digitParity (s+k) := by
  have ne : digitParity (s+k) ≠ digitParity (s+(k+1)) := by
    intro same
    by_cases he : (s+k)%2 = 0
    · exact disagreeEven (s+k) he same
    · have he' : (s+p+k)%2 = 0 := by omega
      have shifted := (h k (by omega)).symm.trans (same.trans (h (k+1) (by omega)))
      exact disagreeEven (s+p+k) he' shifted
  cases h₁ : digitParity (s+k) <;> cases h₂ : digitParity (s+(k+1)) <;> simp_all

private theorem noOddOverlap (s p : Nat) (odd : p%2 = 1) : ¬Overlap s p := by
  intro h
  have alternating (k : Nat) (hk : k ≤ p) :
      digitParity (s+k) = (if k%2 = 0 then digitParity s else !digitParity s) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have step := alternatingOfOddOverlap s p odd h k (by omega)
      rw [step, ih (by omega)]
      by_cases even : k%2 = 0
      · simp [even, show ¬(k+1)%2 = 0 by omega]
      · simp [even, show (k+1)%2 = 0 by omega]
  have endpoint := alternating p (Nat.le_refl p)
  have equal := h 0 (Nat.zero_le _)
  simp [odd] at endpoint
  simp at equal
  have impossible := equal.trans endpoint
  cases v : digitParity s <;> simp [v] at impossible

private theorem sample (s a b : Nat)
    (h : digitParity (s+2*a) = digitParity (s+2*b)) :
    digitParity (s/2+a) = digitParity (s/2+b) := by
  by_cases he : s%2 = 0
  · rwa [show s+2*a = 2*(s/2+a) by omega, show s+2*b = 2*(s/2+b) by omega,
         atEven, atEven] at h
  · rw [show s+2*a = 2*(s/2+a)+1 by omega, show s+2*b = 2*(s/2+b)+1 by omega,
        atOdd, atOdd] at h
    simpa using h

private theorem halveOverlap (s p : Nat) (even : p%2 = 0) (h : Overlap s p) :
    Overlap (s/2) (p/2) := by
  intro k hk
  have spaced := h (2*k) (by omega)
  rw [show s+p+2*k = s+2*(p/2+k) by omega] at spaced
  simpa [Nat.add_assoc] using sample s k (p/2+k) spaced

/-- No nonempty period occurs twice plus one letter. -/
theorem overlapFree (s p : Nat) (hp : 0 < p) : ¬Overlap s p := by
  induction p using Nat.strongRecOn generalizing s with
  | ind p ih =>
    intro h
    by_cases even : p%2 = 0
    · exact ih (p/2) (by omega) (s/2) (by omega) (halveOverlap s p even h)
    · exact noOddOverlap s p (by omega) h

/-- Decidable bounded universal tests either succeed or exhibit a counterexample. -/
private theorem boundedAlternatives (R : Nat → Prop) [DecidablePred R] (p : Nat) :
    (∀ k, k ≤ p → R k) ∨ ∃ k, k ≤ p ∧ ¬ R k := by
  induction p with
  | zero =>
    by_cases h : R 0
    · apply Or.inl
      intro k hk
      have hz : k = 0 := by omega
      exact hz.symm ▸ h
    · exact .inr ⟨0, by omega, h⟩
  | succ p ih =>
    rcases ih with all | ⟨k,hk,bad⟩
    · by_cases h : R (p+1)
      · exact .inl (fun k hk => by
          by_cases prior : k ≤ p
          · exact all k prior
          · have : k = p+1 := by omega
            simpa [this] using h)
      · exact .inr ⟨p+1, by omega, h⟩
    · exact .inr ⟨k, by omega, bad⟩

/-- A mismatch appears within the first p+1 comparisons at any start index. -/
theorem mismatch (s p : Nat) (hp : 0 < p) :
    ∃ k, k ≤ p ∧ digitParity (s+k) ≠ digitParity (s+p+k) := by
  rcases boundedAlternatives (fun k => digitParity (s+k) = digitParity (s+p+k)) p with
    all | bad
  · exact False.elim (overlapFree s p hp all)
  · exact bad

/-- No tail is periodic, with a disagreement witness in [s,s+p]. -/
theorem aperiodic (s p : Nat) (hp : 0 < p) :
    ∃ n, s ≤ n ∧ n ≤ s+p ∧ digitParity n ≠ digitParity (n+p) := by
  obtain ⟨k,hk,bad⟩ := mismatch s p hp
  exact ⟨s+k, by omega, by omega, by simpa [Nat.add_right_comm] using bad⟩

/-- This version uses only ordinary primitive recursion on the highest index:
    its value is the entire table from zero through that index, inclusive. -/
def prefixTable : Nat → List Bool
  | 0 => [false]
  | n+1 =>
    let prior := prefixTable n
    let previous := prior[(n+1)/2]?.getD false
    prior ++ [if (n+1)%2 = 0 then previous else !previous]

theorem tableLength (n : Nat) : (prefixTable n).length = n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [prefixTable, List.length_append, List.length_cons,
                             List.length_nil, ih]

theorem tableCorrect (n k : Nat) (hk : k ≤ n) :
    (prefixTable n)[k]? = some (digitParity k) := by
  induction n generalizing k with
  | zero =>
    have : k = 0 := by omega
    subst k
    simp [prefixTable, digitParity]
  | succ n ih =>
    rw [prefixTable]
    by_cases old : k ≤ n
    · rw [List.getElem?_append_left (by rw [tableLength]; omega)]
      exact ih k old
    · have last : k = n+1 := by omega
      subst k
      rw [List.getElem?_append_right (by rw [tableLength]; omega), tableLength]
      simp only [Nat.sub_self, List.getElem?_cons_zero, ih ((n+1)/2) (by omega),
                 Option.getD_some]
      rw [digitParity]

/-- Overlap freedom implies cube freedom for every nonempty period. -/
theorem cubeFree (s p : Nat) (hp : 0 < p) :
    ¬ (∀ k, k < 2*p → digitParity (s+k) = digitParity (s+p+k)) := by
  intro cube
  apply overlapFree s p hp
  intro k hk
  exact cube k (by omega)

/-- The second half of every power-of-two prefix complements the first half. -/
theorem blockComplement (e i : Nat) (hi : i < 2^e) :
    digitParity (2^e+i) = !digitParity i := by
  induction e generalizing i with
  | zero =>
    simp only [Nat.pow_zero] at *
    have : i = 0 := by omega
    subst i
    exact atOdd 0
  | succ e ih =>
    have hpow : 2^(e+1) = 2*(2^e) := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [hpow] at hi ⊢
    have small : i/2 < 2^e := by omega
    by_cases even : i%2 = 0
    · rw [show 2*2^e+i = 2*(2^e+i/2) by omega, atEven, ih _ small]
      congr 1
      exact (show digitParity i = digitParity (i/2) by
        conv => lhs; rw [show i = 2*(i/2) by omega, atEven]).symm
    · rw [show 2*2^e+i = 2*(2^e+i/2)+1 by omega, atOdd, ih _ small]
      congr 1
      exact (show digitParity i = !digitParity (i/2) by
        conv => lhs; rw [show i = 2*(i/2)+1 by omega, atOdd]).symm

def onesBefore : Nat → Nat
  | 0 => 0
  | k+1 => onesBefore k + (digitParity k).toNat

theorem balancedPairs (n : Nat) : onesBefore (2*n) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2*(n+1) = (2*n+1)+1 by omega, onesBefore, onesBefore, atOdd, atEven, ih]
    cases digitParity n <;> simp

theorem balancedOdd (n : Nat) :
    onesBefore (2*n+1) = n+(digitParity n).toNat := by
  rw [onesBefore, balancedPairs, atEven]

#print axioms tableCorrect
#print axioms blockComplement
#print axioms balancedPairs
#print axioms cubeFree

/-- A single-natural-number primitive-recursive table, with little-endian bits.
    The previous word is never traversed or passed to a recursive call. -/
private def nextParity (n word : Nat) : Bool :=
  let bit := word.testBit ((n+1)/2)
  if (n+1)%2 = 0 then bit else !bit

private def appendParityBit (n word : Nat) : Nat :=
  if nextParity n word then 2^(n+1) + word else word

def packed : Nat → Nat
  | 0 => 0
  | n+1 => appendParityBit n (packed n)

theorem packedBound (n : Nat) : packed n < 2^(n+1) := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [packed, Nat.pow_succ 2 (n+1)]
    unfold appendParityBit
    split <;> omega

/-- First-order equivalence to digitParity, with all inputs numerical. -/
theorem packedCorrect (n k : Nat) (hk : k ≤ n) :
    (packed n).testBit k = digitParity k := by
  induction n generalizing k with
  | zero =>
    have zero : k = 0 := by omega
    subst k
    simp [packed, digitParity]
  | succ n ih =>
    rw [packed]
    unfold appendParityBit
    by_cases old : k ≤ n
    · split
      · rw [Nat.testBit_two_pow_add_gt (by omega), ih _ old]
      · exact ih _ old
    · have last : k = n+1 := by omega
      subst k
      have next : nextParity n (packed n) = digitParity (n+1) := by
        unfold nextParity
        rw [ih ((n+1)/2) (by omega), digitParity]
      rw [next]
      have fresh := Nat.testBit_lt_two_pow (packedBound n)
      cases digitParity (n+1) <;> simp [Nat.testBit_two_pow_add_eq, fresh]

theorem packedMismatch (s p : Nat) (hp : 0 < p) :
    ∃ k, k ≤ p ∧ (packed (s+2*p)).testBit (s+k) ≠
                      (packed (s+2*p)).testBit (s+p+k) := by
  obtain ⟨k,hk,bad⟩ := mismatch s p hp
  refine ⟨k,hk,?_⟩
  simpa only [packedCorrect (s+2*p) (s+k) (by omega),
              packedCorrect (s+2*p) (s+p+k) (by omega)] using bad

#print axioms packedCorrect
#print axioms packedMismatch

#print axioms atEven
#print axioms overlapFree
#print axioms mismatch
#print axioms aperiodic

end ThueMorse

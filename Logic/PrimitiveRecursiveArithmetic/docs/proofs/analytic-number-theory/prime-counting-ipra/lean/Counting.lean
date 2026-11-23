import Std

/-!
Executable arithmetic layer. A prime is an integer at least two for which every
candidate proper divisor is rejected. Counts and bounded selection are generic
so their proofs also apply to residue classes and finite sieves.
-/
namespace PrimeCounting

def prime (n : Nat) : Bool :=
  decide (2 ≤ n) && (List.range n).all (fun d => decide (d < 2 ∨ n % d ≠ 0))

theorem prime_spec (n : Nat) :
    prime n = true ↔ 2 ≤ n ∧ ∀ d, 2 ≤ d → d < n → n % d ≠ 0 := by
  simp only [prime, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range]
  constructor
  · rintro ⟨hn, h⟩
    exact ⟨hn, fun d hlo hhi => (h d hhi).resolve_left (by omega)⟩
  · rintro ⟨hn, h⟩
    refine ⟨hn, fun d hd => ?_⟩
    by_cases hlo : d < 2
    · exact Or.inl hlo
    · exact Or.inr (h d (by omega) hd)

def tick (b : Bool) : Nat := if b then 1 else 0

/-- Count from 1 through n, both ends included. -/
def count (b : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n+1 => count b n + tick (b (n+1))

abbrev pi := count prime

theorem count_step (b : Nat → Bool) (n : Nat) :
    count b (n+1) = count b n + tick (b (n+1)) := rfl

theorem count_mono (b : Nat → Bool) {i j : Nat} (h : i ≤ j) :
    count b i ≤ count b j := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => rw [count_step]; omega

theorem count_le (b : Nat → Bool) (n : Nat) : count b n ≤ n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
    rw [count_step]
    cases b (n+1) <;> simp [tick] <;> omega

/-- Select the first hit of positive rank k using an explicit upper bound. -/
def select (b : Nat → Bool) (k : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => if k ≤ count b n then select b k n
           else if b (n+1) then n+1 else 0

theorem select_spec (b : Nat → Bool) (k n : Nat)
    (hk : 0 < k) (h : k ≤ count b n) :
    0 < select b k n ∧ select b k n ≤ n ∧
    b (select b k n) = true ∧ count b (select b k n) = k ∧
    count b (select b k n - 1) = k - 1 := by
  induction n with
  | zero => simp [count] at h; omega
  | succ n ih =>
    by_cases old : k ≤ count b n
    · rw [select, if_pos old]
      obtain ⟨pos, le, hit, rank, before⟩ := ih old
      exact ⟨pos, by omega, hit, rank, before⟩
    · rw [count_step] at h
      cases hb : b (n+1) with
      | false => simp [hb, tick] at h; omega
      | true =>
        simp [hb, tick] at h
        simp only [select, if_neg old, hb, if_true, Nat.succ_sub_one, count_step,
          tick, Bool.true_eq, decide_true]
        exact ⟨by omega, by omega, trivial, by omega, by omega⟩

theorem select_unique (b : Nat → Bool) (k n i : Nat)
    (hk : 0 < k) (enough : k ≤ count b n)
    (pos : 0 < i) (hit : b i = true) (rank : count b i = k) :
    select b k n = i := by
  obtain ⟨spos, _, _, srank, sprev⟩ := select_spec b k n hk enough
  cases i with
  | zero => omega
  | succ j =>
    rw [count_step, hit] at rank
    simp [tick] at rank
    by_cases small : select b k n ≤ j
    · have := count_mono b small
      omega
    · by_cases big : j+1 ≤ select b k n - 1
      · have hm := count_mono b big
        rw [count_step, hit] at hm
        simp [tick] at hm
        omega
      · omega

def piClass (m r : Nat) := count (fun p => prime p && decide (p % m = r))

def fact : Nat → Nat
  | 0 => 1
  | n+1 => (n+1)*fact n

def euclidBound : Nat → Nat
  | 0 => 1
  | k+1 => fact (euclidBound k) + 1

def nthPrime (k : Nat) := select prime k (euclidBound k)

example : pi 30 = 10 := by decide
example : piClass 4 1 30 = 4 := by decide
example : select prime 5 30 = 11 := by decide
#print axioms prime_spec
#print axioms select_spec
#print axioms select_unique

end PrimeCounting

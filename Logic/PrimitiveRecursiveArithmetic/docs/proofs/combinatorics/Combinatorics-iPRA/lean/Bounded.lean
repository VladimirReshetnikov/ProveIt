/- Reusable numerical encodings. Lean 4.32.0, standard library only. -/
import Std

namespace CombinatoricsCode

/-- Sentinel `N` means that every position below `N` failed. -/
def first (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | N+1 => let j := first p N
           if j < N then j else if p N then N else N+1

theorem first_spec (p : Nat → Bool) (N : Nat) :
    first p N ≤ N ∧ (first p N < N → p (first p N) = true) ∧
    ∀ i, i < first p N → p i = false := by
  induction N with
  | zero => simp [first]
  | succ N ih =>
    obtain ⟨hle, hit, prior⟩ := ih
    by_cases h : first p N < N
    · simp only [first, if_pos h]
      exact ⟨by omega, fun _ => hit h, prior⟩
    · have eqN : first p N = N := by omega
      rw [eqN] at prior
      cases pn : p N with
      | true =>
        simp only [first, if_neg h, pn, ↓reduceIte]
        exact ⟨by omega, fun _ => trivial, prior⟩
      | false =>
        simp only [first, if_neg h, pn, Bool.false_eq_true, ↓reduceIte]
        refine ⟨by omega, fun hh => by omega, ?_⟩
        intro i hi
        by_cases old : i < N
        · exact prior i old
        · have eq : i = N := by omega
          simpa only [eq] using pn

theorem success_iff (p : Nat → Bool) (N : Nat) :
    first p N < N ↔ ∃ i, i < N ∧ p i = true := by
  obtain ⟨limit, hit, before⟩ := first_spec p N
  constructor
  · intro h; exact ⟨_, h, hit h⟩
  · rintro ⟨i, hi, ok⟩
    by_cases h : first p N < N
    · exact h
    · have fail := before i (by omega)
      simp [ok] at fail

def allBelow (N : Nat) (p : Nat → Bool) : Bool := first (fun i => !(p i)) N == N

def tally (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i+1 => tally f i + f i

def bit (mask i : Nat) : Bool := mask / 2^i % 2 == 1

def size (n mask : Nat) : Nat := tally (fun i => (bit mask i).toNat) n

def digit (base code i : Nat) : Nat := code / (max 2 base)^i % max 2 base

/-- A signed difference is represented by two separate natural sums elsewhere. -/
def subset (n a b : Nat) : Bool := allBelow n (fun i => !(bit a i) || bit b i)

def neighborhood (left right graph a y : Nat) : Bool :=
  decide (first (fun x => bit a x && bit graph (right*x+y)) left < left)

def hall (left right graph : Nat) : Bool := allBelow (2^left) (fun a =>
  decide (size left a ≤ tally (fun y => (neighborhood left right graph a y).toNat) right))

/-- The result is an index mask; the caller supplies canonical base-n residues. -/
def zeroSum (n entries : Nat) : Nat :=
  let len := 2*n-1
  first (fun mask => size len mask == n &&
    tally (fun i => if bit mask i then digit n entries i else 0) len % n == 0) (2^len)

example : hall 2 2 9 = true := by decide
example : hall 2 2 5 = false := by decide
example : zeroSum 2 6 = 6 := by decide

#print axioms first_spec
#print axioms success_iff
end CombinatoricsCode

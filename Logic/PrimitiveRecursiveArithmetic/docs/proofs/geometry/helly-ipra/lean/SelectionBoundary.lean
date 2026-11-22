import Std

/-!
The interval obstruction in the Helly report. The endpoints below are integers
0 or 1. A rational approximation is a signed numerator and a positive
denominator. A real point in every interval yields one fixed rational
approximation meeting every interval to error 1/8. All arguments after that
real-to-rational observation are proved here. No computability library is used:
the final lemma takes an index for the particular purported computable bit.
-/

namespace HellyBoundary

def Single (a : Nat → Bool) : Prop :=
  ∀ i j, a i = true → a j = true → i = j

/-- Whether event 2*j+r occurred for some j < t. -/
def seen (a : Nat → Bool) (r t : Nat) : Bool :=
  (List.range t).any (fun j => a (2*j+r))

theorem seen_iff {a : Nat → Bool} {r t : Nat} :
    seen a r t = true ↔ ∃ j, j < t ∧ a (2*j+r) = true := by
  simp [seen, List.any_eq_true]

theorem seen_mono {a : Nat → Bool} {r s t : Nat} (hst : s ≤ t)
    (h : seen a r s = true) : seen a r t = true := by
  obtain ⟨j, hj, h₁⟩ := seen_iff.mp h
  exact seen_iff.mpr ⟨j, by omega, h₁⟩

def lower (a : Nat → Bool) (t : Nat) : Int := if seen a 0 t then 1 else 0
def upper (a : Nat → Bool) (t : Nat) : Int := if seen a 1 t then 0 else 1

theorem interval_inhabited {a : Nat → Bool} (h : Single a) (t : Nat) :
    lower a t ≤ upper a t := by
  by_cases he : seen a 0 t = true
  · have ho : seen a 1 t ≠ true := by
      intro bad
      obtain ⟨i, _, hi⟩ := seen_iff.mp he
      obtain ⟨j, _, hj⟩ := seen_iff.mp bad
      have := h _ _ hi hj
      omega
    simp [lower, upper, he, ho]
  · simp [lower, upper, he]
    split <;> decide

/-- The left endpoint at t is an explicit witness for all stages up to t. -/
theorem common_prefix {a : Nat → Bool} (h : Single a) {s t : Nat} (hst : s ≤ t) :
    lower a s ≤ lower a t ∧ lower a t ≤ upper a s := by
  constructor
  · by_cases he : seen a 0 s = true
    · simp [lower, he, seen_mono hst he]
    · simp [lower, he]
      split <;> decide
  · exact Int.le_trans (interval_inhabited h t) (by
      by_cases ho : seen a 1 s = true
      · simp [upper, ho, seen_mono hst ho]
      · simp [upper, ho]
        split <;> decide)

structure Approximation where
  num : Int
  den : Int
  positive : 0 < den

/-- The rational num/den lies within 1/8 of [lower a t,upper a t]. -/
def Near (a : Nat → Bool) (t : Nat) (q : Approximation) : Prop :=
  8 * lower a t * q.den ≤ 8 * q.num + q.den ∧
  8 * q.num ≤ 8 * upper a t * q.den + q.den

/-- false when the approximation is at most one half. -/
def selectBit (q : Approximation) : Bool := decide (q.den < 2*q.num)

/-- A single 1/8-approximation for all stages excludes the selected parity. -/
theorem excludes_selected {a : Nat → Bool} {q : Approximation}
    (hall : ∀ t, Near a t q) (j : Nat) :
    a (2*j+(selectBit q).toNat) = false := by
  have hp := q.positive
  by_cases ht : q.den < 2*q.num
  · simp [selectBit, ht]
    apply Bool.eq_false_iff.mpr
    intro hj
    have hs : seen a 1 (j+1) = true :=
      seen_iff.mpr ⟨j, by omega, hj⟩
    have hu := (hall (j+1)).2
    simp [upper, hs] at hu
    omega
  · simp [selectBit, ht]
    apply Bool.eq_false_iff.mpr
    intro hj
    have hs : seen a 0 (j+1) = true :=
      seen_iff.mpr ⟨j, by omega, by simpa using hj⟩
    have hl := (hall (j+1)).1
    simp [lower, hs] at hl
    omega

theorem llpo_of_common_approx {a : Nat → Bool} {q : Approximation}
    (hall : ∀ t, Near a t q) :
    (∀ j, a (2*j) = false) ∨ (∀ j, a (2*j+1) = false) := by
  cases hb : selectBit q with
  | false => exact Or.inl (fun j => by simpa [hb] using excludes_selected hall j)
  | true => exact Or.inr (fun j => by simpa [hb] using excludes_selected hall j)

/-- For the diagonal event family, events e (2*t+b) records machine e(e)
    first halting at time t with bit b. If the proposed q is computable, its
    selectBit program has an index e witnessing hindex. -/
theorem diagonal_conflict (events : Nat → Nat → Bool) (q : Nat → Approximation)
    (hall : ∀ e t, Near (events e) t (q e))
    (hindex : ∃ e t, events e (2*t+(selectBit (q e)).toNat) = true) : False := by
  obtain ⟨e, t, hit⟩ := hindex
  have miss := excludes_selected (hall e) t
  simp [miss] at hit

end HellyBoundary

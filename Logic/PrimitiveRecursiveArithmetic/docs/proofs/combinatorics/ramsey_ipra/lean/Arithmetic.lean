import Std

/-! First-order numerical interface for finite Ramsey. Every higher-order argument
    to a fold below is instantiated by a fixed body in the arithmetic predicates. -/
namespace Ramsey.Arithmetic

def allBelow (p : Nat → Bool) : Nat → Bool
  | 0 => true
  | n+1 => allBelow p n && p n

theorem allBelow_spec (p : Nat → Bool) (n : Nat) :
    allBelow p n = true ↔ ∀ j < n, p j = true := by
  induction n with
  | zero => simp [allBelow]
  | succ n ih =>
    rw [allBelow, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨early, last⟩ j hj
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with h | rfl
      · exact early j h
      · exact last
    · intro h
      exact ⟨fun j hj => h j (by omega), h n (by omega)⟩

/-- Failure is encoded by the search bound itself. -/
def firstBelow (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n+1 =>
    let a := firstBelow p n
    if a < n then a else if p n then n else n+1

theorem firstBelow_spec (p : Nat → Bool) (n : Nat) :
    firstBelow p n ≤ n ∧
    (firstBelow p n < n → p (firstBelow p n) = true) ∧
    (∀ j < firstBelow p n, p j = false) := by
  induction n with
  | zero => simp [firstBelow]
  | succ n ih =>
    obtain ⟨ub, hit, minimal⟩ := ih
    by_cases h : firstBelow p n < n
    · simp only [firstBelow, if_pos h]
      exact ⟨by omega, fun _ => hit h, minimal⟩
    · have eq : firstBelow p n = n := by omega
      rw [eq] at minimal
      cases hp : p n with
      | true =>
        simp only [firstBelow, if_neg h, hp, if_true]
        exact ⟨by omega, fun _ => trivial, minimal⟩
      | false =>
        simp only [firstBelow, if_neg h, hp, Bool.false_eq_true, if_false]
        refine ⟨by omega, by omega, ?_⟩
        intro j hj
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj | rfl
        · exact minimal j hj
        · exact hp

theorem firstBelow_found {p : Nat → Bool} {j n : Nat} (hj : j < n) (hp : p j = true) :
    firstBelow p n < n ∧ p (firstBelow p n) = true := by
  obtain ⟨ub, hit, minimal⟩ := firstBelow_spec p n
  have le : firstBelow p n ≤ j := by
    apply Nat.le_of_not_gt
    intro h
    have bad := minimal j h
    simp [hp] at bad
  have lt : firstBelow p n < n := by omega
  exact ⟨lt, hit lt⟩

def base (q : Nat) := max 2 q
def digit (b C i : Nat) := C / b^i % b
def tableLimit (q N : Nat) := base q ^ (2^N)
def valid (q N C : Nat) := allBelow (fun a => decide (digit (base q) C a < q)) (2^N)

def card (mask : Nat) : Nat → Nat
  | 0 => 0
  | i+1 => card mask i + digit 2 mask i

def inside (N a h : Nat) :=
  allBelow (fun i => decide (digit 2 a i ≤ digit 2 h i)) N

/-- Encode a certificate (mask h, color d) as q*h+d. -/
def check (q t r N C w : Nat) : Bool :=
  let h := w / q
  let d := w % q
  decide (h < 2^N ∧ d < q ∧ card h N = t) &&
    allBelow (fun a =>
      !(inside N a h && decide (card a N = r)) || decide (digit (base q) C a = d)) (2^N)

def win (q t r N C : Nat) := firstBelow (check q t r N C) (q*2^N)

def census (q t r N : Nat) : Bool :=
  allBelow (fun C => !valid q N C || decide (win q t r N C < q*2^N)) (tableLimit q N)

/-- The rank induction bit is equivalent to the finite arrow assertion. -/
theorem census_spec (q t r N : Nat) : census q t r N = true ↔
    ∀ C < tableLimit q N, valid q N C = true →
      ∃ w < q*2^N, check q t r N C w = true := by
  rw [census, allBelow_spec]
  constructor
  · intro hall C hC validC
    have result := hall C hC
    have hw : win q t r N C < q*2^N := by simpa [validC] using result
    exact ⟨_, hw, (firstBelow_spec (check q t r N C) (q*2^N)).2.1 hw⟩
  · intro h C hC
    cases hv : valid q N C with
    | false => simp
    | true =>
      obtain ⟨w, hw, ok⟩ := h C hC hv
      have found := (firstBelow_found hw ok).1
      simpa [win] using found

end Ramsey.Arithmetic

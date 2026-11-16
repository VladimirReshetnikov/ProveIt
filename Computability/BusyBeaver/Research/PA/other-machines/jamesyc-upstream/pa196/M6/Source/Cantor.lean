module
public import Std.Tactic
@[expose] public section

/-! The source's Cantor pairing, including the zero alias. The decoder walks
successive diagonal positions exactly as the literal stack-unpairing loop does.
No machine-loop correctness is assumed or claimed in this arithmetic module. -/
namespace M6.Source.Cantor

def triangle : Nat → Nat
  | 0 => 0
  | n + 1 => triangle n + n + 1

/-- The recursive triangle is the standard triangular number, without division. -/
theorem twice_triangle (n : Nat) : 2 * triangle n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have ih' : 2 * triangle n = n*n + n := by simpa [Nat.mul_add] using ih
    simp only [triangle, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
    omega

theorem triangle_closed (n : Nat) : triangle n = n * (n+1) / 2 := by
  rw [← twice_triangle]
  simp

def pair (a b : Nat) : Nat := triangle (a + b) + b

theorem triangle_strict_mono {s t : Nat} (h : s < t) : triangle s < triangle t := by
  induction t with
  | zero => omega
  | succ t ih =>
    by_cases he : s = t
    · subst s; simp only [triangle]; omega
    · have hs : s < t := by omega
      have hm := ih hs
      simp only [triangle]
      omega

theorem pair_diagonal_lower (a b : Nat) : triangle (a+b) ≤ pair a b := by
  simp [pair]

theorem pair_diagonal_upper (a b : Nat) : pair a b < triangle (a+b+1) := by
  simp only [pair, triangle]
  omega

theorem pair_injective {a b c d : Nat} (h : pair a b = pair c d) : a = c ∧ b = d := by
  have lo₁ := pair_diagonal_lower a b
  have hi₁ := pair_diagonal_upper a b
  have lo₂ := pair_diagonal_lower c d
  have hi₂ := pair_diagonal_upper c d
  have hs : a+b = c+d := by
    by_cases hab : a+b < c+d
    · have hle : triangle (a+b+1) ≤ triangle (c+d) := by
        by_cases he : a+b+1 = c+d
        · simp [he]
        · have hh := triangle_strict_mono (s := a+b+1) (t := c+d) (by omega)
          omega
      omega
    · by_cases hcd : c+d < a+b
      · have hle : triangle (c+d+1) ≤ triangle (a+b) := by
          by_cases he : c+d+1 = a+b
          · simp [he]
          · have hh := triangle_strict_mono (s := c+d+1) (t := a+b) (by omega)
            omega
        omega
      · omega
  simp only [pair, hs] at h
  constructor <;> omega

/-- The literal unpair loop's successor on a Cantor diagonal. -/
def advance (p : Nat × Nat) : Nat × Nat :=
  match p.1 with
  | 0 => (p.2 + 1, 0)
  | a + 1 => (a, p.2 + 1)

theorem pair_advance (p : Nat × Nat) : pair (advance p).1 (advance p).2 = pair p.1 p.2 + 1 := by
  rcases p with ⟨a,b⟩
  cases a with
  | zero => simp [advance, pair, triangle, Nat.add_assoc]
  | succ a => simp [advance, pair, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

def decode : Nat → Nat × Nat
  | 0 => (0,0)
  | n + 1 => advance (decode n)

theorem pair_decode (n : Nat) : pair (decode n).1 (decode n).2 = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [decode, pair_advance, ih]

theorem decode_pair (a b : Nat) : decode (pair a b) = (a,b) := by
  have h := pair_injective (a := (decode (pair a b)).1) (b := (decode (pair a b)).2)
    (c := a) (d := b) (pair_decode (pair a b))
  exact Prod.ext h.1 h.2

theorem pair_zero_iff (a b : Nat) : pair a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    exact pair_injective (c := 0) (d := 0) h
  · rintro ⟨rfl,rfl⟩
    rfl

theorem opaque_seed : pair 1 1 = 4 := by decide

def implication (a b : Nat) : Nat := 4 * pair a b

def universal (a b : Nat) : Nat := 4 * pair a b + 2

theorem implication_not_falsity (a b : Nat) : implication a b ≠ 1 := by
  simp only [implication]
  omega

theorem universal_ge_two (a b : Nat) : 2 ≤ universal a b := by
  simp [universal]

theorem implication_zero_iff (a b : Nat) : implication a b = 0 ↔ a = 0 ∧ b = 0 := by
  simp only [implication, Nat.mul_eq_zero, Nat.reduceEqDiff, false_or, pair_zero_iff]

#print axioms pair_decode
#print axioms decode_pair
#print axioms implication_zero_iff
end M6.Source.Cantor


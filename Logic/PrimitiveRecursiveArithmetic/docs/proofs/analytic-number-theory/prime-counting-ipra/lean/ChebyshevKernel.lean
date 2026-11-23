import Std

/-! The periodic arithmetic kernel used for the global upper bound. -/
namespace PrimeCounting.ChebyshevKernel

def floorWeight (n : Nat) : Int :=
  (n : Int) - ((n / 2 : Nat) : Int) - ((n / 3 : Nat) : Int)
    - ((n / 5 : Nat) : Int) + ((n / 30 : Nat) : Int)

theorem periodic (n : Nat) : floorWeight (n + 30) = floorWeight n := by
  simp only [floorWeight, Int.natCast_add]
  omega

private theorem firstBlock : ∀ r : Fin 30, floorWeight r = 0 ∨ floorWeight r = 1 := by
  decide

theorem zero_or_one (n : Nat) : floorWeight n = 0 ∨ floorWeight n = 1 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : n < 30
    · exact firstBlock ⟨n,h⟩
    · have hn : n-30 < n := by omega
      have eq : n-30+30 = n := by omega
      have hw := periodic (n-30)
      rw [eq] at hw
      rw [hw]
      exact ih (n-30) hn

theorem firstSix : ∀ r : Fin 6, 0 < r.1 → floorWeight r = 1 := by decide

/-- Each integer in the newest multiplicative window contributes one. -/
theorem unit_window (n q : Nat) (hq : 0 < q) (hl : n/6 < q) (hr : q ≤ n) :
    floorWeight (n / q) = 1 := by
  have lo : 1 ≤ n/q := (Nat.le_div_iff_mul_le hq).mpr (by simpa using hr)
  have hn : n < 6*q := by omega
  have hi : n/q < 6 := (Nat.div_lt_iff_lt_mul hq).mpr hn
  exact firstSix ⟨n/q, hi⟩ lo

#print axioms zero_or_one
#print axioms unit_window
end PrimeCounting.ChebyshevKernel

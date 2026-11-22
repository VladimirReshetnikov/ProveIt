import IPRAProbability.Finite

/-!
Finite signed sums and the two estimates used to pass from rational
approximations to L1 names.  A shared positive denominator can be cleared.
No assertion about completed spaces is made here.
-/
namespace IPRAProbability

def isum : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, f => isum n f + f n

theorem isum_sub (n : Nat) (f g : Nat → Int) :
    isum n (fun i => f i - g i) = isum n f - isum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change isum n (fun i => f i - g i) + (f n - g n) =
      (isum n f + f n) - (isum n g + g n)
    rw [ih]
    omega

theorem abs_sum_bound (n : Nat) (f : Nat → Int) :
    (isum n f).natAbs ≤ nsum n (fun i => (f i).natAbs) := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
    exact Nat.le_trans (Int.natAbs_add_le (isum n f) (f n))
      (Nat.add_le_add_right ih ((f n).natAbs))

/-- L1 distance numerator on one common finite partition. -/
def distanceSum (n : Nat) (f g : Nat → Int) : Nat :=
  nsum n (fun i => (f i - g i).natAbs)

/-- Absolute difference of integral numerators is bounded by the L1 numerator. -/
theorem expectation_stability (n : Nat) (f g : Nat → Int) :
    (isum n f - isum n g).natAbs ≤ distanceSum n f g := by
  rw [← isum_sub]
  exact abs_sum_bound n (fun i => f i - g i)

theorem distance_triangle (n : Nat) (f g h : Nat → Int) :
    distanceSum n f h ≤ distanceSum n f g + distanceSum n g h := by
  rw [distanceSum, distanceSum, distanceSum, ← nsum_add]
  apply nsum_mono
  intro i _
  have heq : f i - h i = (f i - g i) + (g i - h i) := by omega
  rw [heq]
  exact Int.natAbs_add_le (f i - g i) (g i - h i)

end IPRAProbability

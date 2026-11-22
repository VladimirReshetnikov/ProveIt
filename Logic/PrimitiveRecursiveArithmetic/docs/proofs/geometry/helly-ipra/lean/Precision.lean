import Std

/-!
Coordinatewise error bounds for rational barycentric rows, after taking
common denominators. A list element consists of a natural weight numerator
and an index of an input point. If all sampled coordinates and error bounds
are represented on the common grid 1/D and W is the (positive) weight
mass, sums below represent barycentric coordinates on the grid 1/(D W).
D can be chosen separately for every pair of stages and each coordinate.
-/

namespace HellyPrecision

universe u
variable {I : Type u}

def mass : List (Nat × I) → Int
  | [] => 0
  | (w, _) :: xs => (w : Int) + mass xs

def weighted (f : I → Int) : List (Nat × I) → Int
  | [] => 0
  | (w, j) :: xs => (w : Int) * f j + weighted f xs

private theorem difference_add (a b c d : Int) :
    (a + b) - (c + d) = (a - c) + (b - d) := by
  simp only [Int.sub_eq_add_neg, Int.neg_add]
  ac_rfl

/-- Both signs of a common input error bound pass to the weighted sum. -/
theorem weighted_error (xs : List (Nat × I)) (f g : I → Int) (E : Int)
    (h : ∀ a ∈ xs, -E ≤ f a.2 - g a.2 ∧ f a.2 - g a.2 ≤ E) :
    -(mass xs * E) ≤ weighted f xs - weighted g xs ∧
    weighted f xs - weighted g xs ≤ mass xs * E := by
  induction xs with
  | nil => simp [weighted, mass]
  | cons a xs ih =>
    obtain ⟨w, j⟩ := a
    obtain ⟨left, right⟩ := h (w, j) List.mem_cons_self
    obtain ⟨lower, upper⟩ := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have sw := Int.ofNat_zero_le w
    have lo := Int.mul_le_mul_of_nonneg_left left sw
    have hi := Int.mul_le_mul_of_nonneg_left right sw
    simp only [Int.mul_neg, Int.mul_sub, Prod.snd] at lo hi
    simp only [weighted, mass, Int.add_mul, Int.neg_add, difference_add]
    exact ⟨Int.add_le_add lo lower, Int.add_le_add hi upper⟩

theorem mass_nonnegative (xs : List (Nat × I)) : 0 ≤ mass xs := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    obtain ⟨w,j⟩ := a
    simp only [mass]
    have hw := Int.ofNat_zero_le w
    omega

theorem mass_positive (xs : List (Nat × I))
    (h : ∃ a ∈ xs, 0 < a.1) : 0 < mass xs := by
  induction xs with
  | nil =>
    obtain ⟨a, ha, _⟩ := h
    cases ha
  | cons a xs ih =>
    obtain ⟨w,j⟩ := a
    obtain ⟨b, hb, hbpos⟩ := h
    rcases List.mem_cons.mp hb with hhead | htail
    · subst b
      have hm := mass_nonnegative xs
      simp only [mass, Prod.fst] at *
      omega
    · have hm := ih ⟨b, htail, hbpos⟩
      have hw := Int.ofNat_zero_le w
      simp only [mass]
      omega

/-- The regularity estimate for a barycentric name at a fixed pair of stages.
The sampled integer functions share a denominator chosen for this pair. -/
theorem regularity_pair (xs : List (Nat × I)) (first second : I → Int)
    (errFirst errSecond : Int)
    (h : ∀ a ∈ xs, -(errFirst + errSecond) ≤ first a.2 - second a.2 ∧
        first a.2 - second a.2 ≤ errFirst + errSecond) :
    -(mass xs * (errFirst + errSecond)) ≤ weighted first xs - weighted second xs ∧
    weighted first xs - weighted second xs ≤ mass xs * (errFirst + errSecond) :=
  weighted_error xs first second (errFirst + errSecond) h

/-- If the snapshot barycentre equals y, the same two-sided bound compares
the barycentre at the other stage to y. Here y is on the common input grid. -/
theorem snapshot_pair (xs : List (Nat × I)) (current snapshot : I → Int)
    (errCurrent errSnapshot y : Int)
    (hy : weighted snapshot xs = mass xs * y)
    (h : ∀ a ∈ xs, -(errCurrent + errSnapshot) ≤ current a.2 - snapshot a.2 ∧
        current a.2 - snapshot a.2 ≤ errCurrent + errSnapshot) :
    -(mass xs * (errCurrent + errSnapshot)) ≤ weighted current xs - mass xs * y ∧
    weighted current xs - mass xs * y ≤ mass xs * (errCurrent + errSnapshot) := by
  rw [← hy]
  exact regularity_pair xs current snapshot errCurrent errSnapshot h

end HellyPrecision

import Mathlib.Data.Set.Card
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Factor complexity of an infinite word, and its first difference

The factor complexity `p(ℓ)` of an infinite word counts its distinct
length-`ℓ` windows.  Every *exact* complexity computation — Brlek's
formula for the Thue–Morse word among them — rests on one identity: the
first difference of `p` counts the right extensions.  This module proves
that identity once, for an arbitrary word over an arbitrary finite
alphabet, so that the Thue–Morse case becomes an instance rather than a
bespoke argument.

The mechanism is a fiberwise count over the restriction map
`Fin.init`, which deletes the last letter.  Restriction sends
length-`(ℓ+1)` factors onto length-`ℓ` factors, and the fiber above a
factor `w` is in bijection with the set of letters `a` for which `w a`
is again a factor — the *right extensions* of `w`.  Summing fiber sizes
gives

`p(ℓ+1) = ∑_{w a factor of length ℓ} deg⁺(w)`.

Over a two-letter alphabet `deg⁺(w) ∈ {1,2}`, so the sum collapses to

`p(ℓ+1) = p(ℓ) + #{right-special factors of length ℓ}`,

the form in which the identity is actually used.

* `wordWindow`, `wordFactors`, `wordComplexity` — the basic notions.
* `rightDegree` — the number of right extensions of a word.
* `IsRightSpecial` — having at least two right extensions.
* `wordComplexity_succ_eq_sum` — **the fiberwise identity**.
* `wordComplexity_succ_eq_add_card_rightSpecial` — **the binary form**.
-/

set_option autoImplicit false

open Finset

namespace Fabius

variable {α : Type*}

/-! ### Windows, factors, complexity -/

/-- The length-`ℓ` window of the word `f` at position `i`. -/
def wordWindow (f : ℕ → α) (ℓ i : ℕ) : Fin ℓ → α := fun j => f (i + j)

@[simp] theorem wordWindow_apply (f : ℕ → α) (ℓ i : ℕ) (j : Fin ℓ) :
    wordWindow f ℓ i j = f (i + j) := rfl

/-- The set of length-`ℓ` factors of `f`. -/
def wordFactors (f : ℕ → α) (ℓ : ℕ) : Set (Fin ℓ → α) :=
  Set.range (wordWindow f ℓ)

theorem wordWindow_mem_wordFactors (f : ℕ → α) (ℓ i : ℕ) :
    wordWindow f ℓ i ∈ wordFactors f ℓ := ⟨i, rfl⟩

/-- The factor complexity `p(ℓ)`: the number of distinct length-`ℓ`
factors. -/
noncomputable def wordComplexity (f : ℕ → α) (ℓ : ℕ) : ℕ :=
  (wordFactors f ℓ).ncard

/-- Over a finite alphabet every factor set is finite. -/
theorem wordFactors_finite [Finite α] (f : ℕ → α) (ℓ : ℕ) :
    (wordFactors f ℓ).Finite :=
  Set.toFinite _

/-! ### Restriction and extension -/

/-- Deleting the last letter of a window shortens it. -/
@[simp] theorem init_wordWindow (f : ℕ → α) (ℓ i : ℕ) :
    Fin.init (wordWindow f (ℓ + 1) i) = wordWindow f ℓ i := by
  funext j
  simp [Fin.init]

/-- A length-`(ℓ+1)` window is its length-`ℓ` window with the next
letter appended. -/
theorem wordWindow_succ_eq_snoc (f : ℕ → α) (ℓ i : ℕ) :
    wordWindow f (ℓ + 1) i = Fin.snoc (wordWindow f ℓ i) (f (i + ℓ)) := by
  funext j
  refine Fin.lastCases ?_ ?_ j
  · simp
  · intro j
    simp

/-- Restriction maps factors to factors. -/
theorem init_mem_wordFactors (f : ℕ → α) (ℓ : ℕ) {u : Fin (ℓ + 1) → α}
    (hu : u ∈ wordFactors f (ℓ + 1)) :
    Fin.init u ∈ wordFactors f ℓ := by
  obtain ⟨i, rfl⟩ := hu
  rw [init_wordWindow]
  exact wordWindow_mem_wordFactors f ℓ i

/-! ### Right extensions -/

/-- The set of letters extending `w` to the right inside `f`. -/
def rightExtensions (f : ℕ → α) (ℓ : ℕ) (w : Fin ℓ → α) : Set α :=
  {a : α | Fin.snoc w a ∈ wordFactors f (ℓ + 1)}

/-- The number of right extensions of `w`. -/
noncomputable def rightDegree (f : ℕ → α) (ℓ : ℕ) (w : Fin ℓ → α) : ℕ :=
  (rightExtensions f ℓ w).ncard

/-- A word is **right-special** when it admits at least two right
extensions. -/
def IsRightSpecial (f : ℕ → α) (ℓ : ℕ) (w : Fin ℓ → α) : Prop :=
  2 ≤ rightDegree f ℓ w

/-- Every factor extends to the right at least once. -/
theorem one_le_rightDegree [Finite α] (f : ℕ → α) (ℓ : ℕ)
    {w : Fin ℓ → α} (hw : w ∈ wordFactors f ℓ) :
    1 ≤ rightDegree f ℓ w := by
  obtain ⟨i, rfl⟩ := hw
  have hmem : f (i + ℓ) ∈ rightExtensions f ℓ (wordWindow f ℓ i) := by
    show Fin.snoc (wordWindow f ℓ i) (f (i + ℓ)) ∈ wordFactors f (ℓ + 1)
    rw [← wordWindow_succ_eq_snoc]
    exact wordWindow_mem_wordFactors f (ℓ + 1) i
  rw [rightDegree]
  exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨_, hmem⟩

/-- The right degree never exceeds the alphabet size. -/
theorem rightDegree_le_card [Fintype α] (f : ℕ → α) (ℓ : ℕ)
    (w : Fin ℓ → α) : rightDegree f ℓ w ≤ Fintype.card α := by
  have h := Set.ncard_le_ncard
    (Set.subset_univ (rightExtensions f ℓ w)) (Set.toFinite _)
  rwa [Set.ncard_univ, Nat.card_eq_fintype_card] at h

/-! ### The first difference of the complexity -/

/-- **The fiberwise identity.**  The complexity at length `ℓ+1` is the
total number of right extensions of the length-`ℓ` factors.  Deleting
the last letter fibers the length-`(ℓ+1)` factors over the length-`ℓ`
ones, and the fiber above `w` is exactly its set of right extensions. -/
theorem wordComplexity_succ_eq_sum [Fintype α] (f : ℕ → α) (ℓ : ℕ) :
    wordComplexity f (ℓ + 1) =
      ∑ w ∈ (wordFactors_finite f ℓ).toFinset, rightDegree f ℓ w := by
  classical
  rw [wordComplexity,
    Set.ncard_eq_toFinset_card _ (wordFactors_finite f (ℓ + 1))]
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun u : Fin (ℓ + 1) → α => Fin.init u)
    (t := (wordFactors_finite f ℓ).toFinset) ?maps]
  case maps =>
    intro u hu
    simp only [Set.Finite.coe_toFinset] at hu ⊢
    exact init_mem_wordFactors f ℓ hu
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [Set.Finite.mem_toFinset] at hw
  rw [rightDegree, Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
  refine Finset.card_bij'
    (fun u _ => u (Fin.last ℓ)) (fun a _ => Fin.snoc w a) ?_ ?_ ?_ ?_
  · intro u hu
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset] at hu
    obtain ⟨humem, huinit⟩ := hu
    simp only [Set.Finite.mem_toFinset]
    show Fin.snoc w (u (Fin.last ℓ)) ∈ wordFactors f (ℓ + 1)
    rw [← huinit, Fin.snoc_init_self]
    exact humem
  · intro a ha
    simp only [Set.Finite.mem_toFinset] at ha
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨ha, Fin.init_snoc _ _⟩
  · intro u hu
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset] at hu
    rw [← hu.2, Fin.snoc_init_self]
  · intro a _
    exact Fin.snoc_last _ _

/-- **The binary first-difference identity.**  Over a two-letter
alphabet the complexity increases by exactly the number of
right-special factors:
`p(ℓ+1) = p(ℓ) + #{right-special factors of length ℓ}`. -/
theorem wordComplexity_succ_eq_add_card_rightSpecial [Fintype α]
    [DecidableEq α] (hα : Fintype.card α = 2) (f : ℕ → α) (ℓ : ℕ) :
    wordComplexity f (ℓ + 1) =
      wordComplexity f ℓ +
        ((wordFactors_finite f ℓ).toFinset.filter
          (fun w => 2 ≤ rightDegree f ℓ w)).card := by
  classical
  rw [wordComplexity_succ_eq_sum f ℓ]
  have hsplit : ∀ w ∈ (wordFactors_finite f ℓ).toFinset,
      rightDegree f ℓ w =
        1 + (if 2 ≤ rightDegree f ℓ w then 1 else 0) := by
    intro w hw
    rw [Set.Finite.mem_toFinset] at hw
    have h1 : 1 ≤ rightDegree f ℓ w := one_le_rightDegree f ℓ hw
    have h2 : rightDegree f ℓ w ≤ 2 := by
      have := rightDegree_le_card f ℓ w
      omega
    by_cases hc : 2 ≤ rightDegree f ℓ w
    · rw [if_pos hc]
      omega
    · rw [if_neg hc]
      omega
  have hind : ∑ w ∈ (wordFactors_finite f ℓ).toFinset,
      (if 2 ≤ rightDegree f ℓ w then (1 : ℕ) else 0) =
      ((wordFactors_finite f ℓ).toFinset.filter
        (fun w => 2 ≤ rightDegree f ℓ w)).card := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero,
      ← Finset.card_eq_sum_ones]
  have hone : ∑ _w ∈ (wordFactors_finite f ℓ).toFinset, (1 : ℕ) =
      wordComplexity f ℓ := by
    rw [← Finset.card_eq_sum_ones, wordComplexity,
      Set.ncard_eq_toFinset_card _ (wordFactors_finite f ℓ)]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, hone, hind]

end Fabius

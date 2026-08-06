import PolynomialFormulas.GaussianPolynomialSolver

/-!
# Matching disjoint certified disks with all polynomial roots

This file contains the finite multiplicity argument used by the executable
Gaussian-rational root approximator.  If a degree-`d` complex polynomial has
one root in each of `d` pairwise disjoint closed disks, the selected roots are
distinct and therefore exhaust its root multiset.  Thus multiplicity is
recovered without appealing to an unproved numerical root-matching oracle.
-/

namespace LeanProofs.PolynomialFormulas

open Metric Polynomial

noncomputable section

namespace GaussianPolynomialRootMatching

/-- The multiset obtained from a vector, retaining one occurrence for every
index. -/
def vectorMultiset {d : ℕ} (u : Fin d → ℂ) : Multiset ℂ :=
  Finset.univ.1.map u

@[simp]
theorem vectorMultiset_card {d : ℕ} (u : Fin d → ℂ) :
    (vectorMultiset u).card = d := by
  simp [vectorMultiset]

theorem vectorMultiset_nodup {d : ℕ} {u : Fin d → ℂ}
    (hu : Function.Injective u) : (vectorMultiset u).Nodup := by
  exact Finset.univ.nodup.map hu

/-- Distinct selected zeros form a submultiset of the polynomial's roots. -/
theorem vectorMultiset_le_roots {d : ℕ} {p : ℂ[X]} (hp : p ≠ 0)
    {u : Fin d → ℂ} (hu : Function.Injective u)
    (hroot : ∀ i, p.eval (u i) = 0) : vectorMultiset u ≤ p.roots := by
  rw [Multiset.le_iff_subset (vectorMultiset_nodup hu)]
  intro x hx
  simp only [vectorMultiset, Multiset.mem_map] at hx
  obtain ⟨i, _, rfl⟩ := hx
  exact (Polynomial.mem_roots hp).2 (hroot i)

/-- A full degree's worth of distinct zeros exhausts the root multiset of a
split polynomial. -/
theorem vectorMultiset_eq_roots {d : ℕ} {p : ℂ[X]} (hp : p ≠ 0)
    (hsplit : p.Splits) (hdeg : p.natDegree = d)
    {u : Fin d → ℂ} (hu : Function.Injective u)
    (hroot : ∀ i, p.eval (u i) = 0) : vectorMultiset u = p.roots := by
  apply Multiset.eq_of_le_of_card_le (vectorMultiset_le_roots hp hu hroot)
  rw [← hsplit.natDegree_eq_card_roots, hdeg, vectorMultiset_card]

/-- Points selected from disks whose centers are more than two radii apart
are pairwise distinct. -/
theorem injective_of_mem_disjoint_closedBalls {d : ℕ} {c u : Fin d → ℂ}
    {r : ℝ} (hu : ∀ i, u i ∈ closedBall (c i) r)
    (hsep : ∀ i j, i ≠ j → 2 * r < dist (c i) (c j)) :
    Function.Injective u := by
  intro i j hij
  by_contra hne
  have hi := hu i
  have hj := hu j
  rw [mem_closedBall] at hi hj
  have hc : dist (c i) (c j) ≤ 2 * r := by
    calc
      dist (c i) (c j) ≤ dist (c i) (u i) + dist (u i) (c j) :=
        dist_triangle _ _ _
      _ = dist (c i) (u i) + dist (u j) (c j) := by rw [hij]
      _ ≤ r + r := add_le_add (by simpa [dist_comm] using hi) hj
      _ = 2 * r := by ring
  exact (not_lt_of_ge hc) (hsep i j hne)

/-- The variable-radius version of
`injective_of_mem_disjoint_closedBalls`. -/
theorem injective_of_mem_pairwiseDisjoint_closedBalls {d : ℕ}
    {c u : Fin d → ℂ} {r : Fin d → ℝ}
    (hu : ∀ i, u i ∈ closedBall (c i) (r i))
    (hsep : ∀ i j, i ≠ j → r i + r j < dist (c i) (c j)) :
    Function.Injective u := by
  intro i j hij
  by_contra hne
  have hi := hu i
  have hj := hu j
  rw [mem_closedBall] at hi hj
  have hc : dist (c i) (c j) ≤ r i + r j := by
    calc
      dist (c i) (c j) ≤ dist (c i) (u i) + dist (u i) (c j) :=
        dist_triangle _ _ _
      _ = dist (c i) (u i) + dist (u j) (c j) := by rw [hij]
      _ ≤ r i + r j := add_le_add (by simpa [dist_comm] using hi) hj
  exact (not_lt_of_ge hc) (hsep i j hne)

/-- Choosing a zero from each of a full degree's worth of disjoint disks gives
an ordering of all roots, including the multiplicities recorded by
`Polynomial.roots`. -/
theorem exists_root_vector_of_disjoint_closedBalls {d : ℕ} {p : ℂ[X]}
    (hp : p ≠ 0) (hsplit : p.Splits) (hdeg : p.natDegree = d)
    (c : Fin d → ℂ) {r : ℝ}
    (hex : ∀ i, ∃ z ∈ closedBall (c i) r, p.eval z = 0)
    (hsep : ∀ i j, i ≠ j → 2 * r < dist (c i) (c j)) :
    ∃ u : Fin d → ℂ, vectorMultiset u = p.roots ∧
      ∀ i, u i ∈ closedBall (c i) r := by
  choose u hu_mem hu_root using hex
  have hinj : Function.Injective u :=
    injective_of_mem_disjoint_closedBalls hu_mem hsep
  exact ⟨u, vectorMultiset_eq_roots hp hsplit hdeg hinj hu_root, hu_mem⟩

/-- Variable-radius form of `exists_root_vector_of_disjoint_closedBalls`. -/
theorem exists_root_vector_of_pairwiseDisjoint_closedBalls {d : ℕ}
    {p : ℂ[X]} (hp : p ≠ 0) (hsplit : p.Splits)
    (hdeg : p.natDegree = d) (c : Fin d → ℂ) (r : Fin d → ℝ)
    (hex : ∀ i, ∃ z ∈ closedBall (c i) (r i), p.eval z = 0)
    (hsep : ∀ i j, i ≠ j → r i + r j < dist (c i) (c j)) :
    ∃ u : Fin d → ℂ, vectorMultiset u = p.roots ∧
      ∀ i, u i ∈ closedBall (c i) (r i) := by
  choose u hu_mem hu_root using hex
  have hinj : Function.Injective u :=
    injective_of_mem_pairwiseDisjoint_closedBalls hu_mem hsep
  exact ⟨u, vectorMultiset_eq_roots hp hsplit hdeg hinj hu_root, hu_mem⟩

end GaussianPolynomialRootMatching

end

end LeanProofs.PolynomialFormulas

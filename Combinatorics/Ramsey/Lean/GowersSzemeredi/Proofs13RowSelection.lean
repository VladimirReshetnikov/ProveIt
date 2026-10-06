import GowersSzemeredi.Proofs13RowCoefficients
import Mathlib.Algebra.Order.Chebyshev

/-!
# The common-row selection in Lemma 13.8

The mass attached to a column pair counts every point on their common rows.
Summing it over column pairs gives the cubic row moment. Diagonal column
pairs contribute the quadratic moment, which can be subtracted exactly.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Finset

namespace LeanProofs.GowersSzemeredi

/-- Total row size retained by two selected columns. -/
def rowPairMass {X Y : Type*} [DecidableEq X] (I : Finset Y)
    (D : Y → Finset X) (x₁ x₂ : X) : Real :=
  ∑ h ∈ I, if x₁ ∈ D h ∧ x₂ ∈ D h then ((D h).card : Real) else 0

/-- The cubic-moment identity underlying Lemma 13.8. -/
theorem rowPairMass_sum {X Y : Type*} [DecidableEq X]
    (S : Finset X) (I : Finset Y) (D : Y → Finset X)
    (hD : ∀ h ∈ I, D h ⊆ S) :
    ∑ x₁ ∈ S, ∑ x₂ ∈ S, rowPairMass I D x₁ x₂ =
      ∑ h ∈ I, ((D h).card : Real) ^ 3 := by
  classical
  unfold rowPairMass
  conv_lhs =>
    arg 2
    ext x
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  have heq : S.filter (fun x ↦ x ∈ D h) = D h := by
    rw [filter_mem_eq_inter, Finset.inter_eq_right.mpr (hD h hh)]
  simp only [ite_and]
  simp_rw [Finset.sum_ite_irrel, Finset.sum_const_zero, ← Finset.sum_filter]
  rw [heq]
  simp [pow_succ, mul_assoc]

/-- Identical columns contribute the quadratic row moment exactly. -/
theorem rowPairMass_diagonal {X Y : Type*} [DecidableEq X]
    (S : Finset X) (I : Finset Y) (D : Y → Finset X)
    (hD : ∀ h ∈ I, D h ⊆ S) :
    ∑ x ∈ S, rowPairMass I D x x =
      ∑ h ∈ I, ((D h).card : Real) ^ 2 := by
  classical
  unfold rowPairMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  simp only [and_self, ← Finset.sum_filter]
  rw [filter_mem_eq_inter, Finset.inter_eq_right.mpr (hD h hh)]
  simp [pow_two]

/-- The exact mass left after removing identical column pairs. -/
theorem rowPairMass_off_diagonal {X Y : Type*} [DecidableEq X]
    (S : Finset X) (I : Finset Y) (D : Y → Finset X)
    (hD : ∀ h ∈ I, D h ⊆ S) :
    ∑ x₁ ∈ S, ∑ x₂ ∈ S, (if x₁ = x₂ then 0 else rowPairMass I D x₁ x₂) =
      (∑ h ∈ I, ((D h).card : Real) ^ 3) -
      ∑ h ∈ I, ((D h).card : Real) ^ 2 := by
  classical
  rw [← rowPairMass_sum S I D hD, ← rowPairMass_diagonal S I D hD,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  have heq : ∀ y, (if x = y then 0 else rowPairMass I D x y) =
      rowPairMass I D x y - (if x = y then rowPairMass I D x y else 0) := by
    intro y
    split_ifs <;> simp
  simp_rw [heq]
  rw [Finset.sum_sub_distrib]
  simp [hx]

/-- Select distinct columns using any certified lower bound on the cubic
moment minus the diagonal contribution. -/
theorem exists_distinct_rowPairMass_of_moments {X Y : Type*} [DecidableEq X]
    (S : Finset X) (I : Finset Y) (D : Y → Finset X)
    (hS : S.Nonempty) (hD : ∀ h ∈ I, D h ⊆ S) {t : Real} (ht : 0 < t)
    (hmoment : t * (S.card : Real) ^ 2 ≤
      (∑ h ∈ I, ((D h).card : Real) ^ 3) -
      ∑ h ∈ I, ((D h).card : Real) ^ 2) :
    ∃ x₁ ∈ S, ∃ x₂ ∈ S, x₁ ≠ x₂ ∧ t ≤ rowPairMass I D x₁ x₂ := by
  classical
  have havg : (∑ p ∈ S ×ˢ S, t) ≤
      ∑ p ∈ S ×ˢ S, (if p.1 = p.2 then 0 else rowPairMass I D p.1 p.2) := by
    simp only [Finset.sum_product]
    rw [rowPairMass_off_diagonal S I D hD]
    simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using hmoment
  obtain ⟨⟨x₁, x₂⟩, hp, h⟩ := Finset.exists_le_of_sum_le (hS.product hS) havg
  obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp hp
  have hx : x₁ ≠ x₂ := by
    intro heq
    simp only [heq, ↓reduceIte] at h
    exact (not_le_of_gt ht) h
  exact ⟨x₁, h₁, x₂, h₂, hx, by simpa only [if_neg hx] using h⟩

/-- The mixed density estimate used in the paper: square the density relative
 to the available rows, then use the absolute total-mass bound once. -/
theorem cubic_row_moment_of_two_bounds {Y : Type*} (I : Finset Y)
    (d : Y → Real) (hd : ∀ h ∈ I, 0 ≤ d h) (hI : I.Nonempty)
    {u b : Real} (hu : 0 ≤ u) (hb : 0 ≤ b)
    (hrel : u * I.card ≤ ∑ h ∈ I, d h)
    (habs : b ≤ ∑ h ∈ I, d h) :
    u ^ 2 * b ≤ ∑ h ∈ I, d h ^ 3 := by
  have hIpos : (0 : Real) < I.card := by exact_mod_cast hI.card_pos
  have hsq := pow_le_pow_left₀ (mul_nonneg hu hIpos.le) hrel 2
  have hbound : (I.card : Real) ^ 2 * (u ^ 2 * b) ≤
      (I.card : Real) ^ 2 * ∑ h ∈ I, d h ^ 3 := by
    calc
      _ = (u * I.card) ^ 2 * b := by ring
      _ ≤ (∑ h ∈ I, d h) ^ 2 * (∑ h ∈ I, d h) :=
        mul_le_mul hsq habs hb (sq_nonneg _)
      _ = (∑ h ∈ I, d h) ^ 3 := by ring
      _ ≤ _ := pow_sum_le_card_mul_sum_pow hd 2
  exact le_of_mul_le_mul_left hbound (sq_pos_of_pos hIpos)

/-- A coarse upper bound for the diagonal contribution; the exact quadratic
moment remains available when a particular row distribution gives less. -/
theorem quadratic_row_moment_le {X Y : Type*} (S : Finset X) (I : Finset Y)
    (D : Y → Finset X) (hD : ∀ h ∈ I, D h ⊆ S) {m : Real}
    (hm : (I.card : Real) ≤ m) :
    (∑ h ∈ I, ((D h).card : Real) ^ 2) ≤ m * (S.card : Real) ^ 2 := by
  calc
    _ ≤ ∑ _h ∈ I, (S.card : Real) ^ 2 := by
      apply Finset.sum_le_sum
      intro h hh
      apply pow_le_pow_left₀ (Nat.cast_nonneg _) _ 2
      exact_mod_cast Finset.card_le_card (hD h hh)
    _ = (I.card : Real) * (S.card : Real) ^ 2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hm (sq_nonneg _)

end LeanProofs.GowersSzemeredi

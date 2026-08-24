import GowersSzemeredi.Definitions

/-!
# Shared proof infrastructure for the Gowers catalogue

This module contains elementary facts about the concrete encodings used by the
statement catalogue.  They are deliberately independent of the numbered paper
results, so later companion proofs can use them without circularity.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

theorem IsPartition.mem_iff {X : Type*} [DecidableEq X] {m : Nat}
    {P : Fin m → Finset X} {S : Finset X} (hP : IsPartition P S) (x : X) :
    x ∈ S ↔ ∃ i, x ∈ P i :=
  hP.1 x

theorem IsPartition.cell_subset {X : Type*} [DecidableEq X] {m : Nat}
    {P : Fin m → Finset X} {S : Finset X} (hP : IsPartition P S) (i : Fin m) :
    P i ⊆ S := by
  intro x hx
  exact (hP.1 x).2 ⟨i, hx⟩

theorem IsPartition.pairwise_disjoint {X : Type*} [DecidableEq X] {m : Nat}
    {P : Fin m → Finset X} {S : Finset X} (hP : IsPartition P S) :
    Set.Pairwise (Set.univ : Set (Fin m)) fun i j ↦ Disjoint (P i) (P j) := by
  intro i _ j _ hij
  exact hP.2 i j (bne_iff_ne.mpr hij)

/-- The cells of a finite partition account for the cardinality of the set
exactly once. -/
theorem IsPartition.sum_card {X : Type*} [DecidableEq X] {m : Nat}
    {P : Fin m → Finset X} {S : Finset X} (hP : IsPartition P S) :
    ∑ i, (P i).card = S.card := by
  classical
  have hdisj :
      ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint P := by
    intro i _ j _ hij
    exact hP.2 i j (bne_iff_ne.mpr hij)
  have hunion : Finset.univ.biUnion P = S := by
    ext x
    simp only [mem_biUnion, mem_univ, true_and]
    exact (hP.1 x).symm
  rw [← hunion, Finset.card_biUnion hdisj]

@[simp] theorem sum_indicator {N : Nat} [NeZero N] (A : Finset (ZMod N)) :
    ∑ x : ZMod N, indicator A x = (A.card : Complex) := by
  classical
  simp [indicator]

@[simp] theorem sum_balanced {N : Nat} [NeZero N] (A : Finset (ZMod N)) :
    ∑ x : ZMod N, balanced A x = 0 := by
  classical
  simp only [balanced, sum_sub_distrib, sum_indicator, sum_const, card_univ,
    ZMod.card, nsmul_eq_mul, density]
  apply sub_eq_zero.mpr
  norm_cast
  exact (mul_div_cancel₀ (A.card : Real)
    (by exact_mod_cast NeZero.ne N : (N : Real) ≠ 0)).symm

theorem density_nonneg {N : Nat} (A : Finset (ZMod N)) : 0 ≤ density A := by
  exact div_nonneg (by positivity) (by positivity)

theorem density_le_one {N : Nat} [NeZero N] (A : Finset (ZMod N)) :
    density A ≤ 1 := by
  rw [density, div_le_one (by exact_mod_cast NeZero.pos N : (0 : Real) < N)]
  have hcard : A.card ≤ N := by
    simpa only [ZMod.card] using A.card_le_univ
  exact_mod_cast hcard

theorem indicator_discValued {N : Nat} (A : Finset (ZMod N)) :
    DiscValued (indicator A) := by
  intro x
  classical
  simp only [indicator]
  split_ifs <;> simp

end LeanProofs.GowersSzemeredi

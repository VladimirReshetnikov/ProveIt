import OAI.Combinatorics.Progressions.Estimates.DisjointPowersetSum
import OAI.Combinatorics.Progressions.Polynomial.RestrictedDegreeSupports

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem sum_support_cutoff_split (I : Finset ι) (b : ℕ) (F : Finset ι → ℝ) :
    (∑ S ∈ lowDegreeCoordinateSets ι b, F S) =
      ∑ A ∈ I.powerset, ∑ B ∈ Iᶜ.powerset, if A.card + B.card ≤ b then F (A ∪ B) else 0 := by
  have he : lowDegreeCoordinateSets ι b = Finset.univ.powerset.filter (fun S => S.card ≤ b) := by
    ext S
    simp only [mem_lowDegreeCoordinateSets, Finset.mem_filter, Finset.mem_powerset,
      Finset.subset_univ, true_and]
  rw [he, Finset.sum_filter]
  have hu : (Finset.univ : Finset ι) = I ∪ Iᶜ := (Finset.union_compl I).symm
  rw [hu, disjoint_powerset_sum I Iᶜ disjoint_compl_right]
  apply Finset.sum_congr rfl
  intro A hA
  apply Finset.sum_congr rfl
  intro B hB
  have hd : Disjoint A B := disjoint_compl_right.mono
    (Finset.mem_powerset.mp hA) (Finset.mem_powerset.mp hB)
  rw [Finset.card_union_of_disjoint hd]

theorem sum_cutoff_core_shell (I : Finset ι) (b : ℕ) (hIb : I.card ≤ b)
    (a v : Finset ι → ℝ) :
    (∑ A ∈ I.powerset, ∑ B ∈ Iᶜ.powerset, if A.card + B.card ≤ b then a A * v B else 0) =
      (∑ A ∈ I.powerset, a A) * (∑ B ∈ Iᶜ.powerset, if B.card ≤ b - I.card then v B else 0) +
      ∑ A ∈ I.powerset, a A *
        (∑ B ∈ Iᶜ.powerset, if b - I.card < B.card ∧ A.card + B.card ≤ b then v B else 0) := by
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro A hA
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro B _
  have hAcard := Finset.card_le_card (Finset.mem_powerset.mp hA)
  by_cases hc : B.card ≤ b - I.card
  · have hab : A.card + B.card ≤ b := by omega
    have hn : ¬ b - I.card < B.card := by omega
    simp only [hc, hab, hn, false_and, ite_true, ite_false, mul_zero, add_zero]
  · have hgt : b - I.card < B.card := by omega
    by_cases hab : A.card + B.card ≤ b <;>
      simp only [hc, hgt, hab, true_and, ite_true, ite_false, mul_zero, zero_add]

end Erdos3

end

end OAI

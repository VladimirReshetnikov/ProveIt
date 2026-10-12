import GowersSzemeredi.Proofs13DenseFreimanExtension
import GowersSzemeredi.Proofs13RowCoefficients

/-! Large row domains retain two common columns, and dense row populations
will supply global bilinear coefficients in the high-density Section 13 case. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem four_large_domains_common_columns {N : Nat} [NeZero N]
    (hN : 5 ≤ N) (A : Fin 4 → Finset (ZMod N))
    (hA : ∀ i, 4 * N < 5 * (A i).card) :
    ∃ x y : ZMod N, x ≠ y ∧ (∀ i, x ∈ A i) ∧ (∀ i, y ∈ A i) := by
  have hc (i : Fin 4) : 5 * (N - (A i).card) < N := by
    have hle : (A i).card ≤ N := by simpa only [ZMod.card] using Finset.card_le_univ (A i)
    have hi := hA i
    omega
  have hs : (∑ i : Fin 4, 5 * (N - (A i).card)) < ∑ _i : Fin 4, N :=
    Finset.sum_lt_sum (fun i _ ↦ (hc i).le) ⟨0, Finset.mem_univ _, hc 0⟩
  have hsum : 5 * (∑ i : Fin 4, (N - (A i).card)) < 4 * N := by
    simpa [← Finset.mul_sum] using hs
  apply finite_two_common_points_of_small_complements A (by norm_num)
  simp only [ZMod.card]
  omega

theorem horizontalSection_card_eq_fiber {N : Nat} [NeZero N]
    (A : Finset (Pair N)) (y : ZMod N) :
    (horizontalSection A y).card = (A.filter fun z ↦ z.2 = y).card := by
  classical
  apply Finset.card_bij (fun x _ ↦ (x, y))
  · intro x hx
    simp only [horizontalSection, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact Finset.mem_filter.mpr ⟨hx, rfl⟩
  · intro x _ z _ heq
    exact congrArg Prod.fst heq
  · intro z hz
    obtain ⟨hzA, hzy⟩ := Finset.mem_filter.mp hz
    refine ⟨z.1, ?_, ?_⟩
    · simp only [horizontalSection, Finset.mem_filter, Finset.mem_univ, true_and]
      simpa only [← hzy] using hzA
    · exact Prod.ext rfl hzy.symm

theorem sum_horizontalSection_card {N : Nat} [NeZero N]
    (A : Finset (Pair N)) :
    (∑ y : ZMod N, (horizontalSection A y).card) = A.card := by
  have h := Finset.card_eq_sum_card_fiberwise (s := A)
    (t := Finset.univ) (f := Prod.snd) (by simp)
  simpa only [horizontalSection_card_eq_fiber] using h.symm

end LeanProofs.GowersSzemeredi

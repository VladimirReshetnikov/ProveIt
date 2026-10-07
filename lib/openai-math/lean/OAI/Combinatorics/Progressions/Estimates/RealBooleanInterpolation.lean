/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Lattices.IntegerAffineResidues

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def realBooleanInterpolant {α K : Type*} [DecidableEq α]
    (q : α → MvPolynomial K ℝ) (s : Finset α) : MvPolynomial K ℝ := ∏ r ∈ s, q r

theorem realBooleanInterpolant_eval {α K : Type*} [DecidableEq α]
    (q : α → MvPolynomial K ℝ) (s : Finset α) (vertices : Finset α → K → ℝ)
    (hq : ∀ r t, MvPolynomial.eval (vertices t) (q r) = if r ∈ t then 1 else 0)
    (t : Finset α) :
    MvPolynomial.eval (vertices t) (realBooleanInterpolant q s) =
      if s ⊆ t then 1 else 0 := by
  rw [realBooleanInterpolant, map_prod]
  by_cases hst : s ⊆ t
  · rw [ite_eq_left hst]
    exact Finset.prod_eq_one (fun r hr => by rw [hq, ite_eq_left (hst hr)])
  · rw [ite_eq_right hst]
    obtain ⟨r, hrs, hrt⟩ := Finset.not_subset.mp hst
    exact Finset.prod_eq_zero hrs (by rw [hq, ite_eq_right hrt])

theorem realBooleanInterpolant_jet {α K : Type*} [DecidableEq α]
    (q : α → MvPolynomial K ℝ) (s : Finset α) (vertices : Finset α → K → ℝ)
    (hq : ∀ r t, MvPolynomial.eval (vertices t) (q r) = if r ∈ t then 1 else 0)
    (row : Finset α) :
    booleanCoefficient (fun t => MvPolynomial.eval (vertices t)
      (realBooleanInterpolant q s)) row = if row = s then 1 else 0 := by
  simp_rw [realBooleanInterpolant_eval q s vertices hq]
  exact booleanCoefficient_monomial s row

theorem realBooleanInterpolant_degree {α K : Type*} [DecidableEq α]
    (q : α → MvPolynomial K ℝ) (s : Finset α)
    (hq : ∀ r ∈ s, (q r).totalDegree ≤ 1) :
    (realBooleanInterpolant q s).totalDegree ≤ s.card := by
  apply (MvPolynomial.totalDegree_finsetProd s q).trans
  simpa using Finset.sum_le_sum hq

theorem realBooleanInterpolant_mass {α K : Type*} [DecidableEq α]
    (q : α → MvPolynomial K ℝ) (s : Finset α) {H : ℝ} (hH : 1 ≤ H)
    (hq : ∀ r ∈ s, realPolynomialMass (q r) ≤ H) {h : ℕ} (hs : s.card ≤ h) :
    realPolynomialMass (realBooleanInterpolant q s) ≤ H ^ h := by
  apply (realPolynomialMass_prod_le s q).trans
  calc
    _ ≤ ∏ _r ∈ s, H := Finset.prod_le_prod₀ (fun r _ => realPolynomialMass_nonneg (q r)) hq
    _ = H ^ s.card := by simp
    _ ≤ H ^ h := pow_le_pow_right₀ hH hs

end Erdos3

end

end OAI

/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Lattices.IntegerFrozenChart
import OAI.Combinatorics.Progressions.Probability.AllocatedMixedLiftNormalizedMass

namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial _root_.OAI.MvPolynomial

theorem realPolynomialMass_freezePolynomial_le {I : Type*} (keep : I → Prop)
    (fixed : {i // ¬ keep i} → ℝ) (hfixed : ∀ i, |fixed i| ≤ 1)
    (P : MvPolynomial I ℝ) :
    realPolynomialMass (freezePolynomial keep fixed P) ≤ realPolynomialMass P := by
  have hf : ∀ i, realPolynomialMass (frozenCoordinate keep fixed i) ≤ 1 := by
    intro i
    classical
    by_cases hi : keep i
    · simp only [frozenCoordinate, dite_eq_left hi, realPolynomialMass_X, le_refl]
    · simpa only [frozenCoordinate, dite_eq_right hi, realPolynomialMass_C] using hfixed ⟨i, hi⟩
  have h := realPolynomialMass_substitution_le P (frozenCoordinate keep fixed)
    (M := 1) le_rfl hf le_rfl
  change realPolynomialMass (eval₂Hom C (frozenCoordinate keep fixed) P) ≤ _
  simpa only [one_pow, mul_one] using h

theorem scaleMvPolynomialAxes_freezePolynomial {I : Type*} (keep : I → Prop)
    (T : I → ℝ) (hT : ∀ i, T i ≠ 0) (fixed : {i // ¬ keep i} → ℝ)
    (P : MvPolynomial I ℝ) :
    scaleMvPolynomialAxes (fun i : {i // keep i} => T i.val) (freezePolynomial keep fixed P) =
      freezePolynomial keep (fun i => fixed i / T i.val) (scaleMvPolynomialAxes T P) := by
  classical
  apply MvPolynomial.funext
  intro x
  rw [scaleMvPolynomialAxes_eval, freezePolynomial_eval,
    freezePolynomial_eval, scaleMvPolynomialAxes_eval]
  apply congrArg (fun y => MvPolynomial.eval y P)
  funext i
  by_cases hi : keep i
  · simp only [finiteSplitPoint, dite_eq_left hi]
  · simp only [finiteSplitPoint, dite_eq_right hi]
    field_simp [hT i]

theorem normalizedMass_freezePolynomial_le {I : Type*} (keep : I → Prop)
    (T : I → ℝ) (hT : ∀ i, 0 < T i) (fixed : {i // ¬ keep i} → ℝ)
    (hfixed : ∀ i, |fixed i| ≤ T i.val) (P : MvPolynomial I ℝ) :
    realPolynomialMass
      (scaleMvPolynomialAxes (fun i : {i // keep i} => T i.val) (freezePolynomial keep fixed P)) ≤
      realPolynomialMass (scaleMvPolynomialAxes T P) := by
  rw [scaleMvPolynomialAxes_freezePolynomial keep T (fun i => (hT i).ne')]
  apply realPolynomialMass_freezePolynomial_le
  intro i
  rw [abs_div, abs_of_pos (hT i.val)]
  exact (div_le_one (hT i.val)).mpr (hfixed i)

theorem normalizedMass_neg_weightedHomogeneousComponent_freeze_le {I : Type*}
    (keep : I → Prop) (T : I → ℝ) (hT : ∀ i, 0 < T i)
    (fixed : {i // ¬ keep i} → ℝ) (hfixed : ∀ i, |fixed i| ≤ T i.val)
    (w : {i // keep i} → ℕ) (n : ℕ) (P : MvPolynomial I ℝ) :
    realPolynomialMass (scaleMvPolynomialAxes (fun i : {i // keep i} => T i.val)
      (-weightedHomogeneousComponent w n (freezePolynomial keep fixed P))) ≤
      realPolynomialMass (scaleMvPolynomialAxes T P) :=
  (normalizedMass_neg_weightedHomogeneousComponent_le _ w n _).trans
    (normalizedMass_freezePolynomial_le keep T hT fixed hfixed P)

theorem normalizedMass_neg_homogeneousComponent_freeze_int_le {I : Type*}
    (keep : I → Prop) (T : I → ℝ) (hT : ∀ i, 0 < T i)
    (fixed : {i // ¬ keep i} → ℤ) (hfixed : ∀ i, |(fixed i : ℝ)| ≤ T i.val)
    (n : ℕ) (P : MvPolynomial I ℤ) :
    realPolynomialMass (scaleMvPolynomialAxes (fun i : {i // keep i} => T i.val)
      (-homogeneousComponent n (MvPolynomial.map (Int.castRingHom ℝ) (freezePolynomial keep fixed P)))) ≤
      realPolynomialMass (scaleMvPolynomialAxes T (MvPolynomial.map (Int.castRingHom ℝ) P)) := by
  rw [freezePolynomial_map]
  exact normalizedMass_neg_weightedHomogeneousComponent_freeze_le keep T hT
    (fun i => (fixed i : ℝ)) hfixed (fun _ => 1) n (MvPolynomial.map (Int.castRingHom ℝ) P)

theorem normalizedMass_homogeneousComponent_freeze_le_top {I : Type*}
    (keep : I → Prop) (T : I → ℝ) (hT : ∀ i, 0 < T i)
    (fixed : {i // ¬ keep i} → ℝ) (n : ℕ) (P : MvPolynomial I ℝ)
    (hdegree : P.totalDegree ≤ n) :
    realPolynomialMass (scaleMvPolynomialAxes (fun i : {i // keep i} => T i.val)
      (homogeneousComponent n (freezePolynomial keep fixed P))) ≤
      realPolynomialMass (scaleMvPolynomialAxes T (homogeneousComponent n P)) := by
  rw [freezePolynomial_top keep fixed hdegree]
  exact normalizedMass_freezePolynomial_le keep T hT 0
    (fun i => by simpa only [Pi.zero_apply, abs_zero] using (hT i.val).le) _

theorem normalizedMass_neg_homogeneousComponent_freeze_le_top {I : Type*}
    (keep : I → Prop) (T : I → ℝ) (hT : ∀ i, 0 < T i)
    (fixed : {i // ¬ keep i} → ℝ) (n : ℕ) (P : MvPolynomial I ℝ)
    (hdegree : P.totalDegree ≤ n) :
    realPolynomialMass (scaleMvPolynomialAxes (fun i : {i // keep i} => T i.val)
      (-homogeneousComponent n (freezePolynomial keep fixed P))) ≤
      realPolynomialMass (scaleMvPolynomialAxes T (homogeneousComponent n P)) := by
  rw [scaleMvPolynomialAxes_neg, normalizedPolynomialMass_neg]
  exact normalizedMass_homogeneousComponent_freeze_le_top keep T hT fixed n P hdegree

end Erdos3

end

end OAI

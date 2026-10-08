/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Use MvPolynomial.coeff_sub for the frozen top-component coefficient proof.
All upstream theorem statements are unchanged. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Polynomial.BufferedSampledCurrentGradePhase

namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped Classical

variable {I R : Type*} [CommRing R]

noncomputable def frozenCoordinate (keep : I → Prop) (fixed : {i // ¬keep i} → R)
    (i : I) : MvPolynomial {i // keep i} R :=
  if hi : keep i then X ⟨i, hi⟩ else C (fixed ⟨i, hi⟩)

noncomputable def freezePolynomial (keep : I → Prop) (fixed : {i // ¬keep i} → R) :
    MvPolynomial I R →ₐ[R] MvPolynomial {i // keep i} R :=
  aeval (frozenCoordinate keep fixed)

theorem frozenCoordinate_support (keep : I → Prop) (fixed : {i // ¬keep i} → R) (i : I) :
    frozenCoordinate keep fixed i ∈ weightedSupportLE (fun _ => 1) 1 := by
  by_cases hi : keep i
  · simp only [frozenCoordinate, dite_eq_left hi]
    exact weightedSupportLE_X (R := R) (fun _ : {i // keep i} => 1) ⟨i, hi⟩
  · simp only [frozenCoordinate, dite_eq_right hi]
    exact weightedSupportLE_C (fun _ : {i // keep i} => 1) 1 (fixed ⟨i, hi⟩)

theorem freezePolynomial_support (keep : I → Prop) (fixed : {i // ¬keep i} → R)
    {P : MvPolynomial I R} {d : ℕ} (hP : P ∈ weightedSupportLE (fun _ => 1) d) :
    freezePolynomial keep fixed P ∈ weightedSupportLE (fun _ => 1) d :=
  weightedSupportLE_aeval (fun _ => 1) (fun _ => 1) _ (frozenCoordinate_support keep fixed) hP

theorem freezePolynomial_degree (keep : I → Prop) (fixed : {i // ¬keep i} → R)
    {P : MvPolynomial I R} {d : ℕ} (hP : P.totalDegree ≤ d) :
    (freezePolynomial keep fixed P).totalDegree ≤ d :=
  (mem_weightedSupportLE_one_iff _ _).mp
    (freezePolynomial_support keep fixed ((mem_weightedSupportLE_one_iff _ _).mpr hP))

theorem freezePolynomial_eval (keep : I → Prop) (fixed : {i // ¬keep i} → R)
    (P : MvPolynomial I R) (x : {i // keep i} → R) :
    eval x (freezePolynomial keep fixed P) = eval (finiteSplitPoint keep x fixed) P := by
  calc
    _ = eval (fun i => eval x (frozenCoordinate keep fixed i)) P :=
      MvPolynomial.comp_aeval_apply _ (MvPolynomial.aeval x) P
    _ = _ := by
      apply congrArg (fun y => eval y P)
      funext i
      by_cases hi : keep i <;> simp [frozenCoordinate, finiteSplitPoint, hi]

theorem freezePolynomial_sub_lower (keep : I → Prop)
    (fixed fixed' : {i // ¬keep i} → R) {P : MvPolynomial I R} {d : ℕ}
    (hP : P ∈ weightedSupportLE (fun _ => 1) d) :
    freezePolynomial keep fixed P - freezePolynomial keep fixed' P ∈
      weightedSupportLT (fun _ => 1) d := by
  apply weightedComparison_difference (fun _ => 1) (fun _ => 1)
    (freezePolynomial keep fixed) (freezePolynomial keep fixed')
    (fun i => by simpa only [freezePolynomial, aeval_X] using frozenCoordinate_support keep fixed i)
    (fun i => by simpa only [freezePolynomial, aeval_X] using frozenCoordinate_support keep fixed' i)
    _ hP
  intro i
  by_cases hi : keep i
  · simp only [freezePolynomial, aeval_X, frozenCoordinate, dite_eq_left hi, sub_self]
    exact Submodule.zero_mem _
  · simp only [freezePolynomial, aeval_X, frozenCoordinate, dite_eq_right hi, ← map_sub]
    exact weightedSupportLE_lt_succ (weightedSupportLE_C (fun _ => 1) 0 _)

theorem freezePolynomial_top_independent (keep : I → Prop)
    (fixed fixed' : {i // ¬keep i} → R) {P : MvPolynomial I R} {d : ℕ}
    (hP : P.totalDegree ≤ d) :
    homogeneousComponent d (freezePolynomial keep fixed P) =
      homogeneousComponent d (freezePolynomial keep fixed' P) := by
  have hlower := freezePolynomial_sub_lower keep fixed fixed'
    ((mem_weightedSupportLE_one_iff _ _).mpr hP)
  change weightedHomogeneousComponent (fun _ => 1) d _ =
    weightedHomogeneousComponent (fun _ => 1) d _
  ext α
  rw [coeff_weightedHomogeneousComponent, coeff_weightedHomogeneousComponent]
  split_ifs with hα
  · have hz : (freezePolynomial keep fixed P - freezePolynomial keep fixed' P).coeff α = 0 := by
      by_contra hn
      have hlt := hlower (mem_support_iff.mpr hn)
      exact (Nat.lt_irrefl d) (hα ▸ hlt)
    exact sub_eq_zero.mp (by simpa only [MvPolynomial.coeff_sub] using hz)
  · rfl

theorem freezePolynomial_map {S : Type*} [CommRing S] (φ : R →+* S)
    (keep : I → Prop) (fixed : {i // ¬keep i} → R) (P : MvPolynomial I R) :
    MvPolynomial.map φ (freezePolynomial keep fixed P) =
      freezePolynomial keep (fun i => φ (fixed i)) (MvPolynomial.map φ P) := by
  change MvPolynomial.map φ (eval₂ C (frozenCoordinate keep fixed) P) =
    eval₂ C (frozenCoordinate keep (fun i => φ (fixed i))) (MvPolynomial.map φ P)
  rw [map_eval₂]
  apply congrArg (fun f => eval₂ C f (MvPolynomial.map φ P))
  funext i
  by_cases hi : keep i <;> simp [frozenCoordinate, hi]

theorem frozenCoordinate_zero_homogeneous (keep : I → Prop) (i : I) :
    (frozenCoordinate keep (0 : {i // ¬keep i} → R) i).IsWeightedHomogeneous
      (fun _ => 1) 1 := by
  by_cases hi : keep i
  · simp only [frozenCoordinate, dite_eq_left hi]
    exact isWeightedHomogeneous_X R (fun _ : {i // keep i} => 1) ⟨i, hi⟩
  · simp only [frozenCoordinate, dite_eq_right hi, Pi.zero_apply, map_zero]
    exact isWeightedHomogeneous_zero R (fun _ : {i // keep i} => 1) 1

theorem freezePolynomial_top (keep : I → Prop) (fixed : {i // ¬keep i} → R)
    {P : MvPolynomial I R} {d : ℕ} (hP : P.totalDegree ≤ d) :
    homogeneousComponent d (freezePolynomial keep fixed P) =
      freezePolynomial keep 0 (homogeneousComponent d P) := by
  rw [freezePolynomial_top_independent keep fixed 0 hP]
  exact (aeval_weightedHomogeneousComponent (fun _ : I => 1) (fun _ => 1)
    (frozenCoordinate keep 0) (frozenCoordinate_zero_homogeneous keep) d P).symm

end Erdos3

end

end OAI

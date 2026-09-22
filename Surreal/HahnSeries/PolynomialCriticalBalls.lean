import Surreal.HahnSeries.Characteristic
import Surreal.HahnSeries.PolynomialInitialDerivative
import Surreal.HahnSeries.PolynomialNewtonProfile
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Critical-point counts in occupied valuation balls

This proves `polynomial:thm:criticalballs` for Hahn-coefficient polynomials.
Counts use the native root multiset, so every root occurrence contributes its
multiplicity. Splitting is required explicitly for the original polynomial
and for the derivative whose roots are counted. No algebraic closedness of
the Hahn field is assumed.

In residue characteristic zero, a ball with `k` roots has exactly `k-r` roots
of the `r`th derivative for `r ≤ k`. Including the zeroth derivative is
harmless; any positive derivative order in this range forces occupation.
Residue-direction counts are the root multiplicities of the differentiated
initial polynomial. The all-root-ball containment assertion of
`polynomial:cor:nearest` is proved for both closed and open balls.
-/

namespace Surreal.HahnSeries

open Polynomial Finset
open scoped _root_.HahnSeries Classical

noncomputable section

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ]
  [IsOrderedAddMonoid Γ] [Field K]

/-- The multiplicity-counted roots in the closed valuation ball. -/
def closedBallRootCount (a : K⟦Γ⟧) (ρ : Γ) (P : K⟦Γ⟧[X]) : ℕ :=
  (P.roots.filter (fun α => (ρ : WithTop Γ) ≤ (α - a).orderTop)).card

/-- The multiplicity-counted roots in the open valuation ball. Roots at
the center have displacement valuation `⊤` and are included. -/
def openBallRootCount (a : K⟦Γ⟧) (ρ : Γ) (P : K⟦Γ⟧[X]) : ℕ :=
  (P.roots.filter (fun α => (ρ : WithTop Γ) < (α - a).orderTop)).card

private theorem split_eq_occurrences (P : K⟦Γ⟧[X]) (hs : P.Splits) :
    P = C P.leadingCoeff * ∏ α : P.roots, (X - C (α : K⟦Γ⟧)) := by
  nth_rewrite 1 [hs.eq_prod_roots]
  congr 1
  exact (congrArg Multiset.prod
    (Multiset.map_univ P.roots (fun α => (X : K⟦Γ⟧[X]) - C α))).symm

private theorem root_filter_card_occurrences (P : K⟦Γ⟧[X])
    (f : K⟦Γ⟧ → Prop) [DecidablePred f] :
    (P.roots.filter f).card =
      ((univ : Finset P.roots).filter (fun (α : P.roots) => f (α : K⟦Γ⟧))).card := by
  have h := congrArg (fun s : Multiset K⟦Γ⟧ => (s.filter f).card)
    (Multiset.map_univ_coe P.roots)
  simpa only [Multiset.filter_map, Multiset.card_map, Function.comp_def,
    Finset.card, Finset.filter_val] using h.symm

/-- The native-root-multiset form of `polynomial:eq:closedcount`. -/
theorem closedBallRootCount_eq_natDegree (a : K⟦Γ⟧) (ρ : Γ) (P : K⟦Γ⟧[X])
    (hP : P ≠ 0) (hs : P.Splits) :
    closedBallRootCount a ρ P = (gaussInitial a ρ P).natDegree := by
  have h := natDegree_gaussInitial_split a ρ P.leadingCoeff
    (leadingCoeff_ne_zero.mpr hP) (univ : Finset P.roots)
    (fun (α : P.roots) => (α : K⟦Γ⟧))
  rw [← split_eq_occurrences P hs] at h
  simpa only [closedBallRootCount, root_filter_card_occurrences, closedRootIndices] using h.symm

/-- The native-root-multiset form of `polynomial:eq:opencount`. -/
theorem openBallRootCount_eq_natTrailingDegree (a : K⟦Γ⟧) (ρ : Γ) (P : K⟦Γ⟧[X])
    (hP : P ≠ 0) (hs : P.Splits) :
    openBallRootCount a ρ P = (gaussInitial a ρ P).natTrailingDegree := by
  have h := natTrailingDegree_gaussInitial_split a ρ P.leadingCoeff
    (leadingCoeff_ne_zero.mpr hP) (univ : Finset P.roots)
    (fun (α : P.roots) => (α : K⟦Γ⟧))
  rw [← split_eq_occurrences P hs] at h
  simpa only [openBallRootCount, root_filter_card_occurrences] using h.symm

/-- Native root counts in a residue direction are precisely initial-polynomial
root multiplicities (`polynomial:thm:initialroots`). -/
theorem directionRootCount_eq_rootMultiplicity (a : K⟦Γ⟧) (ρ : Γ) (P : K⟦Γ⟧[X])
    (hP : P ≠ 0) (hs : P.Splits) (d : K) :
    openBallRootCount (a + _root_.HahnSeries.single ρ d) ρ P =
      (gaussInitial a ρ P).rootMultiplicity d := by
  have h := rootMultiplicity_gaussInitial_split_direction a ρ P.leadingCoeff
    (leadingCoeff_ne_zero.mpr hP) (univ : Finset P.roots)
    (fun (α : P.roots) => (α : K⟦Γ⟧)) d
  rw [← split_eq_occurrences P hs] at h
  simpa only [openBallRootCount, root_filter_card_occurrences] using h.symm

variable [CharZero K]

private theorem natDegree_iterate_derivative_eq (I : K[X]) (r : ℕ) :
    (derivative^[r] I).natDegree = I.natDegree - r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply', Polynomial.natDegree_derivative, ih]
    omega

private theorem iterate_derivative_ne_zero (I : K[X]) (hI : I ≠ 0) (r : ℕ)
    (hr : r ≤ I.natDegree) : derivative^[r] I ≠ 0 := by
  cases r with
  | zero => simpa using hI
  | succ r =>
    rw [Function.iterate_succ_apply', Polynomial.derivative_ne_zero,
      natDegree_iterate_derivative_eq]
    omega

private theorem natTrailingDegree_iterate_derivative_eq (I : K[X]) (r : ℕ)
    (hr : r ≤ I.natTrailingDegree) :
    (derivative^[r] I).natTrailingDegree = I.natTrailingDegree - r := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hir := ih (Nat.le_of_succ_le hr)
    have hroot : (derivative^[r] I).IsRoot 0 := by
      apply (Polynomial.rootMultiplicity_pos'.mp _).2
      rw [Polynomial.rootMultiplicity_eq_natTrailingDegree', hir]
      omega
    rw [Function.iterate_succ_apply', ← Polynomial.rootMultiplicity_eq_natTrailingDegree',
      Polynomial.derivative_rootMultiplicity_of_root hroot,
      Polynomial.rootMultiplicity_eq_natTrailingDegree', hir]
    omega

/-- The relevant derivative cannot be zero within the allowed initial-degree
range. This prevents the native zero-polynomial root convention from entering
the critical-ball counts. -/
theorem iterateDerivative_ne_zero_of_initial_degree (a : K⟦Γ⟧) (ρ : Γ)
    (P : K⟦Γ⟧[X]) (hP : P ≠ 0) (r : ℕ) (hr : r ≤ (gaussInitial a ρ P).natDegree) :
    derivative^[r] P ≠ 0 := by
  have hI := iterate_derivative_ne_zero (gaussInitial a ρ P)
    (gaussInitial_ne_zero a ρ P hP) r hr
  intro hz
  have h := (initialIterateDerivative a ρ P r hr).2
  rw [hz] at h
  apply hI
  simpa [gaussInitial] using h.symm

/-- Closed occupied-ball conservation in `polynomial:thm:criticalballs`:
the `r`th derivative has exactly `k-r` roots when the original count is `k`
and `r ≤ k`. Both splitting hypotheses are explicit. -/
theorem closedBallRootCount_iterate_derivative (a : K⟦Γ⟧) (ρ : Γ)
    (P : K⟦Γ⟧[X]) (hP : P ≠ 0) (hs : P.Splits) (r : ℕ)
    (hsr : (derivative^[r] P).Splits) (hr : r ≤ closedBallRootCount a ρ P) :
    closedBallRootCount a ρ (derivative^[r] P) = closedBallRootCount a ρ P - r := by
  rw [closedBallRootCount_eq_natDegree a ρ P hP hs] at hr ⊢
  rw [closedBallRootCount_eq_natDegree a ρ (derivative^[r] P)
      (iterateDerivative_ne_zero_of_initial_degree a ρ P hP r hr) hsr,
    (initialIterateDerivative a ρ P r hr).2, natDegree_iterate_derivative_eq]

/-- Open occupied-ball conservation in `polynomial:thm:criticalballs`.
The bound is the open-ball count, not merely the closed-ball count. -/
theorem openBallRootCount_iterate_derivative (a : K⟦Γ⟧) (ρ : Γ)
    (P : K⟦Γ⟧[X]) (hP : P ≠ 0) (hs : P.Splits) (r : ℕ)
    (hsr : (derivative^[r] P).Splits) (hr : r ≤ openBallRootCount a ρ P) :
    openBallRootCount a ρ (derivative^[r] P) = openBallRootCount a ρ P - r := by
  rw [openBallRootCount_eq_natTrailingDegree a ρ P hP hs] at hr ⊢
  have hrdeg := hr.trans (gaussInitial a ρ P).natTrailingDegree_le_natDegree
  rw [openBallRootCount_eq_natTrailingDegree a ρ (derivative^[r] P)
      (iterateDerivative_ne_zero_of_initial_degree a ρ P hP r hrdeg) hsr,
    (initialIterateDerivative a ρ P r hrdeg).2,
    natTrailingDegree_iterate_derivative_eq _ r hr]

/-- All derivative residue-direction multiplicities can be read from the
corresponding derivative of the initial polynomial. This includes the final
first-derivative assertion of `polynomial:thm:criticalballs`. -/
theorem directionRootCount_iterate_derivative (a : K⟦Γ⟧) (ρ : Γ)
    (P : K⟦Γ⟧[X]) (hP : P ≠ 0) (r : ℕ)
    (hsr : (derivative^[r] P).Splits) (hr : r ≤ (gaussInitial a ρ P).natDegree) (d : K) :
    openBallRootCount (a + _root_.HahnSeries.single ρ d) ρ (derivative^[r] P) =
      (derivative^[r] (gaussInitial a ρ P)).rootMultiplicity d := by
  rw [directionRootCount_eq_rootMultiplicity a ρ (derivative^[r] P)
      (iterateDerivative_ne_zero_of_initial_degree a ρ P hP r hr) hsr d,
    (initialIterateDerivative a ρ P r hr).2]

/-- The critical-point multiplicity in each residue direction is the
multiplicity of that residue as a root of `I′`. -/
theorem critical_direction_count (a : K⟦Γ⟧) (ρ : Γ)
    (P : K⟦Γ⟧[X]) (hP : P ≠ 0) (hsd : P.derivative.Splits)
    (hdeg : 0 < (gaussInitial a ρ P).natDegree) (d : K) :
    openBallRootCount (a + _root_.HahnSeries.single ρ d) ρ P.derivative =
      (gaussInitial a ρ P).derivative.rootMultiplicity d := by
  simpa only [Function.iterate_one] using directionRootCount_iterate_derivative a ρ P hP 1
    (by simpa only [Function.iterate_one] using hsd) hdeg d

section GaussLucas

/-- The closed-ball valuative Gauss--Lucas assertion, the first clause of
`polynomial:cor:nearest`: a closed valuation ball containing every root of a
nonconstant split polynomial also contains every critical point, provided
the derivative splits. -/
theorem criticalPoint_mem_closedBall (a : K⟦Γ⟧) (ρ : Γ) (P : K⟦Γ⟧[X])
    (hdeg : 0 < P.natDegree) (hs : P.Splits) (hsd : P.derivative.Splits)
    (hall : ∀ α, P.IsRoot α → (ρ : WithTop Γ) ≤ (α - a).orderTop)
    {w : K⟦Γ⟧} (hw : P.derivative.IsRoot w) : (ρ : WithTop Γ) ≤ (w - a).orderTop := by
  have hP : P ≠ 0 := by intro hz; simp [hz] at hdeg
  have hd : P.derivative ≠ 0 := Polynomial.derivative_ne_zero.mpr (ne_of_gt hdeg)
  have hf : P.roots.filter (fun α => (ρ : WithTop Γ) ≤ (α - a).orderTop) = P.roots :=
    Multiset.filter_eq_self.mpr (fun α hα => hall α ((mem_roots hP).mp hα))
  have hc : closedBallRootCount a ρ P = P.natDegree := by
    rw [closedBallRootCount, hf, hs.natDegree_eq_card_roots]
  have hcd : closedBallRootCount a ρ P.derivative = P.natDegree - 1 := by
    have h := closedBallRootCount_iterate_derivative a ρ P hP hs 1
      (by simpa only [Function.iterate_one] using hsd) (by rw [hc]; exact hdeg)
    simpa only [Function.iterate_one, hc] using h
  have hcard : (P.derivative.roots.filter
      (fun α => (ρ : WithTop Γ) ≤ (α - a).orderTop)).card = P.derivative.roots.card := by
    change closedBallRootCount a ρ P.derivative = _
    rw [hcd, ← hsd.natDegree_eq_card_roots, Polynomial.natDegree_derivative]
  have hfd := Multiset.eq_of_le_of_card_le
    (Multiset.filter_le (fun α => (ρ : WithTop Γ) ≤ (α - a).orderTop) P.derivative.roots)
    hcard.ge
  exact (Multiset.filter_eq_self.mp hfd) w ((mem_roots hd).mpr hw)

/-- The open-ball valuative Gauss--Lucas assertion, also included in
`polynomial:cor:nearest`. The proof uses the occupied open-ball count and
does not infer open containment merely from closed containment. -/
theorem criticalPoint_mem_openBall (a : K⟦Γ⟧) (ρ : Γ) (P : K⟦Γ⟧[X])
    (hdeg : 0 < P.natDegree) (hs : P.Splits) (hsd : P.derivative.Splits)
    (hall : ∀ α, P.IsRoot α → (ρ : WithTop Γ) < (α - a).orderTop)
    {w : K⟦Γ⟧} (hw : P.derivative.IsRoot w) : (ρ : WithTop Γ) < (w - a).orderTop := by
  have hP : P ≠ 0 := by intro hz; simp [hz] at hdeg
  have hd : P.derivative ≠ 0 := Polynomial.derivative_ne_zero.mpr (ne_of_gt hdeg)
  have hf : P.roots.filter (fun α => (ρ : WithTop Γ) < (α - a).orderTop) = P.roots :=
    Multiset.filter_eq_self.mpr (fun α hα => hall α ((mem_roots hP).mp hα))
  have hc : openBallRootCount a ρ P = P.natDegree := by
    rw [openBallRootCount, hf, hs.natDegree_eq_card_roots]
  have hcd : openBallRootCount a ρ P.derivative = P.natDegree - 1 := by
    have h := openBallRootCount_iterate_derivative a ρ P hP hs 1
      (by simpa only [Function.iterate_one] using hsd) (by rw [hc]; exact hdeg)
    simpa only [Function.iterate_one, hc] using h
  have hcard : (P.derivative.roots.filter
      (fun α => (ρ : WithTop Γ) < (α - a).orderTop)).card = P.derivative.roots.card := by
    change openBallRootCount a ρ P.derivative = _
    rw [hcd, ← hsd.natDegree_eq_card_roots, Polynomial.natDegree_derivative]
  have hfd := Multiset.eq_of_le_of_card_le
    (Multiset.filter_le (fun α => (ρ : WithTop Γ) < (α - a).orderTop) P.derivative.roots)
    hcard.ge
  exact (Multiset.filter_eq_self.mp hfd) w ((mem_roots hd).mpr hw)

end GaussLucas

end

end Surreal.HahnSeries

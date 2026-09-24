import Surreal.HahnSeries.PolynomialInitialRoots
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Data.Multiset.Fintype

/-!
# Newton profiles and root valuations

The fixed-scale root-valuation rule of `polynomial:thm:newton` in
`docs/surcomplex/polynomial-algebra/article.tex`. A lower face is encoded by
its active coefficient indices, without embedding the exponent group in the
reals. Its horizontal span counts root occurrences at that finite valuation.

Splitting is an explicit hypothesis. The exponent group is an arbitrary
set-sized ordered abelian group; divisibility, algebraic closedness, and a
surreal normal-form identification are not assumed.
-/

namespace Surreal.HahnSeries

open Polynomial Finset
open scoped _root_.HahnSeries Classical

noncomputable section

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ]
  [IsOrderedAddMonoid Γ] [Field K]

/-- The active coefficient indices at center zero. -/
def newtonActiveIndices (P : K⟦Γ⟧[X]) (ρ : Γ) : Finset ℕ :=
  (gaussInitial 0 ρ P).support

/-- The horizontal span of the lower face at weight `ρ`. -/
def newtonSpan (P : K⟦Γ⟧[X]) (ρ : Γ) : ℕ :=
  (gaussInitial 0 ρ P).natDegree - (gaussInitial 0 ρ P).natTrailingDegree

/-- A breakpoint is a scale where at least two coefficient indices attain
the weighted minimum. This is an algebraic definition, requiring no topology. -/
def newtonBreakpoint (P : K⟦Γ⟧[X]) (ρ : Γ) : Prop :=
  1 < (newtonActiveIndices P ρ).card

/-- Root occurrences of exactly the finite valuation `ρ`. Zero roots have
valuation `⊤`, so are excluded automatically. -/
def rootValuationCount (P : K⟦Γ⟧[X]) (ρ : Γ) : ℕ :=
  (P.roots.filter (fun α => α.orderTop = (ρ : WithTop Γ))).card

/-- Active membership is exactly attainment of the weighted coefficient minimum. -/
theorem mem_newtonActiveIndices (P : K⟦Γ⟧[X]) (hP : P ≠ 0) (ρ : Γ) (j : ℕ) :
    j ∈ newtonActiveIndices P ρ ↔
      (P.coeff j).orderTop + (j • ρ : Γ) = weightedGaussVal 0 ρ P := by
  simpa only [newtonActiveIndices, mem_support_iff, taylor_zero] using
    coeff_gaussInitial_ne_zero_iff 0 ρ P hP j

/-- The endpoints used in `newtonSpan` are the smallest and largest
indices attaining the source's profile `φ_P(ρ)`. -/
theorem newton_active_extrema (P : K⟦Γ⟧[X]) (hP : P ≠ 0) (ρ : Γ) :
    IsLeast {j | (P.coeff j).orderTop + (j • ρ : Γ) = weightedGaussVal 0 ρ P}
        (gaussInitial 0 ρ P).natTrailingDegree ∧
      IsGreatest {j | (P.coeff j).orderTop + (j • ρ : Γ) = weightedGaussVal 0 ρ P}
        (gaussInitial 0 ρ P).natDegree := by
  simpa only [taylor_zero] using gaussInitial_active_extrema 0 ρ P hP

private theorem split_eq_occurrence_product (P : K⟦Γ⟧[X]) (hs : P.Splits) :
    P = C P.leadingCoeff * ∏ α : P.roots, (X - C (α : K⟦Γ⟧)) := by
  nth_rewrite 1 [hs.eq_prod_roots]
  congr 1
  exact (congrArg Multiset.prod
    (Multiset.map_univ P.roots (fun α => (X : K⟦Γ⟧[X]) - C α))).symm

private theorem root_filter_card_eq_occurrence_filter (P : K⟦Γ⟧[X])
    (f : K⟦Γ⟧ → Prop) [DecidablePred f] :
    (P.roots.filter f).card =
      ((univ : Finset P.roots).filter (fun (α : P.roots) => f (α : K⟦Γ⟧))).card := by
  have h := congrArg (fun s : Multiset K⟦Γ⟧ => (s.filter f).card)
    (Multiset.map_univ_coe P.roots)
  simpa only [Multiset.filter_map, Multiset.card_map, Function.comp_def,
    Finset.card, Finset.filter_val] using h.symm

/-- Newton's exact root-valuation rule: the lower-face span counts all
root occurrences of valuation `ρ`, with multiplicity. -/
theorem rootValuationCount_eq_newtonSpan (P : K⟦Γ⟧[X]) (hP : P ≠ 0)
    (hs : P.Splits) (ρ : Γ) : rootValuationCount P ρ = newtonSpan P ρ := by
  have h := shell_count_gaussInitial_split 0 ρ P.leadingCoeff
    (leadingCoeff_ne_zero.mpr hP) (univ : Finset P.roots) (fun (α : P.roots) => (α : K⟦Γ⟧))
  rw [← split_eq_occurrence_product P hs] at h
  simpa only [rootValuationCount, root_filter_card_eq_occurrence_filter, newtonSpan, sub_zero]
    using h

/-- A positive horizontal span is equivalent to at least two active indices. -/
theorem newtonSpan_pos_iff_breakpoint (P : K⟦Γ⟧[X]) (hP : P ≠ 0) (ρ : Γ) :
    0 < newtonSpan P ρ ↔ newtonBreakpoint P ρ := by
  have hI := gaussInitial_ne_zero 0 ρ P hP
  have hlow : (gaussInitial 0 ρ P).natTrailingDegree ∈ newtonActiveIndices P ρ :=
    mem_support_iff.mpr (coeff_natTrailingDegree_ne_zero.mpr hI)
  have hhigh : (gaussInitial 0 ρ P).natDegree ∈ newtonActiveIndices P ρ :=
    mem_support_iff.mpr (by rw [coeff_natDegree]; exact leadingCoeff_ne_zero.mpr hI)
  rw [newtonSpan, Nat.sub_pos_iff_lt, newtonBreakpoint, Finset.one_lt_card]
  constructor
  · intro h
    exact ⟨_, hlow, _, hhigh, ne_of_lt h⟩
  · rintro ⟨i, hi, j, hj, hij⟩
    have hi0 := natTrailingDegree_le_of_ne_zero (mem_support_iff.mp hi)
    have hin := le_natDegree_of_ne_zero (mem_support_iff.mp hi)
    have hj0 := natTrailingDegree_le_of_ne_zero (mem_support_iff.mp hj)
    have hjn := le_natDegree_of_ne_zero (mem_support_iff.mp hj)
    omega

/-- Positive shell count, nonzero face span, and the breakpoint condition
are equivalent for a split polynomial. -/
theorem rootValuationCount_pos_iff_breakpoint (P : K⟦Γ⟧[X]) (hP : P ≠ 0)
    (hs : P.Splits) (ρ : Γ) :
    0 < rootValuationCount P ρ ↔ newtonBreakpoint P ρ := by
  rw [rootValuationCount_eq_newtonSpan P hP hs, newtonSpan_pos_iff_breakpoint P hP]

/-- The tropical minimum is attained at least twice exactly when a
nonzero root of that finite valuation exists, under the explicit splitting
hypothesis. -/
theorem newtonBreakpoint_iff_exists_root (P : K⟦Γ⟧[X]) (hP : P ≠ 0)
    (hs : P.Splits) (ρ : Γ) :
    newtonBreakpoint P ρ ↔ ∃ α : K⟦Γ⟧, P.IsRoot α ∧ α ≠ 0 ∧
      α.orderTop = (ρ : WithTop Γ) := by
  rw [← rootValuationCount_pos_iff_breakpoint P hP hs, rootValuationCount,
    Multiset.card_pos_iff_exists_mem]
  constructor
  · rintro ⟨α, hα⟩
    obtain ⟨hm, ho⟩ := Multiset.mem_filter.mp hα
    refine ⟨α, (mem_roots hP).mp hm, ?_, ho⟩
    intro hz
    simp [hz] at ho
  · rintro ⟨α, hroot, _, ho⟩
    exact ⟨α, Multiset.mem_filter.mpr ⟨(mem_roots hP).mpr hroot, ho⟩⟩

/-- Every nonzero root's order is a Newton breakpoint. -/
theorem isRoot_newtonBreakpoint_order (P : K⟦Γ⟧[X]) (hP : P ≠ 0) (hs : P.Splits)
    {α : K⟦Γ⟧} (hα : P.IsRoot α) (hα0 : α ≠ 0) : newtonBreakpoint P α.order := by
  apply (newtonBreakpoint_iff_exists_root P hP hs α.order).mpr
  exact ⟨α, hα, hα0, (_root_.HahnSeries.order_eq_orderTop_of_ne_zero hα0).symm⟩

/-- Roots at the center are exactly the roots of infinite valuation, and
are counted separately by their exact algebraic multiplicity. -/
theorem infinite_valuation_root_count (P : K⟦Γ⟧[X]) :
    (P.roots.filter (fun α => α.orderTop = ⊤)).card = P.rootMultiplicity 0 := by
  rw [← count_roots, Multiset.count_eq_card_filter_eq]
  congr 1
  apply Multiset.filter_congr
  intro α _
  simp only [_root_.HahnSeries.orderTop_eq_top, eq_comm]

/-- A lower face with extremal active indices `j` and `k` accounts for
exactly `k-j` root occurrences at its scale. -/
theorem rootValuationCount_eq_of_active_extrema (P : K⟦Γ⟧[X]) (hP : P ≠ 0)
    (hs : P.Splits) (ρ : Γ) {j k : ℕ}
    (hj : IsLeast {i | (P.coeff i).orderTop + (i • ρ : Γ) = weightedGaussVal 0 ρ P} j)
    (hk : IsGreatest {i | (P.coeff i).orderTop + (i • ρ : Γ) = weightedGaussVal 0 ρ P} k) :
    rootValuationCount P ρ = k - j := by
  have he := newton_active_extrema P hP ρ
  rw [hj.unique he.1, hk.unique he.2]
  exact rootValuationCount_eq_newtonSpan P hP hs ρ

omit [IsOrderedAddMonoid Γ] in
private theorem order_eq_of_orderTop_eq (α : K⟦Γ⟧) (ρ : Γ)
    (h : α.orderTop = (ρ : WithTop Γ)) : α.order = ρ := by
  have hα : α ≠ 0 := by intro hz; simp [hz] at h
  apply WithTop.coe_injective
  rw [_root_.HahnSeries.order_eq_orderTop_of_ne_zero hα, h]

omit [IsOrderedAddMonoid Γ] in
private theorem nonzero_residue_iff_order_leadingCoeff (α : K⟦Γ⟧) (ρ : Γ)
    (d : K) (hd : d ≠ 0) :
    (ρ : WithTop Γ) ≤ α.orderTop ∧ α.coeff ρ = d ↔
      α.orderTop = (ρ : WithTop Γ) ∧ α.leadingCoeff = d := by
  constructor
  · rintro ⟨hord, hc⟩
    have hc0 : α.coeff ρ ≠ 0 := hc ▸ hd
    have heq : α.orderTop = (ρ : WithTop Γ) :=
      le_antisymm (_root_.HahnSeries.orderTop_le_of_coeff_ne_zero hc0) hord
    refine ⟨heq, ?_⟩
    rw [_root_.HahnSeries.leadingCoeff_eq, order_eq_of_orderTop_eq α ρ heq, hc]
  · rintro ⟨hord, hc⟩
    refine ⟨hord.ge, ?_⟩
    rwa [_root_.HahnSeries.leadingCoeff_eq, order_eq_of_orderTop_eq α ρ hord] at hc

/-- A nonzero root of the face's initial polynomial counts precisely the
original roots of that valuation with that leading coefficient. This is the
leading-coefficient multiplicity assertion of `polynomial:thm:newton`. -/
theorem rootMultiplicity_initial_eq_leadingCoeff_count (P : K⟦Γ⟧[X]) (hP : P ≠ 0)
    (hs : P.Splits) (ρ : Γ) (d : K) (hd : d ≠ 0) :
    (gaussInitial 0 ρ P).rootMultiplicity d =
      (P.roots.filter (fun α => α.orderTop = (ρ : WithTop Γ) ∧ α.leadingCoeff = d)).card := by
  have h := rootMultiplicity_gaussInitial_split 0 ρ P.leadingCoeff
    (leadingCoeff_ne_zero.mpr hP) (univ : Finset P.roots)
    (fun (α : P.roots) => (α : K⟦Γ⟧)) d
  rw [← split_eq_occurrence_product P hs] at h
  rw [root_filter_card_eq_occurrence_filter]
  simp only [sub_zero] at h
  rw [h]
  congr 1
  apply Finset.filter_congr
  intro α _
  exact nonzero_residue_iff_order_leadingCoeff (α : K⟦Γ⟧) ρ d hd

/-- The finite set of valuations of nonzero root occurrences. Under
splitting it is exactly the set of Newton breakpoints. -/
def newtonBreakpointValues (P : K⟦Γ⟧[X]) : Finset Γ :=
  (P.roots.toFinset.filter (fun α => α ≠ 0)).image _root_.HahnSeries.order

/-- Finite root orders characterize membership in the breakpoint set. -/
theorem mem_newtonBreakpointValues (P : K⟦Γ⟧[X]) (hP : P ≠ 0) (hs : P.Splits)
    (ρ : Γ) : ρ ∈ newtonBreakpointValues P ↔ newtonBreakpoint P ρ := by
  rw [newtonBreakpointValues, Finset.mem_image, newtonBreakpoint_iff_exists_root P hP hs]
  constructor
  · rintro ⟨α, hα, ho⟩
    obtain ⟨hm, hα0⟩ := Finset.mem_filter.mp hα
    refine ⟨α, (mem_roots hP).mp (Multiset.mem_toFinset.mp hm), hα0, ?_⟩
    rw [← _root_.HahnSeries.order_eq_orderTop_of_ne_zero hα0, ho]
  · rintro ⟨α, hroot, hα0, ho⟩
    exact ⟨α, Finset.mem_filter.mpr
      ⟨Multiset.mem_toFinset.mpr ((mem_roots hP).mpr hroot), hα0⟩,
      order_eq_of_orderTop_eq α ρ ho⟩

/-- The Newton profile has finitely many breakpoints, with no real
embedding or rational-slope construction required. -/
theorem finite_newtonBreakpoints (P : K⟦Γ⟧[X]) (hP : P ≠ 0) (hs : P.Splits) :
    {ρ : Γ | newtonBreakpoint P ρ}.Finite := by
  apply (newtonBreakpointValues P).finite_toSet.subset
  intro ρ hρ
  exact (mem_newtonBreakpointValues P hP hs ρ).mpr hρ

end

end Surreal.HahnSeries

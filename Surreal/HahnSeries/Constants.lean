import Mathlib.RingTheory.HahnSeries.Summable

/-!
# Strong summability of constant Hahn series

The two conditions in `a:def:summable` of
`docs/surcomplex/analysis/article.tex` are exactly those stored by Mathlib's
`HahnSeries.SummableFamily`: a partially well-ordered union of supports and
finite coefficient incidence. For a linearly ordered exponent group, partial
well-ordering is equivalent to well-foundedness of the support.

Constants have support contained in `{0}`, but this alone does not make an
infinite family summable. This file proves `a:rule:clauseii` for constant
families and the nonsummability assertion in `a:ex:notsummable`. No topology,
convergence of ordinary series, or surreal normal-form bridge is asserted.
-/

namespace Surreal.HahnSeries

open _root_.HahnSeries

variable {Γ R ι : Type*} [PartialOrder Γ] [Zero Γ]

section AddCommMonoid

variable [AddCommMonoid R]

/-- The well-ordering clause of `a:def:summable` always holds for a family
of constants, because every support is contained in the singleton `{0}`. -/
theorem isPWO_iUnion_support_constants (c : ι → R) :
    (⋃ i, (single (0 : Γ) (c i)).support).IsPWO :=
  (Set.isPWO_singleton (0 : Γ)).mono
    (Set.iUnion_subset fun _ => support_single_subset)

/-- `a:rule:clauseii`: a family of constant Hahn series is strongly summable
exactly when only finitely many coefficients in that family are nonzero.
Summability is expressed using the existing Mathlib bundled family. -/
theorem summable_constants_iff (c : ι → R) :
    (∃ s : SummableFamily Γ R ι, ∀ i, s i = single 0 (c i)) ↔
      c.HasFiniteSupport := by
  constructor
  · rintro ⟨s, hs⟩
    simpa only [hs, coeff_single_same] using s.finite_co_support (0 : Γ)
  · intro hc
    refine ⟨{
      toFun := fun i => single 0 (c i)
      isPWO_iUnion_support' := isPWO_iUnion_support_constants c
      finite_co_support' := fun g => hc.subset ?_
    }, fun _ => rfl⟩
    intro i hi
    change c i ≠ 0
    intro hci
    exact hi (by simp [hci])

/-- The sum in `a:def:summable`, for a summable constant family, is the
constant obtained from its finite coefficient sum. -/
theorem hsum_constants (c : ι → R) (s : SummableFamily Γ R ι)
    (hs : ∀ i, s i = single 0 (c i)) :
    s.hsum = single 0 (∑ᶠ i, c i) := by
  ext g
  by_cases hg : g = 0
  · subst g
    simp only [SummableFamily.coeff_hsum, hs, coeff_single_same]
  · simp only [SummableFamily.coeff_hsum, hs, coeff_single_of_ne hg, finsum_zero]

/-- The finiteness-clause obstruction in `a:rule:clauseii`: infinitely many
nonzero constants cannot form a strongly summable family. -/
theorem not_summable_constants_of_infinite [Infinite ι] (c : ι → R)
    (hc : ∀ i, c i ≠ 0) :
    ¬ ∃ s : SummableFamily Γ R ι, ∀ i, s i = single 0 (c i) := by
  intro hs
  have hfinite := (summable_constants_iff (Γ := Γ) c).mp hs
  exact Set.infinite_univ (hfinite.subset fun i _ => hc i)

end AddCommMonoid

/-- The nonsummability part of `a:ex:notsummable`, valid over any
characteristic-zero coefficient field, in particular the real or complex
numbers. Each term represents the constant coefficient `2⁻ⁿ`; all contribute
at exponent zero. This is not a claim about ordinary analytic convergence. -/
theorem not_summable_geometric_constants [Field R] [CharZero R] :
    ¬ ∃ s : SummableFamily Γ R ℕ,
      ∀ n, s n = single 0 (((2 : R)⁻¹) ^ n) :=
  not_summable_constants_of_infinite _
    (fun n => pow_ne_zero n (inv_ne_zero (two_ne_zero : (2 : R) ≠ 0)))

end Surreal.HahnSeries

import Surreal.Surcomplex.FineDerivative
import Surreal.Surcomplex.StandardPartTopology

/-!
# Nonconstant functions with zero fine derivative

The characteristic function of the clopen infinitesimal ideal is constant
on every infinitesimal coset, has zero fine derivative at every point, and
has different values at zero and one. This supplies the counterexample in
`found:rem:fourtypes` on each actual field. Ordinary connected-domain
uniqueness principles therefore need additional hypotheses here.
-/

open Filter Topology
open scoped Classical

namespace Surreal

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K]

/-- A clopen indicator is locally constant, hence has zero fine derivative. -/
theorem fineHasDerivAt_indicator_of_isClopen {s : Set K} (hs : IsClopen s) (a : K) :
    FineHasDerivAt (s.indicator (fun _ => (1 : K))) 0 a := by
  by_cases ha : a ∈ s
  · apply (FineHasDerivAt.const (1 : K) a).congr_of_eventuallyEq
    filter_upwards [hs.isOpen.mem_nhds ha] with x hx
    simp only [Set.indicator_of_mem hx]
  · apply (FineHasDerivAt.const (0 : K) a).congr_of_eventuallyEq
    filter_upwards [hs.isClosed.isOpen_compl.mem_nhds ha] with x hx
    simp only [Set.indicator_of_notMem hx]

end Surreal

universe u

namespace Surreal.Foundations.SignSequence

noncomputable section

/-- The zero-monad indicator, with values in the actual sign field. -/
def infinitesimalIndicator : SignSequence.{u} → SignSequence.{u} :=
  Set.indicator {x | IsInfinitesimal x} (fun _ => 1)

@[simp] theorem infinitesimalIndicator_zero :
    infinitesimalIndicator (0 : SignSequence.{u}) = 1 :=
  Set.indicator_of_mem infinitesimal_zero _

@[simp] theorem infinitesimalIndicator_one :
    infinitesimalIndicator (1 : SignSequence.{u}) = 0 := by
  have h : ¬ IsInfinitesimal (1 : SignSequence.{u}) := by
    intro h
    have hh := (standardPart_eq_zero_iff finite_one).mpr h
    simp only [standardPart_one, one_ne_zero] at hh
  exact Set.indicator_of_notMem h _

/-- Adding an infinitesimal never changes the indicator. -/
theorem infinitesimalIndicator_add (x ε : SignSequence.{u}) (hε : IsInfinitesimal ε) :
    infinitesimalIndicator (x + ε) = infinitesimalIndicator x := by
  have hi : IsInfinitesimal (x + ε) ↔ IsInfinitesimal x := by
    constructor
    · intro h
      simpa only [add_neg_cancel_right] using infinitesimal_add h (infinitesimal_neg hε)
    · exact fun h => infinitesimal_add h hε
  simp only [infinitesimalIndicator, Set.indicator_apply, Set.mem_setOf_eq, hi]

theorem fineHasDerivAt_infinitesimalIndicator (a : SignSequence.{u}) :
    FineHasDerivAt infinitesimalIndicator 0 a :=
  fineHasDerivAt_indicator_of_isClopen isClopen_setOf_isInfinitesimal a

theorem infinitesimalIndicator_not_constant :
    ¬ ∃ c : SignSequence.{u}, ∀ x, infinitesimalIndicator x = c := by
  rintro ⟨c, hc⟩
  have h := (hc 0).trans (hc 1).symm
  simp only [infinitesimalIndicator_zero, infinitesimalIndicator_one, one_ne_zero] at h

end
end Surreal.Foundations.SignSequence

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- The zero-monad indicator, with values in the actual surcomplex field. -/
def infinitesimalIndicator : Surcomplex.{u} → Surcomplex.{u} :=
  Set.indicator {x | IsInfinitesimal x} (fun _ => 1)

@[simp] theorem infinitesimalIndicator_zero :
    infinitesimalIndicator (0 : Surcomplex.{u}) = 1 := by
  have hz : IsInfinitesimal (0 : Surcomplex.{u}) :=
    ⟨SignSequence.infinitesimal_zero, SignSequence.infinitesimal_zero⟩
  simp only [infinitesimalIndicator, Set.indicator_apply, Set.mem_setOf_eq, if_pos hz]

@[simp] theorem infinitesimalIndicator_one :
    infinitesimalIndicator (1 : Surcomplex.{u}) = 0 := by
  have h : ¬ IsInfinitesimal (1 : Surcomplex.{u}) := by
    intro h
    have hh := (SignSequence.standardPart_eq_zero_iff SignSequence.finite_one).mpr h.1
    simp only [SignSequence.standardPart_one, one_ne_zero] at hh
  exact Set.indicator_of_notMem (s := {x : Surcomplex.{u} | IsInfinitesimal x}) h _

/-- The complex indicator is constant on each infinitesimal coset. -/
theorem infinitesimalIndicator_add (x ε : Surcomplex.{u}) (hε : IsInfinitesimal ε) :
    infinitesimalIndicator (x + ε) = infinitesimalIndicator x := by
  have hr : SignSequence.IsInfinitesimal (x.re + ε.re) ↔ SignSequence.IsInfinitesimal x.re := by
    constructor
    · intro h
      simpa only [add_neg_cancel_right] using
        SignSequence.infinitesimal_add h (SignSequence.infinitesimal_neg hε.1)
    · exact fun h => SignSequence.infinitesimal_add h hε.1
  have hi : SignSequence.IsInfinitesimal (x.im + ε.im) ↔ SignSequence.IsInfinitesimal x.im := by
    constructor
    · intro h
      simpa only [add_neg_cancel_right] using
        SignSequence.infinitesimal_add h (SignSequence.infinitesimal_neg hε.2)
    · exact fun h => SignSequence.infinitesimal_add h hε.2
  simp only [infinitesimalIndicator, Set.indicator_apply, Set.mem_setOf_eq,
    IsInfinitesimal, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, hr, hi]

theorem fineHasDerivAt_infinitesimalIndicator (a : Surcomplex.{u}) :
    FineHasDerivAt infinitesimalIndicator 0 a :=
  fineHasDerivAt_indicator_of_isClopen isClopen_setOf_isInfinitesimal a

theorem infinitesimalIndicator_not_constant :
    ¬ ∃ c : Surcomplex.{u}, ∀ x, infinitesimalIndicator x = c := by
  rintro ⟨c, hc⟩
  have h := (hc 0).trans (hc 1).symm
  simp only [infinitesimalIndicator_zero, infinitesimalIndicator_one, one_ne_zero] at h

end
end Surreal.Surcomplex

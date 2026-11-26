import IPRADerivations.Analysis.Euler.PositiveAxis.UnitKernel.GaussianEulerUnitKernelNestedPanels
import IPRADerivations.Analysis.Euler.PositiveAxis.UnitKernel.GaussianEulerUnitKernelCompactDominance
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedThreeSumObservations
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalThreeSumLower

/-!
# Actual observations of nested unit-kernel panels

The original containing quadrature compares to the three original
quadrature observations at an independent query. For the projected-real
parameter this also gives a one-sided bound on the contained quadrature,
using the checked nonnegativity estimate for each omitted strip.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitKernelNestedObservations

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerUnitKernelCompactName (nameF data name_regular)
open GaussianEulerUnitKernelNestedPanels (source leftData rightData tail_sources original_split)
open GaussianEulerUnitKernelCompactDominance (projected_source original_companion_nonnegative)
open GaussianEulerVerticalNativeProjection (argument)
open GaussianNamedThreeSumObservations (raw numerator denominator)
open GaussianRationalMetric (distanceBounded)
open GaussianCoefficientNameBounds (unit)
open RationalValueBounds (upper)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem projected_nested_source (z R B a C E G b D H J : PTm n)
    (h : Γ ⊢[PRAAx] source z R B a C E G b D H J) : Γ ⊢[PRAAx] source (argument z) R B a C E G b D H J :=
  .andI (projected_source _ _ _ _ _ _ _ h.andE₁)
    (.andI (projected_source _ _ _ _ _ _ _ h.andE₂.andE₁) h.andE₂.andE₂)

theorem original_observations (p q z R B a C E G b D H J : PTm n)
    (h : Γ ⊢[PRAAx] source z R B a C E G b D H J) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (data z R B a C E G))
      (raw nameF nameF nameF q (leftData z R B a E b H) (data z R B b D H J) (rightData z R B a C E b D H))
      (numerator p q) (denominator p q) := by
  have strips := tail_sources z R B a C E G b D H J h
  exact GaussianNamedThreeSumObservations.original_observations nameF nameF nameF nameF p q
    (data z R B a C E G) (leftData z R B a E b H) (data z R B b D H J) (rightData z R B a C E b D H)
    (name_regular _ _ _ _ _ _ _ strips.andE₁) (name_regular _ _ _ _ _ _ _ h.andE₂.andE₁)
    (name_regular _ _ _ _ _ _ _ strips.andE₂) (original_split z R B a C E G b D H J h)

theorem real_middle_upper (p q z R B a C E G b D H J : PTm n)
    (h : Γ ⊢[PRAAx] source z R B a C E G b D H J) : Γ ⊢[PRAAx]
    upper (fstT (ap2 nameF q (data (argument z) R B b D H J)))
      (fstT (ap2 nameF p (data (argument z) R B a C E G))) (unit q+num 5*unit p) (unit p*unit q) := by
  have strips := tail_sources z R B a C E G b D H J h
  exact GaussianRationalThreeSumLower.original_dyadic_middle_upper p q
    (ap2 nameF p (data (argument z) R B a C E G))
    (ap2 nameF q (leftData (argument z) R B a E b H))
    (ap2 nameF q (data (argument z) R B b D H J)) (ap2 nameF q (rightData (argument z) R B a C E b D H))
    (original_observations p q (argument z) R B a C E G b D H J (projected_nested_source z R B a C E G b D H J h))
    (original_companion_nonnegative q _ _ _ _ _ _ _ strips.andE₁)
    (original_companion_nonnegative q _ _ _ _ _ _ _ strips.andE₂)

theorem actual_nested_projected_unit_quadrature_upper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 13
    (source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) ⟶
      upper (fstT (ap2 nameF (var 1) (data (argument (var 2)) (var 3) (var 4) (var 9) (var 10) (var 11) (var 12))))
        (fstT (ap2 nameF (var 0) (data (argument (var 2)) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8))))
        (unit (var 1)+num 5*unit (var 0)) (unit (var 0)*unit (var 1))) :=
  closeUniv 13 (.impI (real_middle_upper _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitKernelNestedObservations

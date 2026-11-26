import IPRADerivations.Analysis.Gamma.NegativeAxis.CriticalPoints.GaussianGammaNegativeIntervalNamedMinimum
import IPRADerivations.Analysis.Gamma.NegativeAxis.Values.GaussianGammaNegativeIntervalNamedApartness

/-!
# Strict log magnitude minimum on negative Gamma intervals

A finite apartness certificate gives a fixed positive rational
separation at all late freezes. The squared margin therefore remains
strict in the actual named logarithm comparison.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedStrictMinimum

open_ipra
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaNegativeCriticalEndpoints (mesh)
open GaussianGammaNegativeCriticalLocation (fractionLocationF)
open GaussianGammaNegativeIntervalCriticalDerivativeZero (locationClock)
open GaussianGammaNegativeIntervalNamedApartness (apart frozen_margin_floor marginDenominator margin_denominator_positive)
open GaussianGammaNegativeIntervalNamedInput (root_source)
open GaussianGammaNegativeIntervalNamedLog (nameF data name_regular)
open GaussianGammaNegativeIntervalNamedMinimum
  (index index_bounds location_clock_later marginAt marginAvailable order_with_margin)
open GaussianNameEquivalence (cross_refl)
open GaussianNamedEulerUnitTime (source)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qzero)
open GaussianStirlingMultiplicativeBoundsCaps (strict_fractions)
open GaussianStirlingMultiplicativeBoundsLog (constant_order fractions_order)
open GaussianStirlingMultiplicativeBoundsStrictOrder (strictOrder strict_transport)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem positive_margin_at (f : PR 2) (p x E N h : PTm n)
    (hs : Γ ⊢[PRAAx] source f x E) (ha : Γ ⊢[PRAAx] apart f h N x) :
    Γ ⊢[PRAAx] marginAt f p x E N (h+num 6) (fraction one (marginDenominator h)) := by
  let k := index p E N (h+num 6)
  let s := locationClock k N
  have late := le_trans (index_bounds (Γ := Γ) p E N (h+num 6)).andE₂.andE₁ (location_clock_later k N)
  exact frozen_margin_floor f h s N x E hs ha late

theorem positive_margin_available (f : PR 2) (x E N h : PTm n)
    (hs : Γ ⊢[PRAAx] source f x E) (ha : Γ ⊢[PRAAx] apart f h N x) :
    Γ ⊢[PRAAx] marginAvailable f x E N (h+num 6) (fraction one (marginDenominator h)) := by
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let sh (z : PTm n) := Syn.shift z
  have hs' : Δ ⊢[PRAAx] source f (sh x) (sh E) := by
    simpa only [Δ,sh,Fm.shift,Syn.shift,GaussianNamedEulerUnitTime.subst_source] using hs.shift
  have ha' : Δ ⊢[PRAAx] apart f (sh h) (sh N) (sh x) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using ha.shift
  simpa only [marginAvailable,Syn.shift,sh,PTm.subst_add,PTm.subst_num,
    GaussianPositiveRationalLogarithm.subst_fraction,GaussianGammaNegativeIntervalNamedApartness.subst_marginDenominator,
    one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    positive_margin_at f (var 0) (sh x) (sh E) (sh N) (sh h) hs' ha'

private theorem margin_positive (h : PTm n) : Γ ⊢[PRAAx] strictOrder constantF constantF qzero (fraction one (marginDenominator h)) := by
  let D := marginDenominator h
  let q := fraction one D
  have hD := margin_denominator_positive (Γ := Γ) h
  have lt0 : Γ ⊢[PRAAx] lt (D*zero) (one*one) := by unfold lt; ipra_le 0
  have hp : Γ ⊢[PRAAx] strictOrder constantF constantF (fraction zero one) q :=
    .andI (constant_order _ _ (fractions_order zero one one D (le_refl _) hD (le_of_lt lt0)))
      (strict_fractions zero one one D (le_refl _) hD lt0)
  exact strict_transport _ _ _ _ _ _ _ _
    (GaussianSignedNameExponentialOrder.constant_equal_cross _ _
      (GaussianGammaRationalWendelBoundary.fraction_zero _ (le_refl one)).eqSymm)
    (cross_refl _ _ (constant_regular q)) hp

theorem strict_log_minimum (f : PR 2) (x E N h : PTm n)
    (hs : Γ ⊢[PRAAx] source f x E) (ha : Γ ⊢[PRAAx] apart f h N x) :
    Γ ⊢[PRAAx] strictOrder (nameF fractionLocationF) (nameF f) (data N (mesh N) N) (data x E N) :=
  GaussianGammaNegativeIntervalNamedComparisonTransfer.strict_from_margin _ _ _ _ _
    (name_regular fractionLocationF N (mesh N) N (root_source N)) (margin_positive h)
    (order_with_margin f x E N (h+num 6) _ hs (positive_margin_available f x E N h hs ha))

theorem actual_named_negative_Gamma_log_strict_minimum_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      ((source f (var 0) (var 1) ⋏ apart f (var 3) (var 2) (var 0)) ⟶
        strictOrder (nameF fractionLocationF) (nameF f)
          (data (var 2) (mesh (var 2)) (var 2)) (data (var 0) (var 1) (var 2))) :=
  closeUniv 4 (.impI (strict_log_minimum f _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedStrictMinimum

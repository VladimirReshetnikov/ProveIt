import IPRADerivations.Analysis.Gamma.Digamma.Bernoulli.GaussianDigammaBernoulliActualBase
import IPRADerivations.Analysis.Gamma.Digamma.Bernoulli.GaussianDigammaBernoulliUpper

/-!
# The actual digamma improper kernel has a strict upper bound

The original base supplies two consecutive certified positive names.
Their exact recurrence identifies the gap between the current name
and the weighted Bernoulli primitive as the next name.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianDigammaBernoulliActualUpper

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ConciseIPRA.PTm (zero)
open GaussianDigammaBernoulliActualBase (original_named_positive)
open GaussianDigammaBernoulliName (nameF nameData name_regular)
open GaussianDigammaBernoulliRecurrence (weightedPrimitive)
open GaussianDigammaBernoulliUpper (named_recurrence_upper)
open GaussianDigammaFirstBernoulliImproper (baseF baseData base_regular)
open GaussianGammaCanonicalExponent (constantF)
open GaussianNameEquivalence (cross_refl)
open GaussianRationalHorner (qzero)
open GaussianSignedNameExponentialOrder (constant_equal_cross)
open GaussianStirlingMultiplicativeBoundsStrictOrder (strictOrder strict_transport)
open GaussianStirlingNames (source)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "fraction" => GaussianPositiveRationalLogarithm.fraction

theorem original_positive (m : ℕ) (A B : PTm n) (hs : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] strictOrder constantF (nameF baseF m) qzero (nameData m A B (baseData A B)) := by
  have e : Γ ⊢[PRAAx] (fraction zero one : PTm n) ≐ qzero :=
    GaussianGammaRationalWendelBoundary.fraction_zero one (le_refl one)
  exact strict_transport _ _ _ _ _ _ _ _ (constant_equal_cross _ _ e.eqSymm)
    (cross_refl _ _ (name_regular baseF m A B _ (base_regular A B hs)))
    (original_named_positive m A B hs)

theorem original_named_upper (m : ℕ) (A B : PTm n) (hs : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] strictOrder (nameF baseF m) constantF (nameData m A B (baseData A B)) (weightedPrimitive m A B) :=
  named_recurrence_upper baseF m A B (baseData A B) (base_regular A B hs) (original_positive (m+1) A B hs)

theorem original_named_bracket (m : ℕ) (A B : PTm n) (hs : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] strictOrder constantF (nameF baseF m) qzero (nameData m A B (baseData A B)) ⋏
      strictOrder (nameF baseF m) constantF (nameData m A B (baseData A B)) (weightedPrimitive m A B) :=
  .andI (original_positive m A B hs) (original_named_upper m A B hs)

theorem actual_digamma_Bernoulli_recurrence_bracket_closed (m : ℕ) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (source (var 0) (var 1) ⟶
        strictOrder constantF (nameF baseF m) qzero (nameData m (var 0) (var 1) (baseData (var 0) (var 1))) ⋏
        strictOrder (nameF baseF m) constantF (nameData m (var 0) (var 1) (baseData (var 0) (var 1)))
          (weightedPrimitive m (var 0) (var 1))) :=
  closeUniv 2 (.impI (original_named_bracket m _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianDigammaBernoulliActualUpper

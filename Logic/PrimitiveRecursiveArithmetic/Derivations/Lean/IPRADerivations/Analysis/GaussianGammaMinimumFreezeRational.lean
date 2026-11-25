import IPRADerivations.Analysis.GaussianGammaMinimumFreeze
import IPRADerivations.Analysis.GaussianGammaPositiveRationalProperness

/-!
# Freeze the original named log Gamma at its actual rational input

The comparison uses a late observation of the original input. Its
canonical positive fraction gives the usual native log Gamma datum.
The native rational remains in the explicit compact interval certified
by the named input and its observation radius.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaMinimumFreezeRational

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit)
open GaussianGammaMinimumFreeze (nameF data frozen_log_rate_at_rational)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNamedGammaPositiveLower (source)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedRightHalfPlane (radius threshold)
open GaussianRationalHorner (ofGaussian)
open GaussianStirlingGammaLogarithm (gammaData logGammaF logGammaData gammaLogMargin)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "N" => GaussianGammaReciprocalInverse.gammaF
local notation "encoded" => GaussianNamedGammaLateInput.encodedData
local notation "input" => GaussianNamedGammaLateInput.input
local notation "decodedNum" => GaussianNamedRightHalfPlane.numerator
local notation "decodedDen" => GaussianNamedRightHalfPlane.denominator
local notation "modulus" => GaussianGammaHalfPlaneInputContinuity.modulus

def numerator (f : PR 2) (r x : PTm n) : PTm n :=
  GaussianUnitIntervalInputDecoding.numerator (ap2 f r x)

def denominator (f : PR 2) (r x : PTm n) : PTm n :=
  GaussianUnitIntervalInputDecoding.denominator (ap2 f r x)

@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (r x : PTm n) :
    Syn.subst σ (numerator f r x) = numerator f (Syn.subst σ r) (Syn.subst σ x) := by
  simp [numerator]

@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (r x : PTm n) :
    Syn.subst σ (denominator f r x) = denominator f (Syn.subst σ r) (Syn.subst σ x) := by
  simp [denominator]

theorem frozen_rational_domain (f : PR 2) (r x A : PTm n) (hs : Γ ⊢[PRAAx] source f x A)
    (hl : Γ ⊢[PRAAx] le (threshold A) r) :
    Γ ⊢[PRAAx] GaussianCompactLogarithmBounds.domain (numerator f r x) (denominator f r x) (two*A) (radius f x) :=
  GaussianPositiveCompactInputDecoding.decoded_source _ _ _
    (GaussianNamedPositiveLateLogSource.late_sample_admissible f x A r hs.andE₁ hs.andE₂ hl).andE₂

theorem fraction_at (f : PR 2) (r x A : PTm n) (hs : Γ ⊢[PRAAx] source f x A)
    (hl : Γ ⊢[PRAAx] le (threshold A) r) :
    Γ ⊢[PRAAx] ap2 f r x ≐ GaussianPositiveRationalLogarithm.fraction (numerator f r x) (denominator f r x) := by
  have h := GaussianNamedPositiveLateLogSource.late_sample_admissible f x A r hs.andE₁ hs.andE₂ hl
  exact (GaussianPositiveCompactInputDecoding.fraction_exact _ _ _ h.andE₂ h.andE₁).eqSymm

theorem frozen_gamma_cross (f : PR 2) (s r x A : PTm n) (hs : Γ ⊢[PRAAx] source f x A)
    (hi : Γ ⊢[PRAAx] input f s r x A) :
    Γ ⊢[PRAAx] crossEquivalent N N (encoded f r x A)
      (gammaData (numerator f r x) (denominator f r x)) := by
  let q := ap2 f r x
  have h := GaussianNamedPositiveLateLogSource.late_sample_admissible f x A r hs.andE₁ hs.andE₂ hi.andE₂.andE₁
  have fixed : Γ ⊢[PRAAx] ofGaussian (decodedNum f r x) (decodedDen f r x) ≐ q :=
    GaussianExponentialReference.recode_fixed q h.andE₁
  exact GaussianGammaPositiveRationalProperness.original_cross _ _ _ _ _ _
    (GaussianNamedGammaLateInput.encoded_source f s r x A hi)
    (frozen_rational_domain f r x A hs hi.andE₂.andE₁).andE₁
    (fixed.eqTrans (fraction_at f r x A hs hi.andE₂.andE₁))

theorem frozen_log_rate (f : PR 2) (s r x A : PTm n) (hs : Γ ⊢[PRAAx] source f x A)
    (hl : Γ ⊢[PRAAx] le (threshold A) r) (hd : Γ ⊢[PRAAx] le (succ (modulus s (radius f x) (two*A))) r) :
    Γ ⊢[PRAAx] independentRate (nameF f) logGammaF (data x A)
      (logGammaData (numerator f r x) (denominator f r x)) gammaLogMargin (unit s) := by
  have hi : Γ ⊢[PRAAx] input f s r x A := .andI hs.andE₁ (.andI hl hd)
  exact frozen_log_rate_at_rational f s r x A _ _ hs hi
    (frozen_rational_domain f r x A hs hl).andE₁ (frozen_gamma_cross f s r x A hs hi)

theorem computed_frozen_log_rate (f : PR 2) (s x A : PTm n) (hs : Γ ⊢[PRAAx] source f x A) :
    Γ ⊢[PRAAx] independentRate (nameF f) logGammaF (data x A)
      (logGammaData (numerator f (GaussianNamedGammaPositiveLower.clock f s x A) x)
        (denominator f (GaussianNamedGammaPositiveLower.clock f s x A) x)) gammaLogMargin (unit s) :=
  frozen_log_rate f s _ x A hs (le_add_right _ _) (le_add_left _ _)

theorem actual_original_named_log_Gamma_frozen_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source f (var 1) (var 2) ⟶ independentRate (nameF f) logGammaF (data (var 1) (var 2))
        (logGammaData (numerator f (GaussianNamedGammaPositiveLower.clock f (var 0) (var 1) (var 2)) (var 1))
          (denominator f (GaussianNamedGammaPositiveLower.clock f (var 0) (var 1) (var 2)) (var 1)))
          gammaLogMargin (unit (var 0))) :=
  closeUniv 3 (.impI (computed_frozen_log_rate f _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaMinimumFreezeRational

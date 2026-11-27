import IPRADerivations.Analysis.Gamma.Names.PositiveAxis.GaussianNamedGammaPositiveLower
import IPRADerivations.Analysis.Logarithm.PositiveAxis.GaussianNamedPositiveLogarithmRate
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateTransport
import IPRADerivations.Analysis.Euler.CompactExhaustion.GaussianEulerCompactModulus
import IPRADerivations.Analysis.Stirling.GammaLogarithm.GaussianStirlingGammaLogarithm
import IPRADerivations.Analysis.Stirling.Bounds.Multiplicative.GaussianStirlingMultiplicativeBoundsOrder
import IPRADerivations.Analysis.Gamma.Digamma.Derivative.GaussianGammaDigammaStep

/-!
# The original named log Gamma and comparison to a frozen rational input

The projected actual Gamma is retimed by its certified one-eighteenth
lower bound. The logarithm then uses the same lower margin as the
original logarithm of Gamma on positive encoded rationals.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaMinimumFreeze

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEulerVerticalProjection (projected_source projected_real_samples)
open GaussianGammaCanonicalExponent (constant_at)
open GaussianGammaRealValues (axisF axis_regular axis_sample_at projection_distance)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm)
open GaussianNamedGammaPositiveLower (source original_gamma_positive_lower)
open GaussianNamedInverseRate (independentRate rate_at denominator_positive)
open GaussianNamedPositiveLateLogSource (retimedF retimedData)
open GaussianNamedRightHalfPlane (certificate marginPoint)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianStirlingGammaLogarithm (gammaMargin gammaLogMargin gammaRealF gammaRetimedF gammaRetimedData
  gammaData gamma_regular logGammaF logGammaData log_input)
open GaussianStirlingMultiplicativeBoundsOrder (fraction_real_part)
open RationalValueBounds (upper_congr upper_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "G" => GaussianNamedGamma.nameF
local notation "gd" => GaussianNamedGamma.data
local notation "N" => GaussianGammaReciprocalInverse.gammaF
local notation "RP" => GaussianStirlingGammaLogarithm.source

def realF (f : PR 2) : PR 2 := axisF (G f)
def retimeF (f : PR 2) : PR 2 := retimedF (realF f)
def retimeData (x A : PTm n) : PTm n := retimedData (gd x A) gammaMargin
def nameF (f : PR 2) : PR 2 := GaussianNamedPositiveLogarithm.nameF (retimeF f)
def data (x A : PTm n) : PTm n := GaussianNamedPositiveLogarithm.data (retimeData x A) gammaLogMargin

ipra_subst retimeData

ipra_subst data

private theorem margin_positive : Γ ⊢[PRAAx] le one (gammaMargin : PTm n) := by unfold gammaMargin; ipra_le 17

private theorem margin_at (p : PTm n) :
    Γ ⊢[PRAAx] fstT (ap2 GaussianGammaCanonicalExponent.constantF p (marginPoint gammaMargin)) ≐
      GaussianNamedGammaPositiveLower.lower := by
  have h : Γ ⊢[PRAAx] le one (gammaMargin : PTm n) := margin_positive
  have e := (GaussianGammaDigammaStep.unit_step_value gammaMargin h).eqSymm
  exact (congrFst (constant_at p (marginPoint gammaMargin))).eqTrans
    ((congrFst e).eqTrans (fraction_real_part one gammaMargin h))

theorem gamma_positive (f : PR 2) (x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) :
    Γ ⊢[PRAAx] GaussianNamedRightHalfPlane.source (G f) (gd x A) gammaMargin := by
  refine .andI (GaussianNamedGamma.name_regular f x A h.andE₁) (.andI margin_positive ?_)
  refine .allI (.allI ?_)
  let sh (v : PTm n) := Syn.shift (Syn.shift v)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let p : PTm (n+2) := var 1
  let q : PTm (n+2) := var 0
  have hs : Δ ⊢[PRAAx] source f (sh x) (sh A) := by
    simpa only [Fm.shift, Syn.shift, GaussianNamedGammaPositiveLower.subst_source, Δ, sh] using h.shift.shift
  have lower := original_gamma_positive_lower f q (sh x) (sh A) hs
  have widened := upper_mono _ _ _ _ (unit p+unit q) (unit p*unit q) (unit_positive q)
    lower (by ipra_le (Groth.ι (Q.mk Δ (unit q)))^2)
  have result := upper_congr (margin_at p).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) widened
  simpa only [certificate, GaussianNamedPositiveExponentialOrder.realOrder,
    GaussianNamedRightHalfPlane.subst_marginPoint, GaussianStirlingGammaLogarithm.subst_gammaMargin,
    GaussianNamedGamma.subst_data, Syn.shift, p, q, sh] using result

theorem log_input (f : PR 2) (x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) :
    Γ ⊢[PRAAx] GaussianNamedPositiveLogarithm.source (retimeF f) (retimeData x A) gammaLogMargin
      (GaussianNameBounds.U (realF f) (gd x A)) :=
  GaussianNamedPositiveLateLogSource.positive_source (realF f) (gd x A) gammaMargin
    (projected_source (G f) (gd x A) gammaMargin (gamma_positive f x A h))
    (projected_real_samples (G f) (gd x A))

theorem name_regular (f : PR 2) (x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) :
    Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN (nameF f) (data x A) :=
  GaussianNamedPositiveLogarithm.name_regular _ _ _ _ (log_input f x A h)

private theorem project_rate (f g : PR 2) (x y C D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] independentRate f g x y C D) :
    Γ ⊢[PRAAx] independentRate (axisF f) (axisF g) x y C D := by
  refine .allI (.allI ?_)
  let sh (v : PTm n) := Syn.shift (Syn.shift v)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let p : PTm (n+2) := var 1
  let q : PTm (n+2) := var 0
  have dh : Δ ⊢[PRAAx] le one (sh D) := by
    simpa [Δ, sh, Fm.shift, Syn.shift, one] using hD.shift.shift
  have rh : Δ ⊢[PRAAx] independentRate f g (sh x) (sh y) (sh C) (sh D) := by
    simpa only [Δ, sh, Fm.shift, Syn.shift, GaussianNamedInverseRate.subst_independentRate] using h.shift.shift
  have raw := rate_at f g (sh x) (sh y) (sh C) (sh D) p q rh
  exact distance_congr (axis_sample_at f p (sh x)).eqSymm (axis_sample_at g q (sh y)).eqSymm
    (.eqRefl _) (.eqRefl _) (projection_distance _ _ _ _ (denominator_positive _ _ _ dh) raw)

theorem frozen_log_rate_at_rational (f : PR 2) (s r x A a b : PTm n)
    (hs : Γ ⊢[PRAAx] source f x A) (hf : Γ ⊢[PRAAx] GaussianNamedGammaLateInput.input f s r x A)
    (hr : Γ ⊢[PRAAx] RP a b)
    (he : Γ ⊢[PRAAx] crossEquivalent N N (GaussianNamedGammaLateInput.encodedData f r x A) (gammaData a b)) :
    Γ ⊢[PRAAx] independentRate (nameF f) logGammaF (data x A) (logGammaData a b) gammaLogMargin (unit s) := by
  let u := gd x A
  let v := gammaData a b
  have hu := GaussianNamedGamma.name_regular f x A hs.andE₁
  have hv := gamma_regular a b hr
  have hS := unit_positive (Γ := Γ) s
  have g := GaussianNamedGammaLateInput.original_independent_rate f s r x A hf
  have fixed := GaussianNamedRateTransport.transport (G f) N (G f) N u
    (GaussianNamedGammaLateInput.encodedData f r x A) u v one (unit s) hS g
    (cross_refl _ _ hu) (cross_symm _ _ _ _ he)
  have projected := project_rate (G f) N u v one (unit s) hS fixed
  have l := GaussianNamedPositiveLateLogSource.original_cross (realF f) u gammaMargin (axis_regular _ _ hu)
  have r := GaussianNamedPositiveLateLogSource.original_cross gammaRealF v gammaMargin (axis_regular _ _ hv)
  have retimed := GaussianNamedRateTransport.transport (realF f) gammaRealF (retimeF f) gammaRetimedF
    u v (retimeData x A) (gammaRetimedData a b) one (unit s) hS projected
    (cross_symm _ _ _ _ l) (cross_symm _ _ _ _ r)
  have logged := GaussianNamedPositiveLogarithmRate.log_rate _ _ _ _ _ _ _ one (unit s)
    (log_input f x A hs) (GaussianStirlingGammaLogarithm.log_input a b hr) hS retimed
  exact GaussianEulerCompactModulus.rate_congr _ _ _ _ _ _ _ (by ipra_ring) logged

end LeanProofs.IPRA.Analysis.GaussianGammaMinimumFreeze

import IPRADerivations.Analysis.Gamma.Names.Derivatives.GaussianNamedGammaSmallIncrementInput
import IPRADerivations.Analysis.Names.Rates.Reciprocals.GaussianNamedInverseRate

/-!
# Freeze one actual observation of a named complex increment

The original addition program f+K is compared to the original addition
of f with the constant canonical fraction decoded from K(k). The query k
is arbitrary. Only original regularity is assumed; no smallness, positive
margin, apartness, or denominator-dependent error constant is needed.
Exact normalized fraction identities handle arbitrary raw K observations.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedGammaIncrementApproximation

open_ipra
open GaussianNamedGammaSmallIncrementInput (sumData)
open GaussianNamedGammaIncrementInput (incrementF incrementData clock)
open GaussianNamedRightHalfPlane (numerator denominator)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianRationalHorner (qadd positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalL1 (raw_den_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def frozenData (K : PR 2) (k x y : PTm n) : PTm n := incrementData x (numerator K k y) (denominator K k y)
def source (f K : PR 2) (x y : PTm n) : Fm PTm n := pointCN f x ⋏ pointCN K y

ipra_subst frozenData
ipra_subst source

theorem frozen_sample_at (f K : PR 2) (q k x y : PTm n) : Γ ⊢[PRAAx]
    qadd (ap2 f (clock q) x) (ap2 K k y) ≐ ap2 (incrementF f) q (frozenData K k x y) :=
  (GaussianNamedGammaSmallIncrementInput.sum_fraction _ _).eqTrans
    (GaussianNamedGammaIncrementInput.sample_fraction f q x _ _ (raw_den_positive _)).eqSymm

theorem frozen_regular (f K : PR 2) (k x y : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx]
    pointCN (incrementF f) (frozenData K k x y) := GaussianNamedGammaIncrementInput.regular f x _ _ hf

/-- The requested sum and constant-increment observations stay independent;
the frozen increment contributes exactly its one original dyadic. -/
theorem original_observations (f K : PR 2) (p q k x y : PTm n) (hs : Γ ⊢[PRAAx] source f K x y) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (GaussianNamedGammaSmallIncrementInput.sumF f K) p (sumData x y)) (ap2 (incrementF f) q (frozenData K k x y))
      (rateNumerator one (unit k) p q) (rateDenominator (unit k) p q) := by
  let P := unit p
  let S := unit k
  have exactFrozen := distance_congr (.eqRefl _) (frozen_sample_at f K q k x y) (.eqRefl _) (.eqRefl _)
    (GaussianNamedGammaSmallIncrementInput.independent_observations f K p (clock q) k x y hs.andE₁ hs.andE₂)
  have oldDen : Γ ⊢[PRAAx] le one (GaussianNamedGammaSmallIncrementInput.observationDenominator p (clock q) k) :=
    positive_product _ _ (positive_product _ _ (unit_positive _) (unit_positive _)) (unit_positive _)
  have grow := GaussianExponentialReference.unit_monotone (GaussianNamedGammaIncrementInput.clock_later (Γ := Γ) q)
  exact distance_radius_mono _ _ _ _ _ _ oldDen (GaussianNamedInverseRate.denominator_positive _ p q (unit_positive k))
    (by dsimp only [GaussianNamedGammaSmallIncrementInput.observationNumerator,GaussianNamedGammaSmallIncrementInput.observationDenominator,
          rateNumerator,rateDenominator]
        ipra_le (𝔞 P*𝔞 S)^2*sl grow) exactFrozen

theorem original_rate (f K : PR 2) (k x y : PTm n) (hs : Γ ⊢[PRAAx] source f K x y) : Γ ⊢[PRAAx]
    independentRate (GaussianNamedGammaSmallIncrementInput.sumF f K) (incrementF f) (sumData x y) (frozenData K k x y) one (unit k) := by
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  have hh : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source f K (sh x) (sh y) :=
    by simpa [Fm.shift,Syn.shift,sh] using hs.shift.shift
  refine .allI (.allI ?_)
  simpa only [independentRate,GaussianNamedGammaSmallIncrementInput.subst_sumData,subst_frozenData,GaussianCoefficientNameBounds.subst_unit,
    one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift,sh] using
    original_observations f K (var 1) (var 0) (sh k) (sh x) (sh y) hh

theorem actual_original_named_increment_frozen_rate_closed (f K : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source f K (var 1) (var 2) ⟶
      independentRate (GaussianNamedGammaSmallIncrementInput.sumF f K) (incrementF f) (sumData (var 1) (var 2)) (frozenData K (var 0) (var 1) (var 2)) one (unit (var 0))) :=
  closeUniv 3 (.impI (original_rate f K _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedGammaIncrementApproximation

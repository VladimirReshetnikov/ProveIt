import IPRADerivations.Analysis.Names.Apartness.GaussianNamedPositiveReciprocal

/-!
# The positive reciprocal at a literal frozen parameter observation

The frozen value reads the same numerator and denominator as the
rational specialization of the original parameter. The comparison
with the genuine reciprocal name keeps the full E²/2^k rate.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedPositiveReciprocalFrozen

open_ipra
open GaussianNamedPositiveReciprocal (clock reciprocal_at_distance nameF data name_at)
open GaussianNamedPositiveLogarithm (source numerator denominator)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalHorner (positive_product)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def frozen (f : PR 2) (k x : PTm n) : PTm n := fraction (denominator f k x) (numerator f k x)

ipra_subst frozen [numerator, denominator]

theorem original_observations (f : PR 2) (p q k x E T : PTm n)
    (hs : Γ ⊢[PRAAx] source f x E T) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (nameF f) p (data x E)) (ap2 constantF q (frozen f k x))
      (rateNumerator (E*E) (unit k) p q) (rateDenominator (unit k) p q) := by
  let s := clock p E
  let j := frozen f k x
  let U := unit s
  let V := unit k
  let P := unit p
  let Q' := unit q
  have hD : Γ ⊢[PRAAx] le one (U*V) := positive_product _ _ (unit_positive _) (unit_positive _)
  have pay : Γ ⊢[PRAAx] le (E*E*P) U := GaussianFastValueCut.query_budget (E*E) p
  have budget : Γ ⊢[PRAAx] le ((E*E*(U+V))*(V*P*Q'))
      ((E*E*P*Q'+V*(P+Q'))*(U*V)) := by
    ipra_le 𝔞(V*V*Q')*sl pay+𝔞(V*P*U*V)
  exact distance_radius_mono _ _ _ _ _ _ hD
    (positive_product _ _ (positive_product _ _ (unit_positive _) (unit_positive _)) (unit_positive _)) budget
    (distance_congr (name_at f p x E).eqSymm (constant_at q j).eqSymm (.eqRefl _) (.eqRefl _)
      (reciprocal_at_distance f s k x E T hs))

theorem original_rate (f : PR 2) (k x E T : PTm n) (hs : Γ ⊢[PRAAx] source f x E T) :
    Γ ⊢[PRAAx] independentRate (nameF f) constantF (data x E) (frozen f k x) (E*E) (unit k) := by
  let sh (v : PTm n) := Syn.shift (Syn.shift v)
  have h : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source f (sh x) (sh E) (sh T) := by
    simpa only [Fm.shift,Syn.shift,GaussianNamedPositiveLogarithm.subst_source,sh] using hs.shift.shift
  refine .allI (.allI ?_)
  simpa only [independentRate,GaussianNamedPositiveReciprocal.subst_data,subst_frozen,subst_ap2,
    GaussianCoefficientNameBounds.subst_unit,LeanProofs.IPRA.PTm.subst_mul,Syn.shift,sh] using
    original_observations f (var 1) (var 0) (sh k) (sh x) (sh E) (sh T) h

theorem actual_named_positive_reciprocal_frozen_rate_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (source f (var 1) (var 2) (var 3) ⟶
        independentRate (nameF f) constantF (data (var 1) (var 2)) (frozen f (var 0) (var 1))
          (var 2*var 2) (unit (var 0))) :=
  closeUniv 4 (.impI (original_rate f _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedPositiveReciprocalFrozen

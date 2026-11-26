import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.GaussianNamedDifferenceQuotient
import IPRADerivations.Analysis.Names.Rates.Reciprocals.GaussianNamedInverseRate

/-!
# Freeze an actual named reciprocal at a late decoded observation

The inverse gain is R(a)^2, fixed by the finite original apartness
certificate. It does not depend on the decoded native denominator.
Actual reciprocal variation and one finite rational gap retain precisely
the requested reciprocal observation error and the frozen input error.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedReciprocalFrozenRate

open_ipra
open GaussianNameReciprocal (anchor R modulus tail lower input nameF nameData name_fast tail_lower R_positive)
open GaussianRationalReciprocal (reciprocal)
open GaussianRationalHorner (ofGaussian positive_product)
open GaussianRationalMetric (qsub bounded distanceBounded)
open GaussianRationalL1 (rawGaussian rawDen raw_den_positive raw_represents)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same distance_symmetric)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianBoundedConstantProductName (constantF constant_at)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def rawFrozen (K : PR 2) (z k : PTm n) : PTm n := reciprocal (ap2 K k z)
def frozen (K : PR 2) (z k : PTm n) : PTm n := reciprocal (ofGaussian (rawGaussian (ap2 K k z)) (rawDen (ap2 K k z)))
def numerator (a p k : PTm n) : PTm n := unit k+modulus a*unit p
def denominator (p k : PTm n) : PTm n := unit p*unit k
def source (K : PR 2) (a z k : PTm n) : Fm PTm n := input K a z ⋏ le (anchor a) k

ipra_subst rawFrozen
ipra_subst frozen
ipra_subst numerator
ipra_subst denominator
ipra_subst source

theorem late_lower (K : PR 2) (a z k : PTm n) (h : Γ ⊢[PRAAx] input K a z) (hk : Γ ⊢[PRAAx] le (anchor a) k) : Γ ⊢[PRAAx]
    lower (ap2 K k z) (R a) := by
  have time : Γ ⊢[PRAAx] LeanProofs.IPRA.PTm.monus k (anchor a)+anchor a ≐ k :=
    (add_comm _ _).eqTrans (eq_add_of_le hk).eqSymm
  exact GaussianNameReciprocal.lower_congr (congrAp2 K time (.eqRefl z)) (.eqRefl _)
    (tail_lower K a z (LeanProofs.IPRA.PTm.monus k (anchor a)) h.andE₁ h.andE₂)

theorem lower_recode (q S : PTm n) (hS : Γ ⊢[PRAAx] le one S) (hq : Γ ⊢[PRAAx] lower q S) : Γ ⊢[PRAAx]
    lower (GaussianFastValueCut.recode q) S :=
  GaussianRationalLowerBounds.lower_from_representation _ (rawGaussian q) (rawDen q) one S (raw_den_positive q) hS
    (GaussianRationalHorner.ofGaussian_represents _ _ (raw_den_positive q))
    (GaussianRationalLowerBounds.lower_to_cleared q (rawGaussian q) (rawDen q) one S (raw_den_positive q) hS (raw_represents q) hq)

theorem reciprocal_recode_zero (q S : PTm n) (hS : Γ ⊢[PRAAx] le one S) (hq : Γ ⊢[PRAAx] lower q S) : Γ ⊢[PRAAx]
    distanceBounded (reciprocal q) (reciprocal (GaussianFastValueCut.recode q)) zero one := by
  have point : Γ ⊢[PRAAx] distanceBounded q (GaussianFastValueCut.recode q) zero one :=
    distance_symmetric _ _ _ _ (le_refl one) (GaussianFastValueCut.recode_distance q)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (GaussianNameReciprocal.inverse_distance_two q (GaussianFastValueCut.recode q) S S zero one hS hS (le_refl one)
      hq (lower_recode q S hS hq) point)

theorem reciprocal_at (K : PR 2) (a z p : PTm n) : Γ ⊢[PRAAx]
    ap2 (nameF K) p (nameData a z) ≐ reciprocal (tail K a z (GaussianFastValueCut.exponent (modulus a) p)) :=
  (GaussianNameReciprocal.name_at K a z p).eqTrans
    (GaussianNamedSmallPerturbationTransport.recode_fixed _ (GaussianRationalReciprocal.reciprocal_canonical _))

theorem raw_slack (K : PR 2) (p a z k t : PTm n) (h : Γ ⊢[PRAAx] input K a z) (hk : Γ ⊢[PRAAx] le (anchor a) k) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (qsub (ap2 (nameF K) p (nameData a z)) (rawFrozen K z k))
      (numerator a p k) (denominator p k) (one+modulus a) t := by
  let e := GaussianFastValueCut.exponent (modulus a) t
  let r := e+anchor a
  let P := unit p
  let Q := unit k
  let T := unit t
  let W := unit r
  let Z := denominator p k*T
  have ht : Γ ⊢[PRAAx] le t r := le_trans (le_add_right t _) (le_add_right e _)
  have grow : Γ ⊢[PRAAx] le T W := GaussianBalancedRadiusArithmetic.unit_monotone t r ht
  have hz : Γ ⊢[PRAAx] le one Z := positive_product _ _ (positive_product _ _ (unit_positive p) (unit_positive k)) (unit_positive t)
  have cn := name_fast K a z h.andE₁ h.andE₂
  have first := distance_radius_mono _ _ _ _ ((P+T)*Q) Z
    (positive_product _ _ (unit_positive p) (unit_positive t)) hz
    (le_of_eq_add (d := zero) (by dsimp only [Z,denominator,P,Q,T]; ipra_ring)) (GaussianNameEquivalence.point_at (nameF K) (nameData a z) p t cn)
  have points := GaussianNameEquivalence.point_at K z r k h.andE₁
  have coarse := distance_radius_mono _ _ _ _ (T+Q) (T*Q)
    (positive_product _ _ (unit_positive r) (unit_positive k)) (positive_product _ _ (unit_positive t) (unit_positive k))
    (by dsimp only [T,Q,W]; ipra_le (𝔞(unit k))^2*sl grow) points
  have inverses := GaussianNameReciprocal.inverse_distance_two _ _ (R a) (R a) (T+Q) (T*Q)
    (R_positive a) (R_positive a) (positive_product _ _ (unit_positive t) (unit_positive k))
    (tail_lower K a z e h.andE₁ h.andE₂) (late_lower K a z k h hk) coarse
  have bound := distance_radius_mono _ _ _ _ (modulus a*(T+Q)*P) Z
    (positive_product _ _ (unit_positive t) (unit_positive k)) hz
    (le_of_eq_add (d := zero) (by dsimp only [modulus,Z,denominator,P,Q,T]; ipra_ring)) inverses
  have second := distance_congr (reciprocal_at K a z t).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) bound
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [numerator,denominator,P,Q,T,unit]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hz first second)

theorem raw_observations (K : PR 2) (p a z k : PTm n) (h : Γ ⊢[PRAAx] input K a z) (hk : Γ ⊢[PRAAx] le (anchor a) k) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (nameF K) p (nameData a z)) (rawFrozen K z k) (numerator a p k) (denominator p k) :=
  GaussianRationalSlackRemoval.slack_removal_at _ _ _ (one+modulus a) (positive_product _ _ (unit_positive p) (unit_positive k))
    (raw_slack K p a z k (GaussianRationalSlackRemoval.precision (qsub (ap2 (nameF K) p (nameData a z)) (rawFrozen K z k))
      (numerator a p k) (denominator p k) (one+modulus a)) h hk)

theorem frozen_observations (K : PR 2) (p a z k : PTm n) (h : Γ ⊢[PRAAx] input K a z) (hk : Γ ⊢[PRAAx] le (anchor a) k) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (nameF K) p (nameData a z)) (frozen K z k) (numerator a p k) (denominator p k) := by
  have last := reciprocal_recode_zero (ap2 K k z) (R a) (R_positive a) (late_lower K a z k h hk)
  have joined := GaussianReconstructionRoots.distance_triangle _ _ _ (numerator a p k) (denominator p k) zero one
    (positive_product _ _ (unit_positive p) (unit_positive k)) (le_refl one) (raw_observations K p a z k h hk) last
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (by ipra_ring) joined

theorem frozen_inverse_bound (K : PR 2) (a z k : PTm n) (h : Γ ⊢[PRAAx] input K a z) (hk : Γ ⊢[PRAAx] le (anchor a) k) : Γ ⊢[PRAAx]
    bounded (frozen K z k) (R a) one :=
  GaussianNameReciprocal.inverse_bound _ (R a) (R_positive a)
    (lower_recode (ap2 K k z) (R a) (R_positive a) (late_lower K a z k h hk))

theorem frozen_rate_at (K : PR 2) (p q a z k : PTm n) (h : Γ ⊢[PRAAx] input K a z) (hk : Γ ⊢[PRAAx] le (anchor a) k) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (nameF K) p (nameData a z)) (ap2 constantF q (frozen K z k))
      (rateNumerator (modulus a) (unit k) p q) (rateDenominator (unit k) p q) := by
  have larger := distance_radius_mono _ _ _ _ (rateNumerator (modulus a) (unit k) p q) (rateDenominator (unit k) p q)
    (positive_product _ _ (unit_positive p) (unit_positive k)) (GaussianNamedInverseRate.denominator_positive _ _ _ (unit_positive k))
    (le_of_eq_add (d := unit k*unit k*unit p*unit p) (by dsimp only [numerator,denominator,rateNumerator,rateDenominator]; ipra_ring))
    (frozen_observations K p a z k h hk)
  exact distance_congr (.eqRefl _) (constant_at q (frozen K z k)).eqSymm (.eqRefl _) (.eqRefl _) larger

theorem frozen_rate (K : PR 2) (a z k : PTm n) (h : Γ ⊢[PRAAx] input K a z) (hk : Γ ⊢[PRAAx] le (anchor a) k) : Γ ⊢[PRAAx]
    independentRate (nameF K) constantF (nameData a z) (frozen K z k) (modulus a) (unit k) := by
  refine .allI (.allI ?_)
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] input K (sh a) (sh z) :=
    by simpa only [Fm.shift,GaussianNameReciprocal.subst_input,Syn.shift,sh] using h.shift.shift
  have ks : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le (anchor (sh a)) (sh k) :=
    by simpa [Fm.shift,Syn.shift,sh] using hk.shift.shift
  simpa only [independentRate,Syn.shift,GaussianNameReciprocal.subst_nameData,GaussianNameReciprocal.subst_modulus,
    subst_frozen,GaussianCoefficientNameBounds.subst_unit,sh] using frozen_rate_at K (var 1) (var 0) (sh a) (sh z) (sh k) hs ks

theorem actual_named_reciprocal_late_decoded_rate_closed (K : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source K (var 1) (var 2) (var 3) ⟶
      distanceBounded (ap2 (nameF K) (var 0) (nameData (var 1) (var 2))) (frozen K (var 2) (var 3))
        (numerator (var 1) (var 0) (var 3)) (denominator (var 0) (var 3))) :=
  closeUniv 4 (.impI (frozen_observations K _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_named_reciprocal_frozen_constant_rate_closed (K : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source K (var 0) (var 1) (var 2) ⟶
      independentRate (nameF K) constantF (nameData (var 0) (var 1)) (frozen K (var 1) (var 2)) (modulus (var 0)) (unit (var 2))) :=
  closeUniv 3 (.impI (frozen_rate K _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianNamedReciprocalFrozenRate

import IPRADerivations.Analysis.Beta.GaussianBetaContiguousUpperTail

/-!
# Cofinal numerical budget for one fixed quarter-degree decay observation

Keep N and the original decay query q0 fixed. Independent lower bounds
on the shared mesh multiplier, row query and auxiliary decay query
absorb all remaining numerical errors. The leading coefficient remains
exactly one D_R, including its one fixed-query observation error.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaContiguousUpperTailBudget

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBetaContiguousUpperTail (source beta euler quarterSample sampleNumerator sampleDenominator count width)
open GaussianWeightedHalfDecayEndpoint (coefficient)
open GaussianGammaIntegralCutoffs (etaDen eta_den_positive)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalDistanceOrder (distance_radius_mono distance_congr)
open GaussianDominantPairAlgebra (radiusPoint radius_bounded)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def fixedNumerator (q0 R N : PTm n) : PTm n := coefficient R*(sampleNumerator q0 N*unit q0+sampleDenominator q0 N)
def fixedDenominator (q0 N : PTm n) : PTm n := sampleDenominator q0 N*unit q0
def meshCost (R T : PTm n) : PTm n := coefficient R*T
def precisionCost (R T : PTm n) : PTm n := (coefficient R+GaussianBetaEulerTailDifferencePointwise.referenceError R)*T
def queryCost (R : PTm n) : PTm n := num 9*coefficient R
def minimumMesh (j R T : PTm n) : PTm n := meshCost R T*unit (j+num 2)+one
def minimumPrecision (j R T : PTm n) : PTm n := GaussianFastValueCut.exponent (precisionCost R T) (j+num 2)
def minimumQuery (j R : PTm n) : PTm n := GaussianFastValueCut.exponent (queryCost R) (j+num 2)
def exactNumerator (p q q0 R N : PTm n) (_T : PTm n) (S E C : PTm n) : PTm n :=
  fixedNumerator q0 R N*(num 4*E*E*S*unit p*unit q)+fixedDenominator q0 N*
    (num 3*coefficient R*C*unit p*unit q+
      (two*coefficient R*C*E+num 4*C*GaussianBetaEulerTailDifferencePointwise.referenceError R*E)*S*unit q+
      num 36*coefficient R*E*E*S*unit p)
def exactDenominator (p q q0 N S E : PTm n) : PTm n := fixedDenominator q0 N*(num 4*E*E*S*unit p*unit q)
def coarseNumerator (p q q0 R N T S : PTm n) : PTm n :=
  fixedNumerator q0 R N*S*unit p*unit q+fixedDenominator q0 N*
    (meshCost R T*unit p*unit q+precisionCost R T*S*unit q+queryCost R*S*unit p)
def coarseDenominator (p q q0 N S : PTm n) : PTm n := fixedDenominator q0 N*S*unit p*unit q
def numerator (j q0 R N : PTm n) : PTm n := fixedNumerator q0 R N*unit j+fixedDenominator q0 N
def denominator (j q0 N : PTm n) : PTm n := fixedDenominator q0 N*unit j

theorem fixed_denominator_positive (q0 N : PTm n) : Γ ⊢[PRAAx] le one (fixedDenominator q0 N) :=
  positive_product _ _ (GaussianRationalL1.raw_den_positive _) (unit_positive q0)

theorem fixed_quarter_bound (q q0 R N : PTm n) : Γ ⊢[PRAAx]
    bounded (qmul (radiusPoint (coefficient R) one) (quarterSample q N))
      (fixedNumerator q0 R N*unit q+coefficient R*fixedDenominator q0 N) (fixedDenominator q0 N*unit q) := by
  have hd := positive_product (Γ := Γ) _ _ (unit_positive q) (unit_positive q0)
  have old := GaussianNameEquivalence.point_at (Γ := Γ) GaussianEulerIntegrandName.decayF (GaussianEulerIntegrandName.decayData N (num 4)) q q0
    (GaussianEulerDecayQuadraturePrecision.observation_regular N (num 4))
  have near := GaussianApproximateInverseDistance.multiply_distance (radiusPoint (coefficient R) one) _ _ (coefficient R)
    (unit q+unit q0) (unit q*unit q0) hd (radius_bounded _ one (le_refl one)) old
  have hy := GaussianRationalL1.raw_den_positive (Γ := Γ) (quarterSample q0 N)
  have first := GaussianRationalReciprocal.bounded_product (radiusPoint (coefficient R) one) _ _ one _ _ (le_refl one) hy
    (radius_bounded _ one (le_refl one)) (GaussianBetaContiguousUpperTail.actual_quarter_sample_bound q0 N)
  have norm := GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _ hd (positive_product _ _ (le_refl one) hy) near first
  exact bound_congr (.eqRefl _) (by unfold fixedNumerator fixedDenominator sampleDenominator; ipra_ring)
    (by unfold fixedDenominator sampleDenominator; ipra_ring) norm

theorem original_exact_envelope (p q q0 k A S z R B N T : PTm n) (h : Γ ⊢[PRAAx] source z R B A N T S) : Γ ⊢[PRAAx]
    distanceBounded (beta p k A S z R B N T) (euler p k A S z R B N T)
      (exactNumerator p q q0 R N T S (etaDen k A R) (width k A R N T))
      (exactDenominator p q q0 N S (etaDen k A R)) := by
  have he := eta_den_positive (Γ := Γ) k A R
  have hs := h.andE₂.andE₂.andE₂.andE₂
  have hf := fixed_denominator_positive (Γ := Γ) q0 N
  have geo := GaussianBetaContiguousUpperTail.geometry k A R N T h.andE₂.andE₁ h.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₁
  have hm := positive_product (Γ := Γ) _ _ geo.andE₁ hs
  have md := GaussianWeightedHalfDecayEndpoint.mesh_denominator_positive p q (count k A R N T S) (etaDen k A R) hm he
  have fy := positive_product (Γ := Γ) _ _ hf (unit_positive q)
  have old := GaussianBetaContiguousUpperTail.original_grid_from_quarter_decay_bound p q k A S z R B N T _ _ h fy (fixed_quarter_bound q q0 R N)
  have den : Γ ⊢[PRAAx] le one (exactDenominator p q q0 N S (etaDen k A R)) :=
    positive_product _ _ hf (positive_product _ _ (positive_product _ _ (positive_product _ _
      (positive_product _ _ (positive_product _ _ GaussianEulerSharpDegreeSchedule.four_positive he) he) hs) (unit_positive p)) (unit_positive q))
  apply distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (positive_product _ _ he (unit_positive p)) (positive_product _ _ md (positive_product _ _ fy (unit_positive q)))) den _ old
  exact le_of_eq_add (d := zero) (by
    dsimp only [GaussianBetaContiguousUpperTail.numerator,GaussianBetaContiguousUpperTail.denominator,
      GaussianWeightedHalfDecayEndpoint.numerator,GaussianWeightedHalfDecayEndpoint.denominator,
      GaussianWeightedHalfDecayEndpoint.meshNumerator,GaussianWeightedHalfDecayEndpoint.meshDenominator,
      GaussianEulerDecayQuadraturePrecision.numerator,GaussianEulerDecayQuadraturePrecision.denominator,
      GaussianNameRingLaws.three,exactNumerator,exactDenominator,count]
    ipra_ring)

theorem original_coarse_envelope (p q q0 k A S z R B N T : PTm n) (h : Γ ⊢[PRAAx] source z R B A N T S) : Γ ⊢[PRAAx]
    distanceBounded (beta p k A S z R B N T) (euler p k A S z R B N T)
      (coarseNumerator p q q0 R N T S) (coarseDenominator p q q0 N S) := by
  let E := etaDen k A R
  let C := width k A R N T
  let D := coefficient R
  let F := GaussianBetaEulerTailDifferencePointwise.referenceError R
  let Y := fixedDenominator q0 N
  let P := unit p
  let Q := unit q
  let O := 𝔞(Y)*𝔞(Y)*𝔞(S)*𝔞(P)*𝔞(Q)
  have he := eta_den_positive (Γ := Γ) k A R
  have hs := h.andE₂.andE₂.andE₂.andE₂
  have hf := fixed_denominator_positive (Γ := Γ) q0 N
  have geo := GaussianBetaContiguousUpperTail.geometry k A R N T h.andE₂.andE₁ h.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₁
  have widthBound : Γ ⊢[PRAAx] le C (E*T) := le_congr (.eqRefl _) geo.andE₂.andE₂.andE₂ (le_add_left C (GaussianBetaContiguousUpperTail.start k A R N))
  have hd : Γ ⊢[PRAAx] le one (exactDenominator p q q0 N S E) := positive_product _ _ hf
    (positive_product _ _ (positive_product _ _ (positive_product _ _ (positive_product _ _
      (positive_product _ _ GaussianEulerSharpDegreeSchedule.four_positive he) he) hs) (unit_positive p)) (unit_positive q))
  have hy : Γ ⊢[PRAAx] le one (coarseDenominator p q q0 N S) := positive_product _ _ (positive_product _ _ (positive_product _ _ hf hs) (unit_positive p)) (unit_positive q)
  apply distance_radius_mono _ _ _ _ _ _ hd hy _ (original_exact_envelope p q q0 k A S z R B N T h)
  dsimp only [exactNumerator,exactDenominator,coarseNumerator,coarseDenominator,meshCost,precisionCost,queryCost]
  ipra_le (O*(3*𝔞(D)*𝔞(P)*𝔞(Q)+𝔞(E)*𝔞(S)*𝔞(Q)*(2*𝔞(D)+4*𝔞(F))))*sl widthBound+
    (O*4*𝔞(D)*𝔞(P)*𝔞(Q)*𝔞(E)*𝔞(T))*sl he+
    O*(𝔞(D)*𝔞(P)*𝔞(Q)*𝔞(E)*𝔞(T)+2*𝔞(D)*𝔞(E)*𝔞(E)*𝔞(S)*𝔞(Q)*𝔞(T))

/-- Exactly one D_R times the fixed original q0 observation radius,
one D_R eps_q0, and the requested cofinal numerical slack eps_j. -/
theorem original_cofinal_bound (j p q q0 k A S z R B N T : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A N T S)
    (hm : Γ ⊢[PRAAx] le (minimumMesh j R T) S)
    (hp : Γ ⊢[PRAAx] le (minimumPrecision j R T) p)
    (hq : Γ ⊢[PRAAx] le (minimumQuery j R) q) : Γ ⊢[PRAAx]
    distanceBounded (beta p k A S z R B N T) (euler p k A S z R B N T)
      (numerator j q0 R N) (denominator j q0 N) := by
  let Y := fixedDenominator q0 N
  let W := unit (j+num 2)
  have hf := fixed_denominator_positive (Γ := Γ) q0 N
  have hs := h.andE₂.andE₂.andE₂.andE₂
  have mesh := le_trans (le_add_right (meshCost R T*W) one) hm
  have prec := le_trans (GaussianFastValueCut.query_budget (precisionCost R T) (j+num 2)) (GaussianExponentialReference.unit_monotone hp)
  have query := le_trans (GaussianFastValueCut.query_budget (queryCost R) (j+num 2)) (GaussianExponentialReference.unit_monotone hq)
  have hd : Γ ⊢[PRAAx] le one (coarseDenominator p q q0 N S) :=
    positive_product _ _ (positive_product _ _ (positive_product _ _ hf hs) (unit_positive p)) (unit_positive q)
  have hw := positive_product (Γ := Γ) _ _ hf (unit_positive (j+num 2))
  have middle := distance_radius_mono _ _ _ _ (fixedNumerator q0 R N*W+num 3*Y) (Y*W) hd hw ?_
    (original_coarse_envelope p q q0 k A S z R B N T h)
  · have four : Γ ⊢[PRAAx] W ≐ num 4*unit j := by
      change Γ ⊢[PRAAx] pw two (j+num 2) ≐ num 4*pw two j
      exact (pw_add two j (num 2)).eqTrans ((congrMul (.eqRefl _) ((pw_succ two one).eqTrans
        (congrMul (pw_one two) (.eqRefl two)))).eqTrans (by ipra_ring))
    apply distance_radius_mono _ _ _ _ _ _ hw (positive_product _ _ hf (unit_positive j)) _ middle
    exact le_of_eq_add (d := Y*Y*unit j) (by
      apply deriveNat
      have eq := natEq four
      dsimp only [numerator,denominator]
      ipra_simps
      rw [eq]
      ring)
  · dsimp only [coarseNumerator,coarseDenominator]
    ipra_le (𝔞(Y)*𝔞(Y)*𝔞(unit p)*𝔞(unit q))*sl mesh+
      (𝔞(Y)*𝔞(Y)*𝔞(S)*𝔞(unit q))*sl prec+(𝔞(Y)*𝔞(Y)*𝔞(S)*𝔞(unit p))*sl query

theorem original_contiguous_single_fixed_decay_observation_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 12
    ((source (var 7) (var 8) (var 9) (var 5) (var 10) (var 11) (var 6) ⋏
      (le (minimumMesh (var 0) (var 8) (var 11)) (var 6) ⋏
       (le (minimumPrecision (var 0) (var 8) (var 11)) (var 1) ⋏ le (minimumQuery (var 0) (var 8)) (var 2)))) ⟶
      distanceBounded (beta (var 1) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11))
        (euler (var 1) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11))
        (numerator (var 0) (var 3) (var 8) (var 10)) (denominator (var 0) (var 3) (var 10))) :=
  closeUniv 12 (.impI (original_cofinal_bound _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBetaContiguousUpperTailBudget

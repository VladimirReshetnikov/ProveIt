import IPRADerivations.Analysis.Euler.PositiveAxis.UpperBounds.GaussianEulerUpperTailLeftNorm
import IPRADerivations.Analysis.Euler.Integration.Decay.GaussianEulerDecayFactorBounds
import IPRADerivations.Analysis.Beta.EulerProducts.GaussianEulerBetaProductPascal

/-!
# Exact upper bound for the actual Euler panel from one to the top

The norm of the actual left half-decay observation is at most one
plus its requested error. The original Euler rows give the factorial
constant D_R, with explicitly adjustable mesh and sampling errors.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitToTopBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerUpperPowerCoefficients (source)
open GaussianEulerWeightedHalfDecay (majorant)
open GaussianEulerUpperTailScalar (budget)
open GaussianEulerIntegrandName (evaluatorF fixedData decayF decayData)
open GaussianCompactRiemannName (quadrature)
open GaussianGammaIntegralCutoffs (tailCoefficient)
open GaussianPositiveRationalExponentialDecay (expF inverseData)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

/-- Every actual positive-time decay observation has norm at most
one plus twice the requested tolerance. -/
theorem original_decay_unit_envelope (q a b : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    bounded (ap2 decayF q (decayData a b)) (unit q+two) (unit q) := by
  let y := ap2 (GaussianNameReciprocal.nameF expF) q (inverseData a b zero)
  have pow := GaussianRationalReciprocal.power_zero (Γ := Γ) (GaussianDominantPairAlgebra.radiusPoint a b)
  have exactBound := GaussianPositiveRationalExponentialDecay.exact_reciprocal_weighted_decay a b zero q ha hb
  have code := (GaussianRationalSyntheticDivision.qmul_congr pow (.eqRefl y)).eqTrans
    (GaussianEulerBetaProductPascal.one_left y (GaussianNameReciprocal.name_canonical _ _ _ _))
  have base := bound_congr code (fact_zero (zero : PTm n)) (.eqRefl _) exactBound
  have near := GaussianNameEquivalence.cross_at _ _ _ _ q q
    (GaussianNameEquivalence.cross_symm _ _ _ _
      (GaussianEulerDecayFactorBounds.original_decay_matches_reciprocal a b zero hb))
  have hq := unit_positive (Γ := Γ) q
  have raw := GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _ (positive_product _ _ hq hq)
    (le_refl one) near base
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ (positive_product _ _ hq hq) (le_refl one))
    hq (le_congr (by ipra_ring) (.eqRefl _) (le_refl _)) raw

def meshCost (R T : PTm n) : PTm n := two*majorant R*T
def rowCost (R T : PTm n) : PTm n := (budget R+majorant R)*T
def endpointCost (R : PTm n) : PTm n := num 16*majorant R+two*tailCoefficient R
def minimumMesh (t R T : PTm n) : PTm n := one+meshCost R T*unit (t+num 2)
def minimumPrecision (t R T : PTm n) : PTm n := GaussianFastValueCut.exponent (rowCost R T) (t+num 2)
def minimumReference (t R : PTm n) : PTm n := GaussianFastValueCut.exponent (endpointCost R) (t+num 2)

def coarseNumerator (p q K R T : PTm n) : PTm n :=
  tailCoefficient R*(K*unit p*unit q)+meshCost R T*(unit p*unit q)+
    rowCost R T*(K*unit q)+endpointCost R*(K*unit p)
def coarseDenominator (p q K : PTm n) : PTm n := K*unit p*unit q

theorem original_coarse_grid_bound (p q C E K T z R B : PTm n)
    (h : Γ ⊢[PRAAx] source z R B) (hE : Γ ⊢[PRAAx] le one E)
    (hC : Γ ⊢[PRAAx] le one C) (hK : Γ ⊢[PRAAx] le one K)
    (hW : Γ ⊢[PRAAx] le C (E*T)) : Γ ⊢[PRAAx]
    bounded (quadrature evaluatorF p (C*K) E C E (fixedData z B))
      (coarseNumerator p q K R T) (coarseDenominator p q K) := by
  let U := unit p
  let V := unit q
  let M := majorant R
  let H := budget R
  let D := tailCoefficient R
  have hU := unit_positive (Γ := Γ) p
  have hV := unit_positive (Γ := Γ) q
  have hm := positive_product C K hC hK
  have mul := positive_product _ _ (le_succ_self one) hE
  have step : Γ ⊢[PRAAx] le C ((two*E)*(C*K)) :=
    le_trans (le_congr (one_mul C) (mul_comm K C) (mul_le_mul_right C hK))
      (le_congr (one_mul (C*K)) (.eqRefl _) (mul_le_mul_right (C*K) mul))
  have raw := GaussianEulerUpperTailLeftNorm.original_grid_left_norm p q (C*K) E C E z R B
    (unit q+two) (unit q) h hm hE hC (le_refl E) hV step (original_decay_unit_envelope q E (two*E) hE mul)
  have oldDen := positive_product _ _ hV (positive_product _ _ (positive_product _ _ hE hU)
    (GaussianEulerHalfDecayLeftNorm.error_denominator_positive p q (C*K) E hm hE))
  have den := positive_product _ _ (positive_product _ _ hK hU) hV
  apply bounded_radius_mono _ _ _ _ _ oldDen den _ raw
  dsimp only [GaussianEulerUpperTailLeftNorm.numerator,GaussianEulerUpperTailLeftNorm.denominator,
    GaussianEulerUpperTailLeftNorm.errorNumerator,GaussianEulerHalfDecayLeftNorm.errorNumerator,
    GaussianEulerHalfDecayLeftNorm.errorDenominator,coarseNumerator,coarseDenominator,meshCost,rowCost,endpointCost]
  let F := 𝔞(C)*𝔞(E)*𝔞(K)*𝔞(U)^3*𝔞(V)^3
  let G := 2*𝔞(E)^2*𝔞(C)*𝔞(K)^2*𝔞(U)^2*𝔞(V)^3
  ipra_le (3*𝔞(M)*F+(𝔞(H)+𝔞(M))*G)*sl hW+
    (4*𝔞(M)*F*𝔞(E)*𝔞(T))*sl hE+𝔞(M)*F*𝔞(E)*𝔞(T)

theorem original_grid_dyadic_bound (t p q C E K T z R B : PTm n)
    (h : Γ ⊢[PRAAx] source z R B) (hE : Γ ⊢[PRAAx] le one E)
    (hC : Γ ⊢[PRAAx] le one C) (hW : Γ ⊢[PRAAx] le C (E*T))
    (hmesh : Γ ⊢[PRAAx] le (minimumMesh t R T) K)
    (hrow : Γ ⊢[PRAAx] le (minimumPrecision t R T) p)
    (href : Γ ⊢[PRAAx] le (minimumReference t R) q) : Γ ⊢[PRAAx]
    bounded (quadrature evaluatorF p (C*K) E C E (fixedData z B))
      (tailCoefficient R*unit t+one) (unit t) := by
  let S := unit (t+num 2)
  let U := unit p
  let V := unit q
  let X := meshCost R T
  let Y := rowCost R T
  let Z := endpointCost R
  have hk : Γ ⊢[PRAAx] le one K := le_trans (le_add_right one (X*S)) hmesh
  have km : Γ ⊢[PRAAx] le (X*S) K := le_trans (le_add_left (X*S) one) hmesh
  have kr : Γ ⊢[PRAAx] le (Y*S) U := le_trans (GaussianFastValueCut.query_budget Y (t+num 2))
    (GaussianExponentialReference.unit_monotone hrow)
  have kq : Γ ⊢[PRAAx] le (Z*S) V := le_trans (GaussianFastValueCut.query_budget Z (t+num 2))
    (GaussianExponentialReference.unit_monotone href)
  have pow : Γ ⊢[PRAAx] S ≐ num 4*unit t :=
    (congrAp2 powF (by ipra_ring : Γ ⊢[PRAAx] t+num 2 ≐ t+two) (.eqRefl two)).eqTrans
      ((pw_add two t two).eqTrans (by
        have c : Γ ⊢[PRAAx] unit (two : PTm n) ≐ num 4 := by
          exact (pw_succ two one).eqTrans
            ((congrMul ((pw_succ two zero).eqTrans ((congrMul (pw_zero two) (.eqRefl _)).eqTrans (one_mul _)))
              (.eqRefl _)).eqTrans (by ipra_ring))
        exact (congrMul (.eqRefl _) c).eqTrans (mul_comm _ _)))
  have pm := le_congr (congrMul (.eqRefl X) pow) (.eqRefl _) km
  have pr := le_congr (congrMul (.eqRefl Y) pow) (.eqRefl _) kr
  have pq := le_congr (congrMul (.eqRefl Z) pow) (.eqRefl _) kq
  have sum : Γ ⊢[PRAAx] le ((X*U*V+Y*K*V+Z*K*U)*(num 4*unit t)) (num 3*(K*U*V)) := by
    ipra_le (𝔞(U)*𝔞(V))*sl pm+(𝔞(K)*𝔞(V))*sl pr+(𝔞(K)*𝔞(U))*sl pq
  have hden := positive_product _ _ (positive_product _ _ hk (unit_positive p)) (unit_positive q)
  have budget' : Γ ⊢[PRAAx] le ((X*U*V+Y*K*V+Z*K*U)*unit t) (K*U*V) := by
    apply RationalValueBounds.positive_cancel (c := num 4)
      (le_of_eq_add (d := num 3) (by ipra_ring))
    exact le_congr (by ipra_ring) (.eqRefl _)
      (le_trans sum (le_of_eq_add (d := K*U*V) (by ipra_ring)))
  apply bounded_radius_mono _ _ _ _ _ hden (unit_positive t) _
    (original_coarse_grid_bound p q C E K T z R B h hE hC hk hW)
  dsimp only [coarseNumerator,coarseDenominator]
  ipra_le sl budget'

theorem actual_upper_Euler_panel_factorial_bound_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
      ((source (var 7) (var 8) (var 9) ⋏ le one (var 4) ⋏ le one (var 3) ⋏
        le (var 3) (var 4*var 6) ⋏ le (minimumMesh (var 0) (var 8) (var 6)) (var 5) ⋏
        le (minimumPrecision (var 0) (var 8) (var 6)) (var 1) ⋏
        le (minimumReference (var 0) (var 8)) (var 2)) ⟶
       bounded (quadrature evaluatorF (var 1) (var 3*var 5) (var 4) (var 3) (var 4)
         (fixedData (var 7) (var 9))) (tailCoefficient (var 8)*unit (var 0)+one) (unit (var 0))) :=
  closeUniv 10 (.impI (original_grid_dyadic_bound _ _ _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitToTopBound

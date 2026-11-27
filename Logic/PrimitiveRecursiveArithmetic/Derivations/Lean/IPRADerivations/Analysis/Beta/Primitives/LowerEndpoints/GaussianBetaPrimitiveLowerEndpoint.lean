import IPRADerivations.Analysis.Beta.Primitives.CompactGrids.GaussianBetaPrimitiveLinearStep
import IPRADerivations.Analysis.Euler.PositiveAxis.LowerBounds.Powers.GaussianEulerLowerTransformedPower
import IPRADerivations.Analysis.Gamma.Integrals.GaussianGammaIntegralCutoffs

/-!
# The original beta primitive at the original lower cutoff

The original eta denominator is exactly the A-th power of its dyadic
root denominator. The unchanged original lower-time power estimate and
the original primitive's computed unit-disk Horner budget therefore
bound the literal endpoint sample. Both its unscaled value and its exact
product with N are retained. No endpoint law is supplied as a premise.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaPrimitiveLowerEndpoint

open_ipra
open GaussianEulerLowerPowerCoefficients (source)
open GaussianGammaIntegralCutoffs (height etaDen eta_den_positive exact_eta_root_power)
open GaussianEulerBetaPolynomialPrimitive (primitive)
open GaussianBetaPrimitiveLinearStep (argument)
open GaussianEulerPowerIncrement (point)
open GaussianTimeWeightedPolynomialIncrement (value)
open GaussianRationalUniformFirstOrderPolynomial (mass)
open GaussianRationalHorner (qmul evaluate positive_product)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def rootDen (k A R : PTm n) : PTm n := unit (height k A R)
def budget (z B N : PTm n) : PTm n := mass (primitive z B N) one
def endpoint (p z B k A R N : PTm n) : PTm n :=
  GaussianBetaPrimitiveLinearStep.sample p z B one (etaDen k A R) N
def scaledEndpoint (p z B k A R N : PTm n) : PTm n := qmul (naturalPoint N) (endpoint p z B k A R N)
def numerator (p z B k A R N : PTm n) : PTm n := budget z B N*(pw (rootDen k A R) (pred A)*unit p+one)
def denominator (p k A R N : PTm n) : PTm n := N*etaDen k A R*unit p

ipra_subst rootDen [height, GaussianGammaIntegralCutoffs.tailCoefficient]
ipra_subst budget
ipra_subst endpoint [GaussianBetaPrimitiveLinearStep.sample, argument, point, value, etaDen, height, GaussianGammaIntegralCutoffs.tailCoefficient]
ipra_subst scaledEndpoint
ipra_subst numerator
ipra_subst denominator [etaDen, height, GaussianGammaIntegralCutoffs.tailCoefficient]

theorem root_den_positive (k A R : PTm n) : Γ ⊢[PRAAx] le one (rootDen k A R) := unit_positive _
theorem eta_factorization (k A R : PTm n) (hA : Γ ⊢[PRAAx] le one A) : Γ ⊢[PRAAx]
    etaDen k A R ≐ rootDen k A R*pw (rootDen k A R) (pred A) :=
  (exact_eta_root_power k A R).eqSymm.eqTrans
    ((congrAp2 powF (GaussianOffDominantWeights.positive_succ_pred A hA) (.eqRefl _)).eqTrans ((pw_succ _ _).eqTrans (mul_comm _ _)))

theorem original_cutoff_power (p z R B A k : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    bounded (point p z B one (etaDen k A R)) (pw (rootDen k A R) (pred A)*unit p+one) (unit p) := by
  let d := rootDen k A R
  have hd := root_den_positive (Γ := Γ) k A R
  have hs : Γ ⊢[PRAAx] GaussianEulerLowerPowerOrder.source z R B A one d :=
    .andI h (.andI (.andI (le_refl one) hd) hd)
  have old := GaussianEulerLowerTransformedPower.original_power_bound p z R B A one d hs
  have same : Γ ⊢[PRAAx] point p z B (pw one A) (pw d A) ≐ point p z B one (etaDen k A R) := by
    simpa only [point,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
      Matrix.cons_val_four,Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons,GaussianEulerIntegrandName.subst_powerData,subst_ap2] using
      Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (point (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
        (σ := ![p,z,B,pw one A,pw d A]) (σ' := ![p,z,B,one,etaDen k A R])
        (fun i => by
          fin_cases i
          · exact .eqRefl p
          · exact .eqRefl z
          · exact .eqRefl B
          · exact AnalyticNumberTheory.Order.pw_one_base A
          · exact exact_eta_root_power k A R)
  exact bound_congr same
    (congrAdd (.eqRefl _) (AnalyticNumberTheory.Order.pw_one_base (pred A)))
    ((congrMul (AnalyticNumberTheory.Order.pw_one_base (pred A)) (.eqRefl _)).eqTrans (one_mul _)) old

theorem cutoff_argument_bound (k A R N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    bounded (argument one (etaDen k A R) N) one (etaDen k A R*N) := by
  have hd := positive_product (Γ := Γ) _ _ (eta_den_positive k A R) hN
  exact bound_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point one (etaDen k A R*N) hd).eqSymm
    (.eqRefl _) (.eqRefl _) (GaussianDominantPairAlgebra.radius_bounded one _ hd)

theorem argument_unit_disk (k A R N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    bounded (argument one (etaDen k A R) N) one one := by
  have hd := positive_product (Γ := Γ) _ _ (eta_den_positive k A R) hN
  exact bounded_radius_mono _ _ _ _ _ hd (le_refl one) (le_congr (by ipra_ring) (by ipra_ring) hd)
    (cutoff_argument_bound k A R N hN)

theorem primitive_cutoff_bound (z B k A R N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    bounded (evaluate (primitive z B N) (argument one (etaDen k A R) N)) (budget z B N) one :=
  GaussianRationalUniformFirstOrderPolynomial.value_bound _ _ one (le_refl one) (argument_unit_disk k A R N hN)

theorem endpoint_bound_of_factors (p z B a b k A R N M : PTm n)
    (hN : Γ ⊢[PRAAx] le one N)
    (hArgument : Γ ⊢[PRAAx] bounded (argument a b N) one (etaDen k A R*N))
    (hPrimitive : Γ ⊢[PRAAx] bounded (evaluate (primitive z B N) (argument a b N)) M one)
    (hPower : Γ ⊢[PRAAx] bounded (point p z B a b) (pw (rootDen k A R) (pred A)*unit p+one) (unit p)) :
    Γ ⊢[PRAAx] bounded (GaussianBetaPrimitiveLinearStep.sample p z B a b N)
      (M*(pw (rootDen k A R) (pred A)*unit p+one)) (denominator p k A R N) := by
  have hd := positive_product (Γ := Γ) _ _ (eta_den_positive k A R) hN
  have poly := bounded_product _ _ M one one (etaDen k A R*N) (le_refl one) hd hPrimitive hArgument
  have weighted := bounded_product _ _ _ _ _ _ (unit_positive p) (positive_product _ _ (le_refl one) hd) hPower poly
  exact bound_congr (.eqRefl _) (by ipra_ring) (by unfold denominator; ipra_ring) weighted

/-- Unchanged original sample at eta=1/etaDen, with the exact N denominator. -/
theorem original_lower_endpoint_bound (p z R B A k N : PTm n) (h : Γ ⊢[PRAAx] source z R B A)
    (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    bounded (endpoint p z B k A R N) (numerator p z B k A R N) (denominator p k A R N) :=
  endpoint_bound_of_factors p z B one (etaDen k A R) k A R N (budget z B N) hN
    (cutoff_argument_bound k A R N hN) (primitive_cutoff_bound z B k A R N hN)
    (original_cutoff_power p z R B A k h)

/-- Multiplying by N cancels the factor N in the endpoint bound's denominator. -/
theorem scale_endpoint_bound (p k A R N y M : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (h : Γ ⊢[PRAAx] bounded y M (denominator p k A R N)) :
    Γ ⊢[PRAAx] bounded (qmul (naturalPoint N) y) M (etaDen k A R*unit p) := by
  have hd := positive_product (Γ := Γ) _ _ (positive_product _ _ hN (eta_den_positive k A R)) (unit_positive p)
  have natural : Γ ⊢[PRAAx] bounded (naturalPoint N) N one :=
    bound_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point N one (le_refl one)).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianDominantPairAlgebra.radius_bounded N one (le_refl one))
  have product := bounded_product _ _ N one _ _ (le_refl one) hd natural h
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ (le_refl one) hd)
    (positive_product _ _ (eta_den_positive k A R) (unit_positive p))
    (le_of_eq_add (d := zero) (by ipra_ring)) product

/-- Exact original endpoint multiplied by N; the original requested
power observation p is preserved. -/
theorem scaled_lower_endpoint_bound (p z R B A k N : PTm n) (h : Γ ⊢[PRAAx] source z R B A)
    (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    bounded (scaledEndpoint p z B k A R N) (numerator p z B k A R N) (etaDen k A R*unit p) :=
  scale_endpoint_bound p k A R N _ _ hN (original_lower_endpoint_bound p z R B A k N h hN)

theorem dyadic_bound_of_eta_bound (p k A R y M : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (h : Γ ⊢[PRAAx] bounded y (M*(pw (rootDen k A R) (pred A)*unit p+one)) (etaDen k A R*unit p)) :
    Γ ⊢[PRAAx] bounded y (M*unit p+M*rootDen k A R) (rootDen k A R*unit p) := by
  let d := rootDen k A R
  let E := etaDen k A R
  let P := unit p
  have hd := positive_product (Γ := Γ) _ _ (eta_den_positive k A R) (unit_positive p)
  have compare : Γ ⊢[PRAAx] le ((M*(pw d (pred A)*P+one))*(d*P)) ((M*P+M*d)*(E*P)) := by
    have e := natEq (eta_factorization (Γ := Γ) k A R hA)
    have growth : Γ ⊢[PRAAx] le (M*d*P) (M*d*P*E) :=
      le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (M*d*P) (eta_den_positive (Γ := Γ) k A R))
    have g := natEq (eq_add_of_le growth)
    apply le_of_eq_add (d := LeanProofs.IPRA.PTm.monus (M*d*P*E) (M*d*P))
    apply deriveNat
    dsimp only [E,d] at g ⊢
    ipra_simps
    rw [e] at g ⊢
    linear_combination g
  exact bounded_radius_mono _ _ _ _ _ hd
    (positive_product _ _ (root_den_positive k A R) (unit_positive p)) compare h

/-- In particular, the exact N-scaled endpoint is at most M/2^height
plus M times its one original observation error. M is computed from the
SAME original primitive on the unit disk before choosing the cutoff. -/
theorem scaled_dyadic_bound (p z R B A k N : PTm n) (h : Γ ⊢[PRAAx] source z R B A)
    (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    bounded (scaledEndpoint p z B k A R N) (budget z B N*unit p+budget z B N*rootDen k A R)
      (rootDen k A R*unit p) :=
  dyadic_bound_of_eta_bound p k A R _ _ h.andE₁ (scaled_lower_endpoint_bound p z R B A k N h hN)

def precision (t z B N : PTm n) : PTm n := GaussianFastValueCut.exponent (budget z B N) (ConciseIPRA.PTm.succ t)
ipra_subst precision

/-- A computed original observation and original cutoff, both at the
same numerical precision, make the exact N-scaled endpoint <=2^-t. -/
theorem constructive_lower_endpoint_small (t z R B A N : PTm n) (h : Γ ⊢[PRAAx] source z R B A)
    (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    bounded (scaledEndpoint (precision t z B N) z B (precision t z B N) A R N) one (unit t) := by
  let q := precision t z B N
  let d := rootDen q A R
  let M := budget z B N
  let P := unit (ConciseIPRA.PTm.succ t)
  have later : Γ ⊢[PRAAx] le q (height q A R) :=
    le_of_eq_add (d := A+GaussianGammaIntegralCutoffs.tailCoefficient R+LeanProofs.IPRA.PTm.num 10) (by unfold height; ipra_ring)
  have growth : Γ ⊢[PRAAx] le (unit q) d := GaussianExponentialReference.unit_monotone later
  have query : Γ ⊢[PRAAx] le (M*P) (unit q) := GaussianFastValueCut.query_budget _ _
  have first : Γ ⊢[PRAAx] le (M*P*unit q) (d*unit q) :=
    le_trans (mul_le_mul_right (unit q) query) (mul_le_mul_right (unit q) growth)
  have last : Γ ⊢[PRAAx] le (M*P*d) (unit q*d) := mul_le_mul_right d query
  have compare : Γ ⊢[PRAAx] le ((M*unit q+M*d)*P) (two*(d*unit q)) :=
    le_congr (by ipra_ring) (by ipra_ring) (add_le_add₂ first last)
  have small : Γ ⊢[PRAAx] bounded (scaledEndpoint q z B q A R N) two P :=
    bounded_radius_mono _ _ _ _ _ (positive_product _ _ (root_den_positive q A R) (unit_positive q))
      (unit_positive (ConciseIPRA.PTm.succ t)) compare (scaled_dyadic_bound q z R B A q N h hN)
  exact bounded_radius_mono _ _ _ _ _ (unit_positive (ConciseIPRA.PTm.succ t)) (unit_positive t)
    (le_of_eq_add (d := zero) ((congrMul (.eqRefl one) (pw_succ two t)).eqTrans (by unfold unit; ipra_ring))) small

theorem original_beta_lower_endpoint_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((source (var 1) (var 2) (var 3) (var 4) ⋏ le one (var 6)) ⟶
      bounded (endpoint (var 0) (var 1) (var 3) (var 5) (var 4) (var 2) (var 6))
        (numerator (var 0) (var 1) (var 3) (var 5) (var 4) (var 2) (var 6))
        (denominator (var 0) (var 5) (var 4) (var 2) (var 6))) :=
  closeUniv 7 (.impI (original_lower_endpoint_bound _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))
theorem original_N_scaled_beta_lower_endpoint_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((source (var 1) (var 2) (var 3) (var 4) ⋏ le one (var 6)) ⟶
      bounded (scaledEndpoint (var 0) (var 1) (var 3) (var 5) (var 4) (var 2) (var 6))
        (numerator (var 0) (var 1) (var 3) (var 5) (var 4) (var 2) (var 6))
        (etaDen (var 5) (var 4) (var 2)*unit (var 0))) :=
  closeUniv 7 (.impI (scaled_lower_endpoint_bound _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))
theorem original_beta_lower_endpoint_dyadic_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((source (var 1) (var 2) (var 3) (var 4) ⋏ le one (var 6)) ⟶
      bounded (scaledEndpoint (var 0) (var 1) (var 3) (var 5) (var 4) (var 2) (var 6))
        (budget (var 1) (var 3) (var 6)*unit (var 0)+budget (var 1) (var 3) (var 6)*rootDen (var 5) (var 4) (var 2))
        (rootDen (var 5) (var 4) (var 2)*unit (var 0))) :=
  closeUniv 7 (.impI (scaled_dyadic_bound _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))
theorem original_beta_lower_endpoint_constructively_small_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((source (var 1) (var 2) (var 3) (var 4) ⋏ le one (var 5)) ⟶
      bounded (scaledEndpoint (precision (var 0) (var 1) (var 3) (var 5)) (var 1) (var 3)
        (precision (var 0) (var 1) (var 3) (var 5)) (var 4) (var 2) (var 5)) one (unit (var 0))) :=
  closeUniv 6 (.impI (constructive_lower_endpoint_small _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBetaPrimitiveLowerEndpoint

import IPRADerivations.Analysis.Gamma.GaussianGammaFixedCoefficientVariation

/-!
# Actual regular names for every original fixed Gamma coefficient

The raw samples are unchanged coefficient readers of the original
cofinal polynomial observations, at the computed radius e+1. Their
derived numerical modulus retimes that original program into a genuine
fast Gaussian name for every internal degree e. Each named sample is
literally an original cofinal coefficient at an explicit computed clock.
Identification between different coefficient radii and the full C19
series statement remain separate consequences.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaHigherCoefficientName

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaFixedCoefficientVariation (modulus fixed_coefficient_distance)
open GaussianGammaInputPrecisionNorm (radiusNumerator radiusDenominator denominator_positive)
open GaussianGammaFiniteCoefficientStability (cofinalObservation fixedCoefficient)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalHorner (canonical)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def rawValue (p e : PTm n) : PTm n := cofinalObservation p (succ e) e
def rawF : PR 2 := PTm.toPR (rawValue (var 0) (var 1))
def modulusData (e : PTm n) : PTm n := modulus (succ e) e
def nameF : PR 2 := GaussianFastValueCut.nameF rawF
def data (e : PTm n) : PTm n := GaussianFastValueCut.nameData (modulusData e) e
def clock (p e : PTm n) : PTm n := GaussianFastValueCut.exponent (modulusData e) p
def sample (p e : PTm n) : PTm n := ap2 nameF p (data e)
@[simp] theorem subst_rawValue {m : ℕ} (σ : Fin n → PTm m) (p e : PTm n) :
    Syn.subst σ (rawValue p e) = rawValue (Syn.subst σ p) (Syn.subst σ e) := by simp [rawValue]
@[simp] theorem subst_modulusData {m : ℕ} (σ : Fin n → PTm m) (e : PTm n) :
    Syn.subst σ (modulusData e) = modulusData (Syn.subst σ e) := by simp [modulusData]
@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (e : PTm n) :
    Syn.subst σ (data e) = data (Syn.subst σ e) := by simp [data]
@[simp] theorem subst_clock {m : ℕ} (σ : Fin n → PTm m) (p e : PTm n) :
    Syn.subst σ (clock p e) = clock (Syn.subst σ p) (Syn.subst σ e) := by simp [clock]
@[simp] theorem subst_sample {m : ℕ} (σ : Fin n → PTm m) (p e : PTm n) :
    Syn.subst σ (sample p e) = sample (Syn.subst σ p) (Syn.subst σ e) := by simp [sample]

theorem raw_at (p e : PTm n) : Γ ⊢[PRAAx] ap2 rawF p e ≐ rawValue p e := by
  simpa only [rawF,ap2,subst_rawValue,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    toPR_eq (Γ := Γ) (rawValue (var 0) (var 1) : PTm 2) ![p,e]

theorem later_distance (s t a b R e : PTm n) (ha : Γ ⊢[PRAAx] le s a) (hb : Γ ⊢[PRAAx] le t b)
    (hR : Γ ⊢[PRAAx] le one R) (he : Γ ⊢[PRAAx] le e (succ (two*R))) : Γ ⊢[PRAAx]
    distanceBounded (fixedCoefficient a R e) (fixedCoefficient b R e)
      (modulus R e*radiusNumerator s t) (radiusDenominator s t) := by
  have sa : Γ ⊢[PRAAx] le (unit s) (unit a) := GaussianFactorBudget.power_monotone_length two s a (le_succ_self one) ha
  have tb : Γ ⊢[PRAAx] le (unit t) (unit b) := GaussianFactorBudget.power_monotone_length two t b (le_succ_self one) hb
  have first := mul_le_mul_right (unit a*unit s) tb
  have second := mul_le_mul_right (unit b*unit t) sa
  have base : Γ ⊢[PRAAx] le ((unit a+unit b)*(unit s*unit t)) ((unit s+unit t)*(unit a*unit b)) :=
    le_congr (by ipra_ring) (by ipra_ring) (add_le_add₂ first second)
  have budget : Γ ⊢[PRAAx] le
      ((modulus R e*radiusNumerator a b)*radiusDenominator s t)
      ((modulus R e*radiusNumerator s t)*radiusDenominator a b) :=
    le_congr (by unfold radiusNumerator radiusDenominator; ipra_ring)
      (by unfold radiusNumerator radiusDenominator; ipra_ring) (mul_le_mul_right (modulus R e) base)
  exact GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ _ _
    (denominator_positive a b) (denominator_positive s t) budget (fixed_coefficient_distance a b R e hR he)

theorem raw_regularity (p q e : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (rawValue p e) (rawValue q e)
      (modulusData e*(unit p+unit q)) (unit p*unit q) := by
  have head : Γ ⊢[PRAAx] le e (succ (two*succ e)) := le_of_eq_add (d := e+succ two) (by ipra_ring)
  have pc := le_trans (le_add_right p e) (GaussianGammaCofinalCoefficientName.coefficient_precision_cofinal (Γ := Γ) (p+e) (succ e))
  have qc := le_trans (le_add_right q e) (GaussianGammaCofinalCoefficientName.coefficient_precision_cofinal (Γ := Γ) (q+e) (succ e))
  exact distance_congr (GaussianGammaFiniteCoefficientStability.cofinal_observation_fixed p (succ e) e head).eqSymm
    (GaussianGammaFiniteCoefficientStability.cofinal_observation_fixed q (succ e) e head).eqSymm (.eqRefl _) (.eqRefl _)
      (later_distance p q _ _ (succ e) e pc qc (zero_lt_succ e) head)

theorem raw_regular (e : PTm n) : Γ ⊢[PRAAx] GaussianFastValueCut.regular rawF (modulusData e) e := by
  refine .allI (.allI ?_)
  have actual := distance_congr (raw_at (Γ := (Γ.map Fm.shift).map Fm.shift) (var 1) (Syn.shift (Syn.shift e))).eqSymm
    (raw_at (var 0) _).eqSymm (.eqRefl _) (.eqRefl _) (raw_regularity (var 1) (var 0) (Syn.shift (Syn.shift e)))
  simpa only [GaussianFastValueCut.regular,Syn.shift,subst_modulusData,unit] using actual

theorem name_regular (e : PTm n) : Γ ⊢[PRAAx] pointCN nameF (data e) :=
  GaussianFastValueCut.name_fast rawF (modulusData e) e (raw_regular e)

theorem raw_canonical (p e : PTm n) : Γ ⊢[PRAAx] canonical (rawValue p e) :=
  GaussianRationalPolynomialExponentialCoefficients.exponent_canonical _ _ _
    (GaussianRationalPolynomialProduct.product_canonical _ _ _ _) (GaussianRationalPolynomialProduct.product_length _ _ _ _)

theorem sample_at (p e : PTm n) : Γ ⊢[PRAAx] sample p e ≐ cofinalObservation (clock p e) (succ e) e :=
  (GaussianFastValueCut.name_at rawF (modulusData e) e p).eqTrans
    ((GaussianNameArithmetic.recode_congr (raw_at (clock p e) e)).eqTrans
      (GaussianNamedSmallPerturbationTransport.recode_fixed _ (raw_canonical _ _)))

theorem sample_fixed_coefficient (p e : PTm n) : Γ ⊢[PRAAx] sample p e ≐
    fixedCoefficient (GaussianGammaCofinalCoefficientName.coefficientPrecision (clock p e+e) (succ e)) (succ e) e :=
  (sample_at p e).eqTrans (GaussianGammaFiniteCoefficientStability.effective_cofinal_observation (clock p e) e)

def coefficientF : PR 3 := PTm.toPR (sample (var 1) (var 0))
theorem coefficient_program (e p x : PTm n) : Γ ⊢[PRAAx] PTm.app coefficientF ![e,p,x] ≐ sample p e := by
  simpa only [coefficientF,subst_sample,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    toPR_eq (Γ := Γ) (sample (var 1) (var 0) : PTm 3) ![e,p,x]

theorem original_all_degree_Gamma_coefficient_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (pointCN nameF (data (var 0))) := closeUniv 1 (name_regular _)
theorem original_Gamma_coefficient_named_cofinal_sample_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (sample (var 0) (var 1) ≐ cofinalObservation (clock (var 0) (var 1)) (succ (var 1)) (var 1)) :=
  closeUniv 2 (sample_at _ _)
theorem original_Gamma_all_degree_coefficient_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (PTm.app coefficientF ![var 0,var 1,var 2] ≐ sample (var 1) (var 0)) := closeUniv 3 (coefficient_program _ _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaHigherCoefficientName

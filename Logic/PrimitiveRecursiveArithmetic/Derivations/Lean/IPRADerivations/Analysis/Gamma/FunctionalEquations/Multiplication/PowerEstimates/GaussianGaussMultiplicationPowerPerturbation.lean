import IPRADerivations.Analysis.Exponential.GaussianExponentialAddition
import IPRADerivations.Analysis.Exponential.Names.GaussianExponentialRadiusIndependence
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.PowerEstimates.GaussianGaussMultiplicationRelativeExponential
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedMultiplyRate
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateTransport

/-!
# Relative perturbation of the actual Gauss multiplication powers

The row power factors into the limiting power and the radius-one
exponential of the certified logarithm correction. A numerical bound
on the limiting power gives the corresponding sharp weighted rate.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGaussMultiplicationPowerPerturbation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit)
open GaussianGaussMultiplicationPowerRate
  (amplification multiplier_bound exponentF exponentData radius powerF powerData rowLogData limitLogData row_power_input limit_power_input)
open GaussianGaussMultiplicationRelativeExponential
  (relativeF relativeData relativeExpF relativeExpData relative_input relative_exponential_near_one exponent_addition)
open GaussianNameArithmetic (addF addData multiplyF multiplyData)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator denominator_positive)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans cross_to_diagonal)
open GaussianNameRingLaws (oneF one_at one_fast)
open GaussianNamedMultiplyRate (sampleBound)
open GaussianRadiusExponentialName (data name_regular)
open GaussianRationalMetric (distanceBounded)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def limitData (z R B m : PTm n) : PTm n := powerData z R B m (limitLogData m)
def rowData (z R B m N : PTm n) : PTm n := powerData z R B m (rowLogData m N)

@[simp] theorem subst_limitData {l : ℕ} (σ : Fin n → PTm l) (z R B m : PTm n) :
    Syn.subst σ (limitData z R B m) = limitData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ m) := by
  simp [limitData]
@[simp] theorem subst_rowData {l : ℕ} (σ : Fin n → PTm l) (z R B m N : PTm n) :
    Syn.subst σ (rowData z R B m N) = rowData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ m) (Syn.subst σ N) := by
  simp [rowData]

theorem power_product_cross (z R B m N : PTm n)
    (hm : Γ ⊢[PRAAx] le one m) (hN : Γ ⊢[PRAAx] le one N) (hA : Γ ⊢[PRAAx] le (amplification R m) N)
    (hB : Γ ⊢[PRAAx] le one B) (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) : Γ ⊢[PRAAx]
    crossEquivalent powerF (multiplyF powerF relativeExpF) (rowData z R B m N)
      (multiplyData powerF relativeExpF (limitData z R B m) (relativeExpData z R B m N)) := by
  let x := exponentData z R B m (rowLogData m N)
  let y := exponentData z R B m (limitLogData m)
  let v := relativeData z R B m N
  let W := radius R m
  let C := W+one
  have hc : Γ ⊢[PRAAx] le one C := le_add_left one W
  have hw : Γ ⊢[PRAAx] le W C := le_add_right W one
  have row := row_power_input z R B m N hm hN hB hz
  have lim := limit_power_input z R B m hm hB hz
  have rel := relative_input z R B m N hm hN hA (multiplier_bound z R B m hm hB hz)
  have lim' := GaussianExponentialRadiusIndependence.input_widen exponentF W C y lim hw
  have rel' := GaussianExponentialRadiusIndependence.input_widen relativeF one C v rel hc
  have sum := GaussianExponentialReference.add_input exponentF relativeF C y v lim' rel'
  have add := GaussianExponentialRadiusIndependence.independent_radii_proper exponentF (addF exponentF relativeF)
    W (C+C) x (addData y v) row sum (exponent_addition z R B m N hm hN hB hz)
  have product := cross_symm _ _ _ _
    (GaussianExponentialAddition.exponential_add_cross exponentF relativeF C y v hc lim' rel')
  have first := GaussianExponentialRadiusIndependence.same_input_cross exponentF C W y lim' lim
  have second := GaussianExponentialRadiusIndependence.same_input_cross relativeF C one v rel' rel
  have shrink := GaussianNameArithmetic.multiply_equivalent powerF powerF relativeExpF relativeExpF
    (data C y) (data W y) (data C v) (data one v)
    (name_regular _ _ _ lim') (name_regular _ _ _ lim) (name_regular _ _ _ rel') (name_regular _ _ _ rel)
    (cross_to_diagonal _ _ _ _ first) (cross_to_diagonal _ _ _ _ second)
  exact cross_trans _ _ _ _ _ _ (cross_trans _ _ _ _ _ _ add product) shrink

theorem relative_rate (z R B m N anchor : PTm n)
    (hm : Γ ⊢[PRAAx] le one m) (hN : Γ ⊢[PRAAx] le one N) (hA : Γ ⊢[PRAAx] le (amplification R m) N)
    (hB : Γ ⊢[PRAAx] le one B) (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) : Γ ⊢[PRAAx]
    independentRate relativeExpF oneF (relativeExpData z R B m N) anchor (two*amplification R m) N := by
  let sh (u : PTm n) := Syn.shift (Syn.shift u)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have ms : Δ ⊢[PRAAx] le one (sh m) := by simpa [Δ,Fm.shift,Syn.shift,sh] using hm.shift.shift
  have ns : Δ ⊢[PRAAx] le one (sh N) := by simpa [Δ,Fm.shift,Syn.shift,sh] using hN.shift.shift
  have bs : Δ ⊢[PRAAx] le one (sh B) := by simpa [Δ,Fm.shift,Syn.shift,sh] using hB.shift.shift
  have ast : Δ ⊢[PRAAx] le (amplification (sh R) (sh m)) (sh N) := by
    simpa [Δ,Fm.shift,Syn.shift,sh] using hA.shift.shift
  have zs : Δ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (sh z) (sh R*sh B) := by
    simpa [Δ,Fm.shift,Syn.shift,sh] using hz.shift.shift
  refine .allI (.allI ?_)
  let p : PTm (n+2) := var 1
  let q : PTm (n+2) := var 0
  let A := two*amplification (sh R) (sh m)
  let D := sh N
  let x := relativeExpData (sh z) (sh R) (sh B) (sh m) D
  have near := relative_exponential_near_one (sh z) (sh R) (sh B) (sh m) D p ms ns ast bs zs
  have strong : Δ ⊢[PRAAx] distanceBounded (ap2 relativeExpF p x) (ap2 oneF q (sh anchor)) A D :=
    GaussianRationalDistanceOrder.distance_congr (.eqRefl _) (one_at q (sh anchor)).eqSymm (.eqRefl _) (.eqRefl _) near
  have budget : Δ ⊢[PRAAx] le (A*rateDenominator D p q) (rateNumerator A D p q*D) :=
    le_of_eq_add (d := (D*D)*(unit p+unit q)) (by unfold rateNumerator rateDenominator; ipra_ring)
  have estimate := GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ _ _ ns
    (denominator_positive D p q ns) budget strong
  simpa only [independentRate,Syn.shift,sh,p,q,A,D,x,Δ,GaussianGaussMultiplicationRelativeExponential.subst_relativeExpData,
    GaussianGaussMultiplicationPowerRate.subst_amplification,PTm.subst_mul,two,one,ConciseIPRA.PTm.subst_zero,
    ConciseIPRA.PTm.subst_succ] using estimate

theorem weighted_power_rate_via (F : PR 2) (d z R B m N M : PTm n)
    (hm : Γ ⊢[PRAAx] le one m) (hN : Γ ⊢[PRAAx] le one N) (hA : Γ ⊢[PRAAx] le (amplification R m) N)
    (hB : Γ ⊢[PRAAx] le one B) (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B))
    (hF : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN F d)
    (he : Γ ⊢[PRAAx] crossEquivalent powerF F (limitData z R B m) d)
    (hM : Γ ⊢[PRAAx] sampleBound F d M) : Γ ⊢[PRAAx]
    independentRate powerF powerF (rowData z R B m N) (limitData z R B m) (two*amplification R m*M) N := by
  let a := relativeExpData z R B m N
  let X := two*amplification R m
  let M' := GaussianNameBounds.U relativeExpF a
  have hP := name_regular _ _ _ (limit_power_input z R B m hm hB hz)
  have hG := name_regular _ _ _ (relative_input z R B m N hm hN hA (multiplier_bound z R B m hm hB hz))
  have hg : Γ ⊢[PRAAx] sampleBound relativeExpF a M' :=
    GaussianNameBounds.all_samples_bounded _ _ hG
  have raw := GaussianNamedMultiplyRate.independent_rate F relativeExpF F oneF
    d a d d zero one X N M' M (le_refl one) hN hF hG hF (one_fast d) hg hM
    (GaussianNamedDifferenceRate.self_rate F d hF) (relative_rate z R B m N d hm hN hA hB hz)
  have normalized := GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ (X*M) N
    (by unfold GaussianNamedMultiplyRate.leadingNumerator; ipra_ring)
    (by unfold GaussianNamedMultiplyRate.leadingDenominator; ipra_ring) raw
  have product := GaussianNameArithmetic.multiply_equivalent powerF F relativeExpF relativeExpF (limitData z R B m) d a a
    hP hF hG hG (cross_to_diagonal _ _ _ _ he) (cross_to_diagonal _ _ _ _ (cross_refl relativeExpF a hG))
  exact GaussianNamedRateTransport.transport _ _ _ _ _ _ _ _ _ _ hN normalized
    (cross_trans _ _ _ _ _ _ (power_product_cross z R B m N hm hN hA hB hz) product)
    (cross_trans _ _ _ _ _ _ he (cross_symm _ _ _ _ (GaussianNameRingLaws.multiply_one F d hF)))

theorem weighted_power_rate (z R B m N M : PTm n)
    (hm : Γ ⊢[PRAAx] le one m) (hN : Γ ⊢[PRAAx] le one N) (hA : Γ ⊢[PRAAx] le (amplification R m) N)
    (hB : Γ ⊢[PRAAx] le one B) (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B))
    (hM : Γ ⊢[PRAAx] sampleBound powerF (limitData z R B m) M) : Γ ⊢[PRAAx]
    independentRate powerF powerF (rowData z R B m N) (limitData z R B m) (two*amplification R m*M) N := by
  have hP := name_regular _ _ _ (limit_power_input z R B m hm hB hz)
  exact weighted_power_rate_via powerF (limitData z R B m) z R B m N M hm hN hA hB hz hP
    (cross_refl _ _ hP) hM

end LeanProofs.IPRA.Analysis.GaussianGaussMultiplicationPowerPerturbation

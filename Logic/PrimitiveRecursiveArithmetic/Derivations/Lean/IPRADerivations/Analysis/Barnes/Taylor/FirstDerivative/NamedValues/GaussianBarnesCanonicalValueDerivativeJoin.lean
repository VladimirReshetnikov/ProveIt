import IPRADerivations.Analysis.Barnes.TailControl.GaussianBarnesCanonicalTailExponentialQuotient
import IPRADerivations.Analysis.Barnes.CanonicalProducts.GaussianBarnesCanonicalUniformContinuity
import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.FiniteFactors.GaussianBarnesCanonicalHeadCorrectionDerivative
import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.GaussianNamedNativeProductDerivativeRate
import IPRADerivations.Analysis.Names.FiniteOperations.Products.GaussianNamedBoundedProductObservation

/-!
# Derivative assembly at the original Barnes split

The entire cofinal tail is already differentiated. This assembly uses
a quotient estimate for the fixed prefix and its checked disk
continuity. All leading constants depend only on the disk and the
supplied prefix derivative constant.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalValueDerivativeJoin

open_ipra
open ComplexLogarithmRemainder (add normSq)
open GaussianBarnesCanonicalDerivativeTailBinding (base_source shifted_source)
open GaussianBarnesCanonicalDiskBound (prefixBound prefix_sample_bound)
open GaussianBarnesCanonicalHeadCorrectionDerivative (point_increment)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial initial_positive)
open GaussianBarnesCanonicalTailExponentialMargin (exponentialBound exponential_samples_bound derivative_sample_bound)
open GaussianEuclideanDistanceName (pointCN)
open GaussianL1 (norm1 normSq_le_norm1_square)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedMultiplyRate (sampleBound)
open GaussianRationalHorner (ofGaussian ofGaussian_represents positive_product)
open GaussianRationalMetric (distanceBounded bounded_of_cleared)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "I" => GaussianBarnesCanonicalValue.prefixF
local notation "id" => GaussianBarnesCanonicalValue.prefixData
local notation "T" => GaussianBarnesCanonicalTailExponential.nameF
local notation "td" => GaussianBarnesCanonicalTailExponential.data
local notation "L" => GaussianBarnesCanonicalDerivativeCofinal.nameF
local notation "ld" => GaussianBarnesCanonicalLogCofinal.data
local notation "DG" => GaussianBarnesCanonicalTailExponentialDerivative.derivativeF
local notation "dg" => GaussianBarnesCanonicalTailExponentialDerivative.derivativeData
local notation "G" => GaussianBarnesCanonicalValue.nameF
local notation "gd" => GaussianBarnesCanonicalValue.data
local notation "QF" => GaussianNamedDifferenceQuotient.nameF
local notation "qd" => GaussianNamedDifferenceQuotient.data

abbrev input (z h R B : PTm n) : Fm PTm n := GaussianBarnesCanonicalTailExponentialQuotient.input z h R B
abbrev denominator (R B : PTm n) : PTm n := GaussianBarnesCanonicalTailExponentialQuotient.denominator R B

def tailDerivativeBound (R : PTm n) : PTm n :=
  exponentialBound R*GaussianBarnesCanonicalDerivativeRow.boundNumerator R

def prefixGain (R : PTm n) : PTm n :=
  GaussianBarnesCanonicalUniformContinuity.gain R (initial R)*initial R

def numerator (R K h : PTm n) : PTm n :=
  (prefixBound R*(two*GaussianBarnesCanonicalTailExponentialDerivative.errorGain R)+
    tailDerivativeBound R*prefixGain R+exponentialBound R*K)*norm1 h

def derivativeF (D : PR 2) : PR 2 := GaussianNamedNativeProductDerivativeRate.derivativeF I T D DG

def derivativeData (D : PR 2) (z R B d : PTm n) : PTm n :=
  GaussianNamedNativeProductDerivativeRate.derivativeData I T D DG (id z R B) (td z R B) d (dg z R B)

theorem prefix_samples_bound (z R B : PTm n) (hs : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] sampleBound I (id z R B) (prefixBound R) := by
  refine .allI ?_
  let sh (x : PTm n) := Syn.shift x
  have hh : Γ.map Fm.shift ⊢[PRAAx] source (sh z) (sh R) (sh B) := by
    simpa [Fm.shift,Syn.shift,sh] using hs.shift
  simpa only [sampleBound,Syn.shift,sh,GaussianBarnesCanonicalValue.subst_prefixData,
    GaussianBarnesCanonicalDiskBound.prefixBound, GaussianBarnesCanonicalDiskBound.subst_prefactorBound,
    GaussianBarnesCanonicalHead.subst_cap,GaussianBarnesCanonicalLogSchedule.subst_initial,
    PTm.subst_mul,ConciseIPRA.PTm.subst_zero] using prefix_sample_bound (var 0) (sh z) (sh R) (sh B) hh

theorem tail_derivative_samples_bound (z R B : PTm n) (hs : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] sampleBound DG (dg z R B) (tailDerivativeBound R) := by
  have hb : Γ ⊢[PRAAx] sampleBound L (ld z R B) (GaussianBarnesCanonicalDerivativeRow.boundNumerator R) := by
    refine .allI ?_
    let sh (x : PTm n) := Syn.shift x
    have hh : Γ.map Fm.shift ⊢[PRAAx] source (sh z) (sh R) (sh B) := by
      simpa [Fm.shift,Syn.shift,sh] using hs.shift
    simpa only [sampleBound,Syn.shift,sh,GaussianBarnesCanonicalLogCofinal.subst_data,
      GaussianBarnesCanonicalDerivativeRow.subst_boundNumerator] using
      derivative_sample_bound (var 0) (sh z) (sh R) (sh B) hh
  exact GaussianNamedBoundedProductObservation.sample_bounds T L (td z R B) (ld z R B) _ _
    (exponential_samples_bound z R B hs) hb

theorem prefix_rate (z h R B : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source (add z h) R B) :
    Γ ⊢[PRAAx] independentRate I I (id (add z h) R B) (id z R B) (prefixGain R*norm1 h) (denominator R B) := by
  let H := norm1 h
  let E := denominator R B
  have hB := hz.andE₁
  have hE := positive_product _ _ hB (initial_positive R)
  have hb := bounded_of_cleared _ _ B H B hB hB (ofGaussian_represents h B hB)
    (le_congr (mul_comm _ _) (.eqRefl _) (mul_le_mul_right (B*B) (normSq_le_norm1_square h)))
  have dist : Γ ⊢[PRAAx] distanceBounded (ofGaussian (add z h) B) (ofGaussian z B) H B :=
    GaussianRationalReciprocal.bound_congr (point_increment z h B hB).eqSymm (.eqRefl _) (.eqRefl _) hb
  have raw := GaussianBarnesCanonicalUniformContinuity.finite_rate (add z h) z R B B (initial R) H B hw hz hB dist
  apply GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ hB hE _ raw
  apply le_of_eq_add (d := ConciseIPRA.PTm.zero)
  change Γ ⊢[PRAAx]
    (GaussianBarnesCanonicalUniformContinuity.gain R (initial R)*initial R*H)*B ≐
      (GaussianBarnesCanonicalUniformContinuity.gain R (initial R)*H)*(B*initial R)+ConciseIPRA.PTm.zero
  ipra_ring

theorem join (D : PR 2) (z h R B d K : PTm n) (hs : Γ ⊢[PRAAx] input z h R B)
    (hd : Γ ⊢[PRAAx] pointCN D d)
    (hp : Γ ⊢[PRAAx] independentRate (QF I I) D (qd I I (id (add z h) R B) (id z R B) h B) d
      (K*norm1 h) (denominator R B)) :
    Γ ⊢[PRAAx] independentRate (QF G G) (derivativeF D)
      (qd G G (gd (add z h) R B) (gd z R B) h B) (derivativeData D z R B d) (numerator R K h) (denominator R B) := by
  let H := norm1 h
  let E := denominator R B
  let M := prefixBound R
  let P := tailDerivativeBound R
  let N := exponentialBound R
  let A := GaussianBarnesCanonicalTailExponentialQuotient.numerator h R
  let C := K*H
  let W := prefixGain R*H
  have hz := base_source z h R B H hs.andE₁.andE₁
  have hw := shifted_source z h R B H hs.andE₁.andE₁
  have hB := hz.andE₁
  have hE := positive_product _ _ hB (initial_positive R)
  have sep : Γ ⊢[PRAAx] GaussianNamedDifferenceQuotient.separated h B := .andI hB hs.andE₂
  have rt := GaussianNamedNativeProductDerivativeRate.rate I T D DG (id (add z h) R B) (id z R B)
    (td (add z h) R B) (td z R B) d (dg z R B) h B A C W E P M N
    (GaussianBarnesCanonicalValue.prefix_regular _ _ _ hw) (GaussianBarnesCanonicalValue.prefix_regular _ _ _ hz)
    (GaussianBarnesCanonicalTailExponential.regular _ _ _ hw) (GaussianBarnesCanonicalTailExponential.regular _ _ _ hz)
    hd (GaussianBarnesCanonicalTailExponentialDerivative.derivative_regular z R B hz)
    sep hE (tail_derivative_samples_bound z R B hz) (prefix_samples_bound (add z h) R B hw)
    (exponential_samples_bound z R B hz) (GaussianBarnesCanonicalTailExponentialQuotient.rate z h R B hs)
    hp (prefix_rate z h R B hz hw)
  exact GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ hE hE (le_of_eq_add (d := ConciseIPRA.PTm.zero) (by
    change Γ ⊢[PRAAx]
      ((M*(two*GaussianBarnesCanonicalTailExponentialDerivative.errorGain R)+P*prefixGain R+N*K)*H)*E ≐
        (M*(two*GaussianBarnesCanonicalTailExponentialDerivative.errorGain R*H)+P*(prefixGain R*H)+N*(K*H))*E+
          ConciseIPRA.PTm.zero
    ipra_ring)) rt

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalValueDerivativeJoin

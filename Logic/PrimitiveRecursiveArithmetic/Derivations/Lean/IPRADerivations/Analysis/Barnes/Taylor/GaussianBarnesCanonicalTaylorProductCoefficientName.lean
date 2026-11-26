import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalTaylorProductCoefficientCauchy
import IPRADerivations.Analysis.Gamma.GaussianGammaFixedCoefficientVariation
import IPRADerivations.Analysis.Exponential.GaussianExponentialReference

/-!
# Regular names of the original Barnes Taylor product coefficients

At each retained order, the computed modulus retimes the original
finite coefficient reader. The same name approximates any finite
reader with independent admitted prefactor precision and tail cutoff.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorProductCoefficientName

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianBarnesCanonicalExponentTaylorMass (massCap)
open GaussianBarnesCanonicalExponentTaylorCoefficientMassGap (massError)
open GaussianBarnesCanonicalExponentTaylorRetainedCoefficient (cutoff precision prefactorGain)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalTaylorProductCoefficientCauchy
  (exponentialError headCap productCoefficient productError rowError)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (fraction pointCN)
open GaussianExponentialReference (unit_monotone)
open GaussianFastValueCut (exponent query_budget)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianPolynomialExponentialCoefficientVariation (variationBudget)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalSyntheticBounds (natCode natCode_nonnegative)
open RationalArgmin (rationalLE rationalLE_congr)
open RationalArithmetic (multiply)
open RationalSupMetric (numeratorOf)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def integerBudget (R M : PTm n) : PTm n :=
  (numeratorOf (variationBudget (massCap R M) (previous M))).pos

def gain (z R B M e : PTm n) : PTm n :=
  succ e*(headCap z R B*(integerBudget R M*(num 8*succ (previous M))))

def clock (p z R B M e : PTm n) : PTm n := exponent (gain z R B M e) p

def ready (p z R B M e q r : PTm n) : Fm PTm n :=
  le (prefactorGain R*unit (clock p z R B M e)) (unit q) ⋏ le (cutoff (clock p z R B M e) R M) r

def sample (p z R B M e : PTm n) : PTm n :=
  productCoefficient (precision (clock p z R B M e) R) z R B (cutoff (clock p z R B M e) R M) M e

def data (z R B M e : PTm n) : PTm n := pairT z (pairT R (pairT B (pairT M e)))

private def sampleBody : PTm 2 :=
  let x := var 1
  sample (var 0) (fstT x) (fstT (sndT x)) (fstT (sndT (sndT x)))
    (fstT (sndT (sndT (sndT x)))) (sndT (sndT (sndT (sndT x))))

def nameF : PR 2 := PTm.toPR sampleBody

@[simp] theorem subst_gain {l : ℕ} (σ : Fin n → PTm l) (z R B M e : PTm n) :
    Syn.subst σ (gain z R B M e) = gain (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ M)
      (Syn.subst σ e) := by
  simp [gain,integerBudget,headCap,GaussianBarnesCanonicalTaylorProduct.headPolynomial,
    GaussianRationalPolynomialExponentialRecomposition.coefficientBudget,massCap,
    GaussianBarnesCanonicalExponentTaylorMass.coefficientCap,GaussianBarnesCanonicalExponentTaylorMass.linearCap,
    GaussianBarnesCanonicalExponentTaylorMass.squareCap,GaussianBarnesCanonicalExponentTaylorMass.stirlingCap,
    GaussianBarnesCanonicalExponentTaylorMass.quadraticCap,GaussianBarnesCanonicalExponentTaylorMass.halfCap,
    GaussianBarnesCanonicalPrefactor.negativeHalf,GaussianBarnesCanonicalPrefactor.quadraticCoefficientData,
    numeratorOf,pw,one,two]

@[simp] theorem subst_clock {l : ℕ} (σ : Fin n → PTm l) (p z R B M e : PTm n) :
    Syn.subst σ (clock p z R B M e) = clock (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ M) (Syn.subst σ e) := by simp [clock]

private theorem subst_schedule {l : ℕ} (σ : Fin n → PTm l) (p R M : PTm n) :
    Syn.subst σ (prefactorGain R) = prefactorGain (Syn.subst σ R) ∧
      Syn.subst σ (cutoff p R M) = cutoff (Syn.subst σ p) (Syn.subst σ R) (Syn.subst σ M) := by
  simp [prefactorGain,cutoff,GaussianBarnesCanonicalExponentTaylorRetainedCoefficient.tailGain,
    GaussianBarnesCanonicalExponentTaylorCoefficientCauchy.linearGain,GaussianBarnesCanonicalPrefactorLipschitz.halfGain,
    GaussianBarnesCanonicalPrefactor.negativeHalf,one,two]

@[simp] theorem subst_ready {l : ℕ} (σ : Fin n → PTm l) (p z R B M e q r : PTm n) :
    (ready p z R B M e q r).subst σ = ready (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ M) (Syn.subst σ e) (Syn.subst σ q) (Syn.subst σ r) := by
  simp [ready,(subst_schedule σ (clock p z R B M e) R M).1,(subst_schedule σ (clock p z R B M e) R M).2]

@[simp] theorem subst_sample {l : ℕ} (σ : Fin n → PTm l) (p z R B M e : PTm n) :
    Syn.subst σ (sample p z R B M e) = sample (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ M) (Syn.subst σ e) := by
  simp [sample,precision,productCoefficient,GaussianBarnesCanonicalTaylorProduct.polynomial,
    GaussianBarnesCanonicalTaylorProduct.headPolynomial,GaussianBarnesCanonicalTaylorProduct.headDegree,
    (subst_schedule σ (clock p z R B M e) R M).1,(subst_schedule σ (clock p z R B M e) R M).2]

@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (z R B M e : PTm n) :
    Syn.subst σ (data z R B M e) = data (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ M)
      (Syn.subst σ e) := by simp [data]

private theorem scale_fraction (A C D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] multiply (natCode A) (fraction C D) ≐ fraction (A*C) D :=
  (RationalNonnegativePowers.fraction_multiply _ _ _ _ (le_refl one) hD).eqTrans
    (RationalNonnegativePowers.fraction_congr (.eqRefl _) (one_mul _))

private theorem scale_bound (A v C D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] rationalLE v (fraction C D)) :
    Γ ⊢[PRAAx] rationalLE (multiply (natCode A) v) (fraction (A*C) D) :=
  rationalLE_congr (.eqRefl _) (scale_fraction A C D hD)
    (RationalArithmetic.multiply_monotone _ _ _ (natCode_nonnegative _) h)

theorem product_error_bound (p z R B M e : PTm n) :
    Γ ⊢[PRAAx] rationalLE (productError p z R B M e) (fraction (gain z R B M e) (unit p)) := by
  let E := massError p M
  let V := variationBudget (massCap R M) (previous M)
  have positive := GaussianRationalL1.nonnegative_of_representation (Γ := Γ) E _ _ (unit_positive p)
    (GaussianEuclideanDistanceName.fraction_represents _ _ (unit_positive p))
  have cap := RationalArithmetic.multiply_monotone E _ _ positive
    (GaussianGammaFixedCoefficientVariation.rational_integral_upper (Γ := Γ) V)
  have base := rationalLE_congr (RationalAlgebra.multiply_commutative _ _) (RationalAlgebra.multiply_commutative _ _) cap
  have scaled : Γ ⊢[PRAAx] rationalLE (exponentialError p R M (previous M))
      (fraction (integerBudget R M*(num 8*succ (previous M))) (unit p)) :=
    rationalLE_congr (.eqRefl _) (scale_fraction (integerBudget R M) _ _ (unit_positive p)) base
  exact scale_bound (succ e) _ _ _ (unit_positive p)
    (scale_bound (headCap z R B) _ _ _ (unit_positive p) scaled)

theorem finite_gap (p q t z R B r s M e : PTm n) (hz : Γ ⊢[PRAAx] source z R B) (he : Γ ⊢[PRAAx] le e (previous M))
    (hq : Γ ⊢[PRAAx] le (prefactorGain R*unit p) (unit q)) (ht : Γ ⊢[PRAAx] le (prefactorGain R*unit p) (unit t))
    (hr : Γ ⊢[PRAAx] le (cutoff p R M) r) (hs : Γ ⊢[PRAAx] le (cutoff p R M) s) :
    Γ ⊢[PRAAx] distanceBounded (productCoefficient q z R B r M e) (productCoefficient t z R B s M e)
      (gain z R B M e) (unit p) :=
  GaussianCoefficientNormEntries.l1_to_euclidean _ _ _ (unit_positive p)
    (RationalArgmin.transitive
      (GaussianBarnesCanonicalTaylorProductCoefficientCauchy.late_product_gap p q t z R B r s M e hz he hq ht hr hs)
      (product_error_bound p z R B M e))

theorem sample_ready (p z R B M e : PTm n) : Γ ⊢[PRAAx] ready p z R B M e (precision (clock p z R B M e) R)
    (cutoff (clock p z R B M e) R M) :=
  .andI (query_budget _ _) (le_refl _)

theorem ready_weaken (p P z R B M e q r : PTm n) (hp : Γ ⊢[PRAAx] le p P)
    (h : Γ ⊢[PRAAx] ready P z R B M e q r) : Γ ⊢[PRAAx] ready p z R B M e q r := by
  have time : Γ ⊢[PRAAx] le (unit (clock p z R B M e)) (unit (clock P z R B M e)) :=
    unit_monotone (add_le_add_right _ hp)
  exact .andI (le_trans (le_mul_mono (le_refl _) time) h.andE₁)
    (le_trans (le_mul_mono (le_refl _) time) h.andE₂)

theorem ready_gap (p q t z R B r s M e : PTm n) (hz : Γ ⊢[PRAAx] source z R B) (he : Γ ⊢[PRAAx] le e (previous M))
    (hq : Γ ⊢[PRAAx] ready p z R B M e q r) (ht : Γ ⊢[PRAAx] ready p z R B M e t s) :
    Γ ⊢[PRAAx] distanceBounded (productCoefficient q z R B r M e) (productCoefficient t z R B s M e) one (unit p) :=
  distance_radius_mono _ _ _ _ _ _ (unit_positive _) (unit_positive p)
    (le_congr (.eqRefl _) (one_mul _).eqSymm (query_budget (gain z R B M e) p))
    (finite_gap (clock p z R B M e) q t z R B r s M e hz he hq.andE₁ ht.andE₁ hq.andE₂ ht.andE₂)

theorem sample_comparison (p P z R B M e q r : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B) (he : Γ ⊢[PRAAx] le e (previous M)) (h : Γ ⊢[PRAAx] ready P z R B M e q r) :
    Γ ⊢[PRAAx] distanceBounded (sample p z R B M e) (productCoefficient q z R B r M e)
      (unit p+unit P) (unit p*unit P) := by
  refine .orE (le_total p P) ?_ ?_
  · exact distance_radius_mono _ _ _ _ _ _ (unit_positive p) (positive_product _ _ (unit_positive p) (unit_positive P))
      (le_of_eq_add (d := unit p*unit p) (by ipra_ring))
      (ready_gap p _ q z R B _ r M e hz.wk he.wk (sample_ready p z R B M e)
        (ready_weaken p P z R B M e q r Prf.hyp0 h.wk))
  · exact distance_radius_mono _ _ _ _ _ _ (unit_positive P) (positive_product _ _ (unit_positive p) (unit_positive P))
      (le_of_eq_add (d := unit P*unit P) (by ipra_ring))
      (ready_gap P _ q z R B _ r M e hz.wk he.wk
        (ready_weaken P p z R B M e _ _ Prf.hyp0 (sample_ready p z R B M e)) h.wk)

theorem sample_at (p z R B M e : PTm n) : Γ ⊢[PRAAx] ap2 nameF p (data z R B M e) ≐ sample p z R B M e := by
  let x := data z R B M e
  have raw : Γ ⊢[PRAAx] ap2 nameF p x ≐ sample p (fstT x) (fstT (sndT x)) (fstT (sndT (sndT x)))
      (fstT (sndT (sndT (sndT x)))) (sndT (sndT (sndT (sndT x)))) := by
    simpa [nameF,sampleBody,ap2] using toPR_eq (Γ := Γ) sampleBody ![p,x]
  have tail := snd_pair (Γ := Γ) z (pairT R (pairT B (pairT M e)))
  have tail₂ := (congrSnd tail).eqTrans (snd_pair R (pairT B (pairT M e)))
  have tail₃ := (congrSnd tail₂).eqTrans (snd_pair B (pairT M e))
  refine raw.eqTrans ?_
  unfold x data
  ipra_congr (sample (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) with
    [.eqRefl p, fst_pair z _, (congrFst tail).eqTrans (fst_pair R _), (congrFst tail₂).eqTrans (fst_pair B _),
      (congrFst tail₃).eqTrans (fst_pair M e), (congrSnd tail₃).eqTrans (snd_pair M e)]

theorem finite_observation (p P z R B M e q r : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B) (he : Γ ⊢[PRAAx] le e (previous M)) (hr : Γ ⊢[PRAAx] ready P z R B M e q r) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data z R B M e)) (productCoefficient q z R B r M e)
      (unit p+unit P) (unit p*unit P) :=
  distance_congr (sample_at p z R B M e).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (sample_comparison p P z R B M e q r hz he hr)

theorem regular (z R B M e : PTm n) (hz : Γ ⊢[PRAAx] source z R B) (he : Γ ⊢[PRAAx] le e (previous M)) :
    Γ ⊢[PRAAx] pointCN nameF (data z R B M e) := by
  refine .allI (.allI ?_)
  let sh (v : PTm n) := Syn.shift (Syn.shift v)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let p : PTm (n+2) := var 1
  let P : PTm (n+2) := var 0
  have hz' : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hz.shift.shift
  have he' : Δ ⊢[PRAAx] le (sh e) (previous (sh M)) := by simpa [Δ,sh,Fm.shift,Syn.shift] using he.shift.shift
  have h := finite_observation p P (sh z) (sh R) (sh B) (sh M) (sh e) _ _ hz' he'
    (sample_ready P (sh z) (sh R) (sh B) (sh M) (sh e))
  simpa [pointCN,Δ,sh,p,P,Syn.shift,unit,GaussianEuclideanPointDistance.unit] using
    distance_congr (.eqRefl _) (sample_at P (sh z) (sh R) (sh B) (sh M) (sh e)).eqSymm (.eqRefl _) (.eqRefl _) h

theorem finite_rate (P z R B M e q r : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B) (he : Γ ⊢[PRAAx] le e (previous M)) (hr : Γ ⊢[PRAAx] ready P z R B M e q r) :
    Γ ⊢[PRAAx] independentRate nameF constantF (data z R B M e) (productCoefficient q z R B r M e) one (unit P) := by
  refine .allI (.allI ?_)
  let sh (v : PTm n) := Syn.shift (Syn.shift v)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let p : PTm (n+2) := var 1
  let t : PTm (n+2) := var 0
  let u := sh P
  have hz' : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hz.shift.shift
  have he' : Δ ⊢[PRAAx] le (sh e) (previous (sh M)) := by simpa [Δ,sh,Fm.shift,Syn.shift] using he.shift.shift
  have hr' : Δ ⊢[PRAAx] ready u (sh z) (sh R) (sh B) (sh M) (sh e) (sh q) (sh r) := by
    simpa [u,Δ,sh,Fm.shift,Syn.shift] using hr.shift.shift
  have fit : Δ ⊢[PRAAx] le ((unit p+unit u)*rateDenominator (unit u) p t)
      (rateNumerator one (unit u) p t*(unit p*unit u)) :=
    le_of_eq_add (d := unit p*unit p*unit u*unit u) (by unfold rateNumerator rateDenominator; ipra_ring)
  have h := distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive p) (unit_positive u))
    (GaussianNamedInverseRate.denominator_positive _ _ _ (unit_positive u)) fit
    (finite_observation p u (sh z) (sh R) (sh B) (sh M) (sh e) (sh q) (sh r) hz' he' hr')
  simpa [independentRate,Δ,sh,p,t,u,Syn.shift,productCoefficient,GaussianBarnesCanonicalTaylorProduct.polynomial,
    GaussianBarnesCanonicalTaylorProduct.headPolynomial,GaussianBarnesCanonicalTaylorProduct.headDegree] using
    distance_congr (.eqRefl _) (constant_at t _).eqSymm (.eqRefl _) (.eqRefl _) h

theorem actual_Barnes_fixed_order_Taylor_product_coefficient_regular_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((source (var 0) (var 1) (var 2) ⋏ le (var 4) (previous (var 3))) ⟶
      pointCN nameF (data (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (regular _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_Barnes_fixed_order_Taylor_product_coefficient_readback_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (let P := var 0
     let z := var 1
     let R := var 2
     let B := var 3
     let M := var 4
     let e := var 5
     let q := var 6
     let r := var 7
     (source z R B ⋏ le e (previous M)) ⟶ ready P z R B M e q r ⟶
       independentRate nameF constantF (data z R B M e) (productCoefficient q z R B r M e) one (unit P)) :=
  closeUniv 8 (.impI (.impI (finite_rate _ _ _ _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorProductCoefficientName

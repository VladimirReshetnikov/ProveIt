import IPRADerivations.Analysis.Barnes.Taylor.CenteredCharts.GaussianBarnesCanonicalHeadUniformMass
import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.ProductCoefficients.GaussianBarnesCanonicalTaylorProductCoefficientName

/-!
# Disk-uniform rate for the stored Barnes Taylor product coefficients

Use one disk cap for the actual padded-head coefficients, then propagate
the existing finite exponential coefficient gap through the actual
convolution. Its explicit observation schedule depends only on the disk
radius, retained order, queried degree, and requested precision.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorProductUniformGap

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianBarnesCanonicalExponentTaylorCoefficientCauchy (linearGain)
open GaussianBarnesCanonicalExponentTaylorCoefficientMassGap (massError)
open GaussianBarnesCanonicalExponentTaylorMass (massCap)
open GaussianBarnesCanonicalExponentTaylorRetainedCoefficient (prefactorGain tailGain)
open GaussianBarnesCanonicalHeadUniformMass (headCap padded_head_coefficient subst_headCap)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalTaylorProductCoefficientCauchy
  (exponentialError subst_exponentialError productCoefficient late_product_gap_with_head)
open GaussianBarnesCanonicalTaylorProductCoefficientName (integerBudget)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (fraction)
open GaussianExponentialReference (unit_monotone)
open GaussianFastValueCut (exponent query_budget)
open GaussianPolynomialExponentialCoefficientVariation (variationBudget)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalL1 (qL1)
open GaussianRationalMetric (qsub distanceBounded)
open GaussianRationalSyntheticBounds (natCode)
open RationalNonnegativePowers (nat_mul_fraction nat_mul_fraction_bound)
open RationalArgmin (rationalLE rationalLE_congr)
open RationalArithmetic (multiply)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def rowError (p R M : PTm n) : PTm n :=
  multiply (natCode (headCap R)) (exponentialError p R M (previous M))

def productError (p R M e : PTm n) : PTm n := multiply (natCode (succ e)) (rowError p R M)

def gain (R M e : PTm n) : PTm n :=
  succ e*(headCap R*(integerBudget R M*(num 8*succ (previous M))))

def clock (p R M e : PTm n) : PTm n := exponent (gain R M e) p

def cutoff (p R M e : PTm n) : PTm n :=
  GaussianBarnesCanonicalExponentTaylorRetainedCoefficient.cutoff (clock p R M e) R M

def precision (p R M e : PTm n) : PTm n :=
  GaussianBarnesCanonicalExponentTaylorRetainedCoefficient.precision (clock p R M e) R

def ready (p R M e q r : PTm n) : Fm PTm n :=
  le (prefactorGain R*unit (clock p R M e)) (unit q) ⋏ le (cutoff p R M e) r

@[simp] private theorem subst_prefactorGain {l : ℕ} (σ : Fin n → PTm l) (R : PTm n) :
    Syn.subst σ (prefactorGain R) = prefactorGain (Syn.subst σ R) := by
  simp [prefactorGain,linearGain,GaussianBarnesCanonicalPrefactorLipschitz.halfGain,
    GaussianBarnesCanonicalPrefactor.negativeHalf,one,two]

@[simp] private theorem subst_integerBudget {l : ℕ} (σ : Fin n → PTm l) (R M : PTm n) :
    Syn.subst σ (integerBudget R M) = integerBudget (Syn.subst σ R) (Syn.subst σ M) := by
  simp [integerBudget,massCap,GaussianBarnesCanonicalExponentTaylorMass.coefficientCap,
    GaussianBarnesCanonicalExponentTaylorMass.linearCap,GaussianBarnesCanonicalExponentTaylorMass.squareCap,
    GaussianBarnesCanonicalExponentTaylorMass.stirlingCap,GaussianBarnesCanonicalExponentTaylorMass.quadraticCap,
    GaussianBarnesCanonicalExponentTaylorMass.halfCap,GaussianBarnesCanonicalPrefactor.quadraticCoefficientData,
    GaussianBarnesCanonicalPrefactor.negativeHalf,RationalSupMetric.numeratorOf,pw,one,two]

@[simp] theorem subst_rowError {l : ℕ} (σ : Fin n → PTm l) (p R M : PTm n) :
    Syn.subst σ (rowError p R M) = rowError (Syn.subst σ p) (Syn.subst σ R) (Syn.subst σ M) := by
  simp [rowError]

@[simp] theorem subst_gain {l : ℕ} (σ : Fin n → PTm l) (R M e : PTm n) :
    Syn.subst σ (gain R M e) = gain (Syn.subst σ R) (Syn.subst σ M) (Syn.subst σ e) := by simp [gain]

@[simp] theorem subst_clock {l : ℕ} (σ : Fin n → PTm l) (p R M e : PTm n) :
    Syn.subst σ (clock p R M e) = clock (Syn.subst σ p) (Syn.subst σ R) (Syn.subst σ M) (Syn.subst σ e) := by simp [clock]

@[simp] theorem subst_cutoff {l : ℕ} (σ : Fin n → PTm l) (p R M e : PTm n) :
    Syn.subst σ (cutoff p R M e) = cutoff (Syn.subst σ p) (Syn.subst σ R) (Syn.subst σ M) (Syn.subst σ e) := by
  simp [cutoff,GaussianBarnesCanonicalExponentTaylorRetainedCoefficient.cutoff,tailGain,pw,two]

@[simp] theorem subst_precision {l : ℕ} (σ : Fin n → PTm l) (p R M e : PTm n) :
    Syn.subst σ (precision p R M e) = precision (Syn.subst σ p) (Syn.subst σ R) (Syn.subst σ M) (Syn.subst σ e) := by
  simp [precision,GaussianBarnesCanonicalExponentTaylorRetainedCoefficient.precision]

@[simp] theorem subst_ready {l : ℕ} (σ : Fin n → PTm l) (p R M e q r : PTm n) :
    (ready p R M e q r).subst σ = ready (Syn.subst σ p) (Syn.subst σ R) (Syn.subst σ M) (Syn.subst σ e)
      (Syn.subst σ q) (Syn.subst σ r) := by simp [ready]

theorem late_product_gap (p q t z R B r s M e : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B) (he : Γ ⊢[PRAAx] le e (previous M))
    (hq : Γ ⊢[PRAAx] le (prefactorGain R*unit p) (unit q)) (ht : Γ ⊢[PRAAx] le (prefactorGain R*unit p) (unit t))
    (hr : Γ ⊢[PRAAx] le (GaussianBarnesCanonicalExponentTaylorRetainedCoefficient.cutoff p R M) r)
    (hs : Γ ⊢[PRAAx] le (GaussianBarnesCanonicalExponentTaylorRetainedCoefficient.cutoff p R M) s) : Γ ⊢[PRAAx]
    rationalLE (qL1 (qsub (productCoefficient q z R B r M e) (productCoefficient t z R B s M e))) (productError p R M e) := by
  refine late_product_gap_with_head p q t z R B r s M e (headCap R) hz he hq ht hr hs ?_
  intro sh Δ
  have source' : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using hz.shift.wk
  simpa only [Δ,sh,Syn.shift,subst_headCap,GaussianBarnesCanonicalTaylorProductCoefficientCauchy.paddedHead,
    GaussianBarnesCanonicalTaylorProductCoefficientCauchy.paddedDegree,GaussianBarnesCanonicalTaylorProduct.headPolynomial,
    GaussianBarnesCanonicalTaylorProduct.headDegree] using
    padded_head_coefficient (sh z) (sh R) (sh B) (sh e) (var 0) source'

theorem product_error_bound (p R M e : PTm n) :
    Γ ⊢[PRAAx] rationalLE (productError p R M e) (fraction (gain R M e) (unit p)) := by
  let E := massError p M
  let V := variationBudget (massCap R M) (previous M)
  have positive := GaussianRationalL1.nonnegative_of_representation (Γ := Γ) E _ _ (unit_positive p)
    (GaussianEuclideanDistanceName.fraction_represents _ _ (unit_positive p))
  have cap := RationalArithmetic.multiply_monotone E _ _ positive
    (GaussianGammaFixedCoefficientVariation.rational_integral_upper (Γ := Γ) V)
  have base := rationalLE_congr (RationalAlgebra.multiply_commutative _ _) (RationalAlgebra.multiply_commutative _ _) cap
  have scaled : Γ ⊢[PRAAx] rationalLE (exponentialError p R M (previous M))
      (fraction (integerBudget R M*(num 8*succ (previous M))) (unit p)) :=
    rationalLE_congr (.eqRefl _) (nat_mul_fraction (unit_positive p) (.eqRefl _)) base
  exact nat_mul_fraction_bound (succ e) (unit_positive p) (nat_mul_fraction_bound (headCap R) (unit_positive p) scaled)

theorem finite_gap (p q t z R B r s M e : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B) (he : Γ ⊢[PRAAx] le e (previous M))
    (hq : Γ ⊢[PRAAx] le (prefactorGain R*unit p) (unit q)) (ht : Γ ⊢[PRAAx] le (prefactorGain R*unit p) (unit t))
    (hr : Γ ⊢[PRAAx] le (GaussianBarnesCanonicalExponentTaylorRetainedCoefficient.cutoff p R M) r)
    (hs : Γ ⊢[PRAAx] le (GaussianBarnesCanonicalExponentTaylorRetainedCoefficient.cutoff p R M) s) : Γ ⊢[PRAAx]
    distanceBounded (productCoefficient q z R B r M e) (productCoefficient t z R B s M e) (gain R M e) (unit p) :=
  GaussianCoefficientNormEntries.l1_to_euclidean _ _ _ (unit_positive p)
    (RationalArgmin.transitive (late_product_gap p q t z R B r s M e hz he hq ht hr hs) (product_error_bound p R M e))

theorem sample_ready (p R M e : PTm n) : Γ ⊢[PRAAx] ready p R M e (precision p R M e) (cutoff p R M e) :=
  .andI (query_budget _ _) (le_refl _)

theorem ready_weaken (p P R M e q r : PTm n) (hp : Γ ⊢[PRAAx] le p P)
    (h : Γ ⊢[PRAAx] ready P R M e q r) : Γ ⊢[PRAAx] ready p R M e q r := by
  have time : Γ ⊢[PRAAx] le (unit (clock p R M e)) (unit (clock P R M e)) := unit_monotone (add_le_add_right _ hp)
  exact .andI (le_trans (le_mul_mono (le_refl _) time) h.andE₁) (le_trans (le_mul_mono (le_refl _) time) h.andE₂)

theorem ready_gap (p q t z R B r s M e : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B) (he : Γ ⊢[PRAAx] le e (previous M))
    (hq : Γ ⊢[PRAAx] ready p R M e q r) (ht : Γ ⊢[PRAAx] ready p R M e t s) : Γ ⊢[PRAAx]
    distanceBounded (productCoefficient q z R B r M e) (productCoefficient t z R B s M e) one (unit p) :=
  distance_radius_mono _ _ _ _ _ _ (unit_positive _) (unit_positive p)
    (le_congr (.eqRefl _) (one_mul _).eqSymm (query_budget (gain R M e) p))
    (finite_gap (clock p R M e) q t z R B r s M e hz he hq.andE₁ ht.andE₁ hq.andE₂ ht.andE₂)

theorem actual_Barnes_disk_uniform_Taylor_coefficient_gap_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (let p := var 0
     let q := var 1
     let t := var 2
     let z := var 3
     let R := var 4
     let B := var 5
     let r := var 6
     let s := var 7
     let M := var 8
     let e := var 9
     (source z R B ⋏ (le e (previous M) ⋏ (ready p R M e q r ⋏ ready p R M e t s))) ⟶
       distanceBounded (productCoefficient q z R B r M e) (productCoefficient t z R B s M e) one (unit p)) :=
  closeUniv 10 (.impI (ready_gap (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9)
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorProductUniformGap

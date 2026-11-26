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
  (exponential exponentialError exponential_gap exponentPrefix paddedHead paddedDegree productCoefficient
    coefficient_reader subst_exponentPrefix subst_paddedHead subst_paddedDegree)
open GaussianBarnesCanonicalTaylorProductCoefficientName (integerBudget)
open GaussianCoefficientL1 (qL1_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (fraction)
open GaussianExponentialReference (unit_monotone)
open GaussianFastValueCut (exponent query_budget)
open GaussianFiniteSumL1Variation (termsError)
open GaussianPolynomialExponentialCoefficientVariation (variationBudget)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalL1 (qL1 qL1_nonnegative)
open GaussianRationalLowCoefficientConvolution (exponentCoefficient exponent_inside term termBody term_at)
open GaussianRationalMetric (qsub distanceBounded)
open GaussianRationalSyntheticBounds (natCode natCode_nonnegative)
open GaussianRationalSyntheticDivision (qsub_congr)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
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
  simp [rowError,exponentialError,massError,massCap,GaussianBarnesCanonicalExponentTaylorMass.coefficientCap,
    GaussianBarnesCanonicalExponentTaylorMass.linearCap,GaussianBarnesCanonicalExponentTaylorMass.squareCap,
    GaussianBarnesCanonicalExponentTaylorMass.stirlingCap,GaussianBarnesCanonicalExponentTaylorMass.quadraticCap,
    GaussianBarnesCanonicalExponentTaylorMass.halfCap,GaussianBarnesCanonicalPrefactor.quadraticCoefficientData,
    GaussianBarnesCanonicalPrefactor.negativeHalf,pw,one,two]

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

private theorem prefix_reader (q z R B r M e : PTm n) (he : Γ ⊢[PRAAx] le e (previous M)) :
    let N := previous M
    Γ ⊢[PRAAx] entry (exponentPrefix q z R B r M) (monus N e) ≐
      exponentCoefficient (exponential q z R B r M N) (N*N) e := by
  let N := previous M
  have hm : Γ ⊢[PRAAx] le N (N*N) :=
    le_congr (one_mul N) (.eqRefl _) (mul_le_mul_right N (zero_lt_succ (succ M)))
  exact (GaussianPolynomialLowPrefix.original_reader (exponential q z R B r M N) (N*N) N e he).eqTrans
    (exponent_inside _ _ _ (le_trans he hm)).eqSymm

private theorem row_gap (p q t z R B r s M e i : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B) (he : Γ ⊢[PRAAx] le e (previous M))
    (hq : Γ ⊢[PRAAx] le (prefactorGain R*unit p) (unit q)) (ht : Γ ⊢[PRAAx] le (prefactorGain R*unit p) (unit t))
    (hr : Γ ⊢[PRAAx] le (GaussianBarnesCanonicalExponentTaylorRetainedCoefficient.cutoff p R M) r)
    (hs : Γ ⊢[PRAAx] le (GaussianBarnesCanonicalExponentTaylorRetainedCoefficient.cutoff p R M) s) : Γ ⊢[PRAAx]
    rationalLE (qL1 (qsub (term (paddedHead z R B e) (exponentPrefix q z R B r M) (paddedDegree R e) (previous M) e i)
      (term (paddedHead z R B e) (exponentPrefix t z R B s M) (paddedDegree R e) (previous M) e i))) (rowError p R M) := by
  let N := previous M
  let j := monus e i
  let a := entry (paddedHead z R B e) (monus (paddedDegree R e) i)
  let b := entry (exponentPrefix q z R B r M) (monus N j)
  let c := entry (exponentPrefix t z R B s M) (monus N j)
  have hj := le_trans (GaussianRationalMonicReconstruction.monus_le_left e i) he
  have codes := qsub_congr (prefix_reader q z R B r M j hj) (prefix_reader t z R B s M j hj)
  have expGap : Γ ⊢[PRAAx] rationalLE (qL1 (qsub b c)) (exponentialError p R M N) :=
    rationalLE_congr (qL1_congr codes).eqSymm (.eqRefl _) (exponential_gap p q t z R B r s M N j hz hj hq ht hr hs)
  have head : Γ ⊢[PRAAx] rationalLE (qL1 a) (natCode (headCap R)) := padded_head_coefficient z R B e i hz
  have product := RationalArgmin.transitive (GaussianRationalL1Algebra.qL1_multiply (Γ := Γ) a (qsub b c))
    (GaussianFiniteExponentialWeightedNorm.multiply_bounds _ _ _ _ (qL1_nonnegative _) (natCode_nonnegative _) head expGap)
  exact rationalLE_congr (qL1_congr (GaussianPolynomialCoefficientDifferences.scalar_scaled_difference a b c)).eqSymm
    (.eqRefl _) product

theorem late_product_gap (p q t z R B r s M e : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B) (he : Γ ⊢[PRAAx] le e (previous M))
    (hq : Γ ⊢[PRAAx] le (prefactorGain R*unit p) (unit q)) (ht : Γ ⊢[PRAAx] le (prefactorGain R*unit p) (unit t))
    (hr : Γ ⊢[PRAAx] le (GaussianBarnesCanonicalExponentTaylorRetainedCoefficient.cutoff p R M) r)
    (hs : Γ ⊢[PRAAx] le (GaussianBarnesCanonicalExponentTaylorRetainedCoefficient.cutoff p R M) s) : Γ ⊢[PRAAx]
    rationalLE (qL1 (qsub (productCoefficient q z R B r M e) (productCoefficient t z R B s M e))) (productError p R M e) := by
  let P := paddedHead z R B e
  let K := paddedDegree R e
  let N := previous M
  let x := GaussianRationalLowCoefficientConvolution.data P (exponentPrefix q z R B r M) K N e
  let y := GaussianRationalLowCoefficientConvolution.data P (exponentPrefix t z R B s M) K N e
  have rows : Γ ⊢[PRAAx] termsError termBody termBody (succ e) x y (rowError p R M) := by
    refine .allI (.impI ?_)
    let a (u : PTm n) := Syn.shift u
    let Δ := lt (var 0) (succ (a e)) :: Γ.map Fm.shift
    have hz' : Δ ⊢[PRAAx] source (a z) (a R) (a B) := by simpa [Δ,a,Fm.shift,Syn.shift] using hz.shift.wk
    have he' : Δ ⊢[PRAAx] le (a e) (previous (a M)) := by simpa [Δ,a,Fm.shift,Syn.shift] using he.shift.wk
    have clock_budget {u : PTm n} (h : Γ ⊢[PRAAx] le (prefactorGain R*unit p) (unit u)) :
        Δ ⊢[PRAAx] le (prefactorGain (a R)*unit (a p)) (unit (a u)) := by
      simpa [Δ,a,Fm.shift,Syn.shift] using h.shift.wk
    let cut {k : ℕ} (p R M : PTm k) := GaussianBarnesCanonicalExponentTaylorRetainedCoefficient.cutoff p R M
    have cutoff_budget {u : PTm n} (h : Γ ⊢[PRAAx] le (cut p R M) u) : Δ ⊢[PRAAx] le (cut (a p) (a R) (a M)) (a u) := by
      simpa [Δ,a,Fm.shift,Syn.shift,cut,GaussianBarnesCanonicalExponentTaylorRetainedCoefficient.cutoff,tailGain,pw,two] using h.shift.wk
    have codes := qsub_congr (Γ := Δ)
      (term_at (paddedHead (a z) (a R) (a B) (a e)) (exponentPrefix (a q) (a z) (a R) (a B) (a r) (a M))
        (paddedDegree (a R) (a e)) (previous (a M)) (a e) (var 0))
      (term_at (paddedHead (a z) (a R) (a B) (a e)) (exponentPrefix (a t) (a z) (a R) (a B) (a s) (a M))
        (paddedDegree (a R) (a e)) (previous (a M)) (a e) (var 0))
    simpa only [termsError,Δ,a,P,K,N,x,y,Syn.shift,GaussianRationalLowCoefficientConvolution.subst_data,
      subst_exponentPrefix,subst_paddedHead,subst_paddedDegree,GaussianBarnesCanonicalHigherRows.subst_previous,subst_rowError,
      ConciseIPRA.PTm.subst_succ] using rationalLE_congr (qL1_congr codes).eqSymm (.eqRefl _)
        (row_gap (a p) (a q) (a t) (a z) (a R) (a B) (a r) (a s) (a M) (a e) (var 0)
          hz' he' (clock_budget hq) (clock_budget ht) (cutoff_budget hr) (cutoff_budget hs))
  exact rationalLE_congr
    (qL1_congr (qsub_congr (coefficient_reader q z R B r M e he) (coefficient_reader t z R B s M e he))).eqSymm
    (.eqRefl _) (GaussianFiniteSumL1Variation.sum_error termBody termBody (succ e) x y (rowError p R M) rows)

private theorem scale_fraction (A C D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] multiply (natCode A) (fraction C D) ≐ fraction (A*C) D :=
  (RationalNonnegativePowers.fraction_multiply _ _ _ _ (le_refl one) hD).eqTrans
    (RationalNonnegativePowers.fraction_congr (.eqRefl _) (one_mul _))

private theorem scale_bound (A v C D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] rationalLE v (fraction C D)) : Γ ⊢[PRAAx] rationalLE (multiply (natCode A) v) (fraction (A*C) D) :=
  rationalLE_congr (.eqRefl _) (scale_fraction A C D hD)
    (RationalArithmetic.multiply_monotone _ _ _ (natCode_nonnegative _) h)

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
    rationalLE_congr (.eqRefl _) (scale_fraction (integerBudget R M) _ _ (unit_positive p)) base
  exact scale_bound (succ e) _ _ _ (unit_positive p) (scale_bound (headCap R) _ _ _ (unit_positive p) scaled)

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

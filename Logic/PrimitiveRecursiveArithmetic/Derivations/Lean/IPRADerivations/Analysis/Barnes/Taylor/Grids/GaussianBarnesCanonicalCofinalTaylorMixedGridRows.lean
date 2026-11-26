import IPRADerivations.Analysis.Barnes.Taylor.Grids.GaussianBarnesCanonicalMixedTaylorGridGeometry
import IPRADerivations.Analysis.Barnes.Taylor.Grids.GaussianBarnesCanonicalFiniteTaylorDiskGridLimit

/-!
# A shared Taylor approximation for the two cofinal Barnes grids

An exact coded displacement determines each original Barnes value row.
The same polynomial and scalar observation work for both orientations,
with an explicit budget for the product normalization.
-/

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCofinalTaylorMixedGridRows

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (add bounded bounded_mono scale)
open GaussianBarnesCanonicalCofinalTaylorGridObservations (cofinalGrid cofinal_at tailCutoff)
open GaussianBarnesCanonicalFiniteCentralExponential (finiteNameF finiteData finite_regular)
open GaussianBarnesCanonicalFiniteTaylorDiskGridLimit (analyticGain clockGain)
open GaussianBarnesCanonicalFiniteTaylorGrid (polynomial)
open GaussianBarnesCanonicalFiniteTaylorGridObservations (cap cost_le_cap scaledPolynomial)
open GaussianBarnesCanonicalFiniteTaylorNormalizedGridBudget (rowNumeratorWithGains rowDenominator row_denominator_positive)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianBarnesCanonicalMixedTaylorGridGeometry
  (admitted_node forward_bound backward_bound forward_point backward_point backward_data backwardDisplacement)
open GaussianBarnesCanonicalWeightedTaylorBallSource (stepDivisor stepDivisor_positive)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (multiplyData multiplyModulus)
open GaussianNamedInverseRate (rate_at rateNumerator rateDenominator denominator_positive)
open GaussianPolynomialForwardDifferenceGrid (point samples sample_lookup)
open GaussianPolynomialForwardDifferenceGridError (rowBound)
open GaussianRationalCoefficientScaling (scaled evaluation_linearity)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (evaluate ofGaussian positive_product qmul qzero)
open GaussianRationalMetric (distanceBounded qnegative)
open GaussianRationalSyntheticDivision (qmul_congr)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open ConciseIPRA.PTm (succ zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "G" => GaussianBarnesCanonicalValue.nameF
local notation "V" => GaussianBarnesCanonicalValue.prefixF
local notation "C" => GaussianBarnesCanonicalFiniteWeightedTaylorValue.nameF
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "gneg" => ComplexLogarithmRemainder.neg

def polynomialGrid (t q z R B H r M x k : PTm n) : PTm n :=
  samples (scaledPolynomial t q z R B H r M (previous M)) (succ (previous M)) x k

def productCap (q z R B H r M x k : PTm n) : PTm n :=
  cap (finiteData z (R+one) B r) (samples (polynomial q z R B H r M (previous M)) (succ (previous M)) x k) (previous M)

def rowNumerator (t q z R B H r M x k : PTm n) : PTm n :=
  rowNumeratorWithGains q t B H M (num 4+productCap q z R B H r M x k) (analyticGain R M) (clockGain R+one)

@[simp] theorem subst_polynomialGrid {m : ℕ} (σ : Fin n → PTm m) (t q z R B H r M x k : PTm n) :
    Syn.subst σ (polynomialGrid t q z R B H r M x k) = polynomialGrid (Syn.subst σ t) (Syn.subst σ q)
      (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ H) (Syn.subst σ r) (Syn.subst σ M)
      (Syn.subst σ x) (Syn.subst σ k) := by simp [polynomialGrid]

@[simp] private theorem subst_productCap {m : ℕ} (σ : Fin n → PTm m) (q z R B H r M x k : PTm n) :
    Syn.subst σ (productCap q z R B H r M x k) = productCap (Syn.subst σ q) (Syn.subst σ z)
      (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ H) (Syn.subst σ r) (Syn.subst σ M)
      (Syn.subst σ x) (Syn.subst σ k) := by
  simp [productCap,cap,finiteData,GaussianBarnesCanonicalFiniteCentralExponential.prefixExpData,
    GaussianBarnesCanonicalSingleExponential.prefixData,GaussianBarnesCanonicalSingleExponential.prefactorExponentData,
    GaussianGammaFiniteApproximantName.exponentialInputData,polynomial,GaussianBarnesCanonicalFiniteWeightedTaylorValue.polynomial,
    GaussianBarnesCanonicalTaylorProduct.polynomial,GaussianBarnesCanonicalTaylorProduct.headPolynomial,
    GaussianBarnesCanonicalTaylorProduct.headDegree,GaussianBarnesCanonicalHeadPolynomial.degree,
    GaussianBarnesCanonicalExponentTaylorBallSchedule.precision,GaussianBarnesCanonicalExponentTaylorBallSchedule.uniformCost,
    GaussianBarnesCanonicalExponentTaylorBallSchedule.stepClockCap,GaussianBarnesCanonicalExponentTaylorBallSchedule.polynomialClockCap,
    GaussianBarnesCanonicalExponentTaylorBallSchedule.squareClockCap,GaussianBarnesCanonicalExponentTaylorBallSchedule.squareCap,
    GaussianBarnesCanonicalPrefactor.negativeHalf,GaussianBarnesCanonicalPrefactor.quadraticCoefficientData,one,two]

@[simp] private theorem subst_prefactorRadius {m : ℕ} (σ : Fin n → PTm m) (R : PTm n) :
    Syn.subst σ (GaussianBarnesCanonicalDiskBound.prefactorRadius R) =
      GaussianBarnesCanonicalDiskBound.prefactorRadius (Syn.subst σ R) := by
  let expression {l : ℕ} (v : PTm l) : PTm l :=
    let a := GaussianNameBounds.U GaussianStirlingConstant.nameF (GaussianStirlingConstant.nameData zero)
    let b := GaussianNameBounds.U GaussianGammaCanonicalExponent.gammaF zero
    (two*(v*a)+two)+(two*(v+(v*v)*(one+b))+two)
  change Syn.subst σ (expression R) = expression (Syn.subst σ R)
  simp [expression,one,two]

@[simp] theorem subst_rowNumerator {m : ℕ} (σ : Fin n → PTm m) (t q z R B H r M x k : PTm n) :
    Syn.subst σ (rowNumerator t q z R B H r M x k) = rowNumerator (Syn.subst σ t) (Syn.subst σ q)
      (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ H) (Syn.subst σ r) (Syn.subst σ M)
      (Syn.subst σ x) (Syn.subst σ k) := by simp [rowNumerator,analyticGain,clockGain,GaussianBarnesCanonicalFiniteCentralDiskBound.cap,GaussianBarnesCanonicalCentralUniformBound.prefixCap,
      GaussianBarnesCanonicalCentralUniformBound.prefixArgumentCap,GaussianBarnesCanonicalCentralUniformBound.correctionCap,
      GaussianBarnesCanonicalFactor.exponentRadius,one,two]

theorem sufficient_disk_width (R B H : PTm n) (hs : Γ ⊢[PRAAx] le (stepDivisor R*H) B) :
    Γ ⊢[PRAAx] le H B :=
  le_trans (le_congr (one_mul H) (.eqRefl _) (mul_le_mul_right H (stepDivisor_positive R))) hs

private theorem row_chain (U X W A B D t q C₀ : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hD' : Γ ⊢[PRAAx] le one (B*unit q))
    (hA : Γ ⊢[PRAAx] le (A*(B*unit q)) (C₀*D))
    (h₁ : Γ ⊢[PRAAx] distanceBounded U X (rateNumerator one (unit q) t t) (rateDenominator (unit q) t t))
    (h₂ : Γ ⊢[PRAAx] distanceBounded X W (rateNumerator A D t t) (rateDenominator D t t)) :
    Γ ⊢[PRAAx] distanceBounded U W ((B+C₀)*unit t+(B*unit q)*num 4) ((B*unit q)*unit t) := by
  let Q := unit q
  let T := unit t
  let F := B*Q
  let E := F*T
  have hE : Γ ⊢[PRAAx] le one E := positive_product _ _ hD' (unit_positive t)
  have u : Γ ⊢[PRAAx] distanceBounded U X (B*T+F*two) E :=
    distance_radius_mono _ _ _ _ _ _ (denominator_positive _ _ _ (unit_positive q)) hE
      (le_of_eq_add (d := zero) (by dsimp only [E,F,Q,T,rateNumerator,rateDenominator]; ipra_ring)) h₁
  have v : Γ ⊢[PRAAx] distanceBounded X W (C₀*T+F*two) E :=
    distance_radius_mono _ _ _ _ _ _ (denominator_positive _ _ _ hD) hE
      (by
        dsimp only [E,F,rateNumerator,rateDenominator,T,Q] at *
        ipra_le 𝔞(T)*𝔞(T)*𝔞(T)*sl hA) h₂
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [F,Q,T]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hE u v)

theorem node_error (t q z δ R B H r M x k j : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B)
    (hδ : Γ ⊢[PRAAx] bounded δ (previous M*H))
    (hs : Γ ⊢[PRAAx] le (stepDivisor R*(previous M*H)) B)
    (hr : Γ ⊢[PRAAx] le (tailCutoff q R) r)
    (hj : Γ ⊢[PRAAx] lt j (succ (previous M)))
    (hp : Γ ⊢[PRAAx] ofGaussian δ B ≐ point x k j) :
    Γ ⊢[PRAAx] distanceBounded (ap2 G t (GaussianBarnesCanonicalValue.data (add z δ) (R+one) B))
      (entry (polynomialGrid t q z R B H r M x k) j)
      (rowNumerator t q z R B H r M x k) (rowDenominator q t B M) := by
  let S := R+one
  let N := previous M
  let P := polynomial q z R B H r M N
  let d := finiteData z S B r
  let c := ap2 finiteNameF t d
  let α := samples P (succ N) x k
  let v := entry α j
  let y := point x k j
  let L := multiplyModulus finiteNameF constantF d v+one
  let K := productCap q z R B H r M x k
  let A := GaussianBarnesCanonicalFiniteWeightedTaylorUniformValue.numerator q S B (N*H) M
  let D := GaussianBarnesCanonicalFiniteWeightedTaylorValue.denominator q S B M
  let D' := GaussianBarnesCanonicalFiniteTaylorGridBudget.denominator q B M
  let U := unit t
  let Q := unit q
  let J := pw B (succ N)
  let A' := GaussianBarnesCanonicalFiniteTaylorGridBudget.numeratorWithCaps q S B H M
    (GaussianBarnesCanonicalHeadUniformMass.headCap S) (GaussianBarnesCanonicalFiniteCentralDiskBound.cap S)
  have z' : Γ ⊢[PRAAx] source z S B :=
    .andI hz.andE₁ (bounded_mono hz.andE₂ (le_of_eq_add (d := B) (by dsimp only [S]; ipra_ring)))
  have node := admitted_node z δ R B (N*H) hz hδ (sufficient_disk_width R B (N*H) hs)
  have guard := le_trans hr (le_add_left r (initial S))
  have tail := GaussianBarnesCanonicalUniformCutoff.uniform_rate (add z δ) S B q (initial S+r) node guard
  have earlier := GaussianNamedRateComposition.symmetric _ _ _ _ _ _ (unit_positive q) tail
  have step₁ := rate_at _ _ _ _ _ _ t t earlier
  have finite := GaussianBarnesCanonicalFiniteWeightedTaylorUniformValue.shared_rate q z δ R B (N*H) r M hz hδ hs
  have step₂ := rate_at _ _ _ _ _ _ t t finite
  have cmp : Γ ⊢[PRAAx] le (A*D') (A'*D) :=
    GaussianBarnesCanonicalFiniteTaylorGridBudget.radius_comparison_with_caps q S B H M _ _
  have pos : Γ ⊢[PRAAx] le one D' :=
    GaussianBarnesCanonicalFiniteTaylorGridBudget.denominator_positive q B M hz.andE₁
  have hd : Γ ⊢[PRAAx] le one D :=
    GaussianBarnesCanonicalFiniteTaylorGrid.denominator_positive q R B M hz.andE₁
  have hsamp : Γ ⊢[PRAAx] evaluate P (ofGaussian δ B) ≐ v :=
    (GaussianRationalReconstruction.evaluate_congr (.eqRefl P) hp).eqTrans
      (sample_lookup P (succ N) x k j hj).eqSymm
  have pd : Γ ⊢[PRAAx] GaussianBarnesCanonicalFiniteWeightedTaylorValue.data q z δ S B (N*H) r M ≐
      multiplyData finiteNameF constantF d v := by
    ipra_congr (multiplyData finiteNameF constantF (var 0) (var 1) : PTm 2) with [.eqRefl d, hsamp]
      using [GaussianBarnesCanonicalFiniteWeightedTaylorValue.data, P, polynomial, d, S, N]
  have product := GaussianNameRingLaws.multiply_sample_error finiteNameF constantF d v t
    (finite_regular z S B r z') (constant_regular v)
  have eval : Γ ⊢[PRAAx] qmul c (ap2 constantF t v) ≐ entry (polynomialGrid t q z R B H r M x k) j :=
    (qmul_congr (.eqRefl c) ((constant_at t v).eqTrans (sample_lookup P (succ N) x k j hj))).eqTrans
      ((evaluation_linearity P c y).eqSymm.eqTrans (sample_lookup (scaled P c) (succ N) x k j hj).eqSymm)
  have step₃ := distance_congr (congrAp2 C (.eqRefl t) pd).eqSymm eval (.eqRefl _) (.eqRefl _) product
  have Epos := row_denominator_positive q t B M hz.andE₁
  have bound : Γ ⊢[PRAAx] le L K := cost_le_cap d α N j hj
  have hleft : Γ ⊢[PRAAx] L*(D'*U) ≐ L*rowDenominator q t B M := .eqRefl _
  have hright : Γ ⊢[PRAAx] K*(D'*U) ≐ (D'*K)*U := by ipra_ring
  have paid := distance_radius_mono _ _ _ _ (D'*K) (rowDenominator q t B M) (unit_positive t) Epos
    (le_congr hleft hright (mul_le_mul_right (D'*U) bound)) step₃
  have sum := distance_triangle_same _ _ _ _ _ _ Epos (row_chain _ _ _ A J D t q A' hd pos cmp step₁ step₂) paid
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by dsimp only [rowNumerator,rowNumeratorWithGains,A',D',analyticGain,clockGain,
      GaussianBarnesCanonicalFiniteTaylorGridBudget.numeratorWithCaps,
      GaussianBarnesCanonicalFiniteTaylorGridBudget.denominator,J,Q,U,K]; ipra_ring)
    (.eqRefl _) sum

theorem forward_rows (t q z h R B H r M : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hh : Γ ⊢[PRAAx] bounded h H)
    (hs : Γ ⊢[PRAAx] le (stepDivisor R*(previous M*(two*H))) B)
    (hr : Γ ⊢[PRAAx] le (tailCutoff q R) r) :
    Γ ⊢[PRAAx] rowBound (cofinalGrid t z h R B (previous M))
      (polynomialGrid t q z R B (two*H) r M qzero (ofGaussian h B)) (succ (previous M))
      (rowNumerator t q z R B (two*H) r M qzero (ofGaussian h B)) (rowDenominator q t B M) := by
  refine .allI (.impI ?_)
  let a (v : PTm n) := Syn.shift v
  let j : PTm (n+1) := var 0
  let N := previous (a M)
  let Δ := lt j (succ N) :: Γ.map Fm.shift
  have z' : Δ ⊢[PRAAx] source (a z) (a R) (a B) := by simpa [Δ,a,Fm.shift,Syn.shift] using hz.shift.wk
  have h' : Δ ⊢[PRAAx] bounded (a h) (a H) := by simpa [Δ,a,Fm.shift,Syn.shift] using hh.shift.wk
  have s' : Δ ⊢[PRAAx] le (stepDivisor (a R)*(N*(two*a H))) (a B) := by
    simpa [Δ,a,N,Fm.shift,Syn.shift,two] using hs.shift.wk
  have r' : Δ ⊢[PRAAx] le (tailCutoff (a q) (a R)) (a r) := by
    simpa [Δ,a,Fm.shift,Syn.shift] using hr.shift.wk
  have hj : Δ ⊢[PRAAx] lt j (succ N) := Prf.hyp0
  have row := node_error (a t) (a q) (a z) (scale j (a h)) (a R) (a B) (two*a H) (a r) (a M) qzero
    (ofGaussian (a h) (a B)) j z' (forward_bound _ _ _ _ h' (Common.le_of_lt_succ hj))
    s' r' hj (forward_point _ _ _ z'.andE₁)
  have read := cofinal_at (a t) (a z) (a h) (a R) (a B) N j hj
  simpa [Δ,a,j,N,Syn.shift,one,two] using distance_congr read.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) row

theorem backward_rows (t q z h R B H r M : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hh : Γ ⊢[PRAAx] bounded h H)
    (hs : Γ ⊢[PRAAx] le (stepDivisor R*(previous M*(two*H))) B)
    (hr : Γ ⊢[PRAAx] le (tailCutoff q R) r) :
    Γ ⊢[PRAAx] rowBound (cofinalGrid t (add z h) (gneg h) R B (previous M))
      (polynomialGrid t q z R B (two*H) r M (ofGaussian h B) (qnegative (ofGaussian h B))) (succ (previous M))
      (rowNumerator t q z R B (two*H) r M (ofGaussian h B) (qnegative (ofGaussian h B))) (rowDenominator q t B M) := by
  refine .allI (.impI ?_)
  let a (v : PTm n) := Syn.shift v
  let j : PTm (n+1) := var 0
  let N := previous (a M)
  let Δ := lt j (succ N) :: Γ.map Fm.shift
  let w := ofGaussian (a h) (a B)
  have z' : Δ ⊢[PRAAx] source (a z) (a R) (a B) := by simpa [Δ,a,Fm.shift,Syn.shift] using hz.shift.wk
  have h' : Δ ⊢[PRAAx] bounded (a h) (a H) := by simpa [Δ,a,Fm.shift,Syn.shift] using hh.shift.wk
  have s' : Δ ⊢[PRAAx] le (stepDivisor (a R)*(N*(two*a H))) (a B) := by
    simpa [Δ,a,N,Fm.shift,Syn.shift,two] using hs.shift.wk
  have r' : Δ ⊢[PRAAx] le (tailCutoff (a q) (a R)) (a r) := by
    simpa [Δ,a,Fm.shift,Syn.shift] using hr.shift.wk
  have hj : Δ ⊢[PRAAx] lt j (succ N) := Prf.hyp0
  have hN : Δ ⊢[PRAAx] le one N := zero_lt_succ _
  have row := node_error (a t) (a q) (a z) (backwardDisplacement (a h) j) (a R) (a B)
    (two*a H) (a r) (a M) w (qnegative w) j z'
    (backward_bound _ _ _ _ h' hN (Common.le_of_lt_succ hj)) s' r' hj (backward_point _ _ _ z'.andE₁)
  have read := (cofinal_at (a t) (add (a z) (a h)) (gneg (a h)) (a R) (a B) N j hj).eqTrans
    (congrAp2 G (.eqRefl _) (backward_data (a z) (a h) (a R) (a B) j))
  simpa [Δ,a,j,N,w,Syn.shift,one,two] using distance_congr read.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) row

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCofinalTaylorMixedGridRows

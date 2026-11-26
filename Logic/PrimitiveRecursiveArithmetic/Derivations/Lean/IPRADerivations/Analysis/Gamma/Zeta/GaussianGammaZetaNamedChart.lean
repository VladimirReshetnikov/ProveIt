import IPRADerivations.Analysis.Gamma.Zeta.GaussianGammaZetaDirichletProductParameterRate
import IPRADerivations.Analysis.Names.GaussianNamedRightHalfPlaneDemandLift

/-!
# Signed rational charts for the original C58 samplers

The supplied regular input names represent the parameter minus one.
Each admitted signed observation supplies the native numerator,
a fixed enlarged disk, and an integer reciprocal real-part margin.
The original Dirichlet and Gamma–Dirichlet samplers share a demand.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaNamedChart

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (bounded eval_re_code)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEulerIntegralGammaIdentification (source)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianNamedMultiplyRate (sampleBound)
open GaussianNamedInverseRate (independentRate subst_independentRate)
open GaussianNamedRightHalfPlaneSigned (certificate point realNumerator imagNumerator sign)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalMetric (distanceBounded)
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (monus)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev denominator (q : PTm n) : PTm n := GaussianNamedRightHalfPlaneSigned.denominator q

def numerator (q : PTm n) : PTm n :=
  GaussianLogGammaEulerResidualDomain.native (realNumerator q) (imagNumerator q) (sign q)

def radius (R : PTm n) : PTm n := succ R

def degree (K : PTm n) : PTm n := succ K

theorem native_source (q R K : PTm n) (hq : Γ ⊢[PRAAx] certificate q R K) :
    Γ ⊢[PRAAx] source (numerator q) (radius R) (denominator q) (degree K) := by
  let D := denominator q
  let A := degree K
  let u := realNumerator q
  have grow : Γ ⊢[PRAAx] le D (A*u) :=
    le_trans hq.andE₂.andE₁ (mul_le_mul_right u (le_succ_self K))
  have low : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.realLower (numerator q) A D := by
    apply zle_of_toZ (monus (A*u) D)
    have e := natEq (eq_add_of_le grow)
    simp only [numerator,GaussianLogGammaEulerResidualDomain.native,eval_re_code,
      ZT.toZ_mul,ZT.toZ_ofNat]
    ipra_simps
    exact e.symm
  have disk : Γ ⊢[PRAAx] bounded (numerator q) (radius R*D) :=
    ComplexLogarithmRemainder.bounded_mono hq.andE₁.andE₂ (mul_le_mul_right D (le_succ_self R))
  exact .andI (.andI (zero_lt_succ K) (.andI (.andI hq.andE₁.andE₁.andE₂ disk) low)) (zero_lt_succ R)

def dirichletData (q R K : PTm n) : PTm n :=
  GaussianGammaZetaDirichletCofinal.data (numerator q) (radius R) (denominator q) (degree K)

def productData (q R K : PTm n) : PTm n :=
  GaussianGammaZetaDirichletProduct.data (numerator q) (radius R) (denominator q) (degree K)

def gammaData (q R K : PTm n) : PTm n :=
  GaussianGammaZetaDirichletProduct.actualGammaData (numerator q) (radius R) (denominator q) (degree K)

def gammaDemand (s R K : PTm n) : PTm n :=
  GaussianGammaHalfPlaneInputContinuity.modulus s (radius R+one) (degree K)

def demandValue (s R K : PTm n) : PTm n :=
  GaussianGammaZetaDirichletProductParameterRate.demand s (radius R) (degree K)+
    GaussianGammaZetaDirichletParameterRate.demand s (radius R) (degree K)+gammaDemand s R K

def dirichletDataF : PR 3 := PTm.toPR (dirichletData (var 0) (var 1) (var 2) : PTm 3)
def productDataF : PR 3 := PTm.toPR (productData (var 0) (var 1) (var 2) : PTm 3)
def gammaDataF : PR 3 := PTm.toPR (gammaData (var 0) (var 1) (var 2) : PTm 3)
def demand : PR 3 := PTm.toPR (demandValue (var 0) (var 1) (var 2) : PTm 3)

@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (q : PTm n) :
    Syn.subst σ (numerator q) = numerator (Syn.subst σ q) := by
  simp [numerator]

@[simp] theorem subst_dirichletData {m : ℕ} (σ : Fin n → PTm m) (q R K : PTm n) :
    Syn.subst σ (dirichletData q R K) = dirichletData (Syn.subst σ q) (Syn.subst σ R) (Syn.subst σ K) := by
  simp [dirichletData,GaussianGammaZetaDirichletCofinal.data,radius,degree]

@[simp] theorem subst_productData {m : ℕ} (σ : Fin n → PTm m) (q R K : PTm n) :
    Syn.subst σ (productData q R K) = productData (Syn.subst σ q) (Syn.subst σ R) (Syn.subst σ K) := by
  simp [productData,radius,degree]

@[simp] theorem subst_gammaData {m : ℕ} (σ : Fin n → PTm m) (q R K : PTm n) :
    Syn.subst σ (gammaData q R K) = gammaData (Syn.subst σ q) (Syn.subst σ R) (Syn.subst σ K) := by
  simp [gammaData,radius,degree]

@[simp] theorem subst_demandValue {m : ℕ} (σ : Fin n → PTm m) (s R K : PTm n) :
    Syn.subst σ (demandValue s R K) = demandValue (Syn.subst σ s) (Syn.subst σ R) (Syn.subst σ K) := by
  simp [demandValue,gammaDemand,radius,degree,one]

theorem dirichlet_data_at (q R K : PTm n) : Γ ⊢[PRAAx] ap3 dirichletDataF q R K ≐ dirichletData q R K := by
  simpa only [dirichletDataF,ap3,subst_dirichletData,Syn.subst_var,Matrix.cons_val] using
    toPR_eq (Γ := Γ) (dirichletData (var 0) (var 1) (var 2) : PTm 3) ![q,R,K]

theorem product_data_at (q R K : PTm n) : Γ ⊢[PRAAx] ap3 productDataF q R K ≐ productData q R K := by
  simpa only [productDataF,ap3,subst_productData,Syn.subst_var,Matrix.cons_val] using
    toPR_eq (Γ := Γ) (productData (var 0) (var 1) (var 2) : PTm 3) ![q,R,K]

theorem gamma_data_at (q R K : PTm n) : Γ ⊢[PRAAx] ap3 gammaDataF q R K ≐ gammaData q R K := by
  simpa only [gammaDataF,ap3,subst_gammaData,Syn.subst_var,Matrix.cons_val] using
    toPR_eq (Γ := Γ) (gammaData (var 0) (var 1) (var 2) : PTm 3) ![q,R,K]

theorem demand_at (s R K : PTm n) : Γ ⊢[PRAAx] ap3 demand s R K ≐ demandValue s R K := by
  simpa only [demand,ap3,subst_demandValue,Syn.subst_var,Matrix.cons_val] using
    toPR_eq (Γ := Γ) (demandValue (var 0) (var 1) (var 2) : PTm 3) ![s,R,K]

theorem demand_lower (x y R K s k : PTm n)
    (hk : Γ ⊢[PRAAx] le k (demandValue s R K))
    (hd : Γ ⊢[PRAAx] distanceBounded (point x) (point y) one (unit (ap3 demand s R K))) :
    Γ ⊢[PRAAx] distanceBounded (point x) (point y) one (unit k) := by
  let m := demandValue s R K
  have read : Γ ⊢[PRAAx] unit (ap3 demand s R K) ≐ unit m :=
    congrAp2 powF (demand_at s R K) (.eqRefl two)
  have h : Γ ⊢[PRAAx] distanceBounded (point x) (point y) one (unit m) :=
    distance_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) read hd
  exact distance_radius_mono _ _ _ _ _ _ (unit_positive m) (unit_positive k)
    (le_congr (one_mul _).eqSymm (one_mul _).eqSymm (GaussianExponentialReference.unit_monotone hk)) h

theorem variation_congr (F : PR 2) (x y u v s : PTm n)
    (ex : Γ ⊢[PRAAx] x ≐ u) (ey : Γ ⊢[PRAAx] y ≐ v)
    (h : Γ ⊢[PRAAx] independentRate F F x y one (unit s)) :
    Γ ⊢[PRAAx] independentRate F F u v one (unit s) := by
  let φ : Fm PTm 4 := independentRate F F (var 0) (var 1) (var 2) (var 3)
  have e := Prf.eqSubst (Γ := Γ) (Ax := PRAAx) φ ![x,y,one,unit s] ![u,v,one,unit s]
    (fun i => by
      fin_cases i
      · exact ex
      · exact ey
      · exact .eqRefl _
      · exact .eqRefl _)
    (by simpa only [φ,subst_independentRate,Syn.subst_var,Matrix.cons_val] using h)
  simpa only [φ,subst_independentRate,Syn.subst_var,Matrix.cons_val] using e

theorem product_variation (x y R K s : PTm n) (hx : Γ ⊢[PRAAx] certificate x R K)
    (hy : Γ ⊢[PRAAx] certificate y R K)
    (hd : Γ ⊢[PRAAx] distanceBounded (point x) (point y) one (unit (ap3 demand s R K))) :
    Γ ⊢[PRAAx] independentRate GaussianGammaZetaDirichletProduct.nameF GaussianGammaZetaDirichletProduct.nameF
      (ap3 productDataF x R K) (ap3 productDataF y R K) one (unit s) := by
  let p := GaussianGammaZetaDirichletProductParameterRate.demand s (radius R) (degree K)
  let d := GaussianGammaZetaDirichletParameterRate.demand s (radius R) (degree K)
  have near := demand_lower x y R K s p (le_trans (le_add_right p d) (le_add_right _ (gammaDemand s R K))) hd
  have rate := GaussianGammaZetaDirichletProductParameterRate.original_demand_rate s (numerator x) (numerator y)
    (radius R) (denominator x) (denominator y) (degree K) (native_source x R K hx) (native_source y R K hy) near
  exact variation_congr _ _ _ _ _ s (product_data_at x R K).eqSymm (product_data_at y R K).eqSymm rate

theorem dirichlet_variation (x y R K s : PTm n) (hx : Γ ⊢[PRAAx] certificate x R K)
    (hy : Γ ⊢[PRAAx] certificate y R K)
    (hd : Γ ⊢[PRAAx] distanceBounded (point x) (point y) one (unit (ap3 demand s R K))) :
    Γ ⊢[PRAAx] independentRate GaussianGammaZetaDirichletCofinal.nameF GaussianGammaZetaDirichletCofinal.nameF
      (ap3 dirichletDataF x R K) (ap3 dirichletDataF y R K) one (unit s) := by
  let p := GaussianGammaZetaDirichletProductParameterRate.demand s (radius R) (degree K)
  let d := GaussianGammaZetaDirichletParameterRate.demand s (radius R) (degree K)
  have near := demand_lower x y R K s d (le_trans (le_add_left d p) (le_add_right _ (gammaDemand s R K))) hd
  have rate := GaussianGammaZetaDirichletParameterRate.original_demand_rate s (numerator x) (numerator y)
    (radius R) (denominator x) (denominator y) (degree K) (native_source x R K hx) (native_source y R K hy) near
  exact variation_congr _ _ _ _ _ s (dirichlet_data_at x R K).eqSymm (dirichlet_data_at y R K).eqSymm rate

theorem gamma_variation (x y R K s : PTm n) (hx : Γ ⊢[PRAAx] certificate x R K)
    (hy : Γ ⊢[PRAAx] certificate y R K)
    (hd : Γ ⊢[PRAAx] distanceBounded (point x) (point y) one (unit (ap3 demand s R K))) :
    Γ ⊢[PRAAx] independentRate gammaF gammaF
      (ap3 gammaDataF x R K) (ap3 gammaDataF y R K) one (unit s) := by
  have near := demand_lower x y R K s (gammaDemand s R K) (le_add_left (gammaDemand s R K) _) hd
  have rate := GaussianGammaZetaDirichletProductParameterRate.gamma_rate s (numerator x) (numerator y)
    (radius R) (denominator x) (denominator y) (degree K) (native_source x R K hx) (native_source y R K hy) near
  exact variation_congr _ _ _ _ _ s (gamma_data_at x R K).eqSymm (gamma_data_at y R K).eqSymm rate

theorem dirichlet_regular (q R K : PTm n) (h : Γ ⊢[PRAAx] certificate q R K) :
    Γ ⊢[PRAAx] pointCN GaussianGammaZetaDirichletCofinal.nameF (dirichletData q R K) :=
  GaussianGammaZetaDirichletCofinal.regular _ _ _ _ (native_source q R K h)

theorem gamma_regular (q R K : PTm n) (h : Γ ⊢[PRAAx] certificate q R K) :
    Γ ⊢[PRAAx] pointCN gammaF (gammaData q R K) :=
  GaussianEulerIntegralGammaIdentification.original_gamma_regular _ _ _ _
    (GaussianGammaZetaDirichletPowerOrder.shifted_source _ _ _ _ (native_source q R K h))

theorem dirichlet_samples (q R K : PTm n) (h : Γ ⊢[PRAAx] certificate q R K) :
    Γ ⊢[PRAAx] sampleBound GaussianGammaZetaDirichletCofinal.nameF (dirichletData q R K)
      (GaussianGammaZetaDirichletUniformBound.cap (degree K)) :=
  GaussianGammaZetaDirichletUniformBound.samples _ _ _ _ (native_source q R K h)

theorem gamma_samples (q R K : PTm n) (h : Γ ⊢[PRAAx] certificate q R K) :
    Γ ⊢[PRAAx] sampleBound gammaF (gammaData q R K)
      (GaussianGammaZetaDirichletProductParameterRate.gammaCap (radius R) (degree K)) :=
  GaussianGammaZetaDirichletProductParameterRate.gamma_samples _ _ _ _ (native_source q R K h)

def productMap : GaussianNamedRightHalfPlaneDemandLift.RationalMap where
  evaluator := GaussianGammaZetaDirichletProduct.nameF
  rationalData := productDataF
  demand := demand
  variation := product_variation

def dirichletMap : GaussianNamedRightHalfPlaneDemandLift.RationalMap where
  evaluator := GaussianGammaZetaDirichletCofinal.nameF
  rationalData := dirichletDataF
  demand := demand
  variation := dirichlet_variation

def gammaMap : GaussianNamedRightHalfPlaneDemandLift.RationalMap where
  evaluator := gammaF
  rationalData := gammaDataF
  demand := demand
  variation := gamma_variation

end LeanProofs.IPRA.Analysis.GaussianGammaZetaNamedChart

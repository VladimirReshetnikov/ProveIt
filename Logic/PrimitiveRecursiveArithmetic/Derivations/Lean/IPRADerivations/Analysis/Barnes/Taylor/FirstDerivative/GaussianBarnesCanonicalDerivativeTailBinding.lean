import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.GaussianBarnesCanonicalDerivativeInterval
import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.GaussianBarnesCanonicalDerivativeCofinalRate
import IPRADerivations.Analysis.Names.Rates.GaussianBoundedConstantProductRate
import IPRADerivations.Analysis.Names.Rates.GaussianNamedDifferenceRate
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateComposition
import IPRADerivations.Analysis.Names.GaussianNameConjugation

/-!
# First-order increment of the original cofinal Barnes logarithmic tail

Use the same finite truncation to compare the original cofinal logarithms
and the cofinal derivative. The comparison length absorbs all three
prefix errors; the leading remainder keeps the inverse-square bound
for the full infinite tail.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDerivativeTailBinding

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open ComplexLogarithmRemainder (add normSq)
open GaussianBarnesCanonicalDerivativeInterval (errorNumerator errorDenominator scaledValue)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial initial_positive)
open GaussianBarnesCanonicalLogTail (tailDenominator tail_denominator_positive)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNamedInverseRate (independentRate diagonal_rate)
open GaussianNamedLipschitzRate (diagonalEnvelope diagonalNumerator diagonalDenominator)
open GaussianNamedRateComposition (same_denominator symmetric)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalHorner (ofGaussian ofGaussian_represents positive_product qmul)
open GaussianRationalMetric (bounded bounded_of_cleared distanceBounded)
open GaussianRationalSyntheticDivision (qmul_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "L" => GaussianBarnesCanonicalLogCofinal.nameF
local notation "ld" => GaussianBarnesCanonicalLogCofinal.data
local notation "F" => GaussianBarnesCanonicalFiniteLog.nameF
local notation "fd" => GaussianBarnesCanonicalFiniteLog.data
local notation "D" => GaussianBarnesCanonicalDerivativeCofinal.nameF
local notation "CofinalDerivativeBound" => GaussianBarnesCanonicalDerivativeRow.boundNumerator
local notation "CofinalLogBound" => GaussianBarnesCanonicalLogRow.boundNumerator
local notation "Prod" => GaussianBoundedConstantProductName.nameF
local notation "prodData" => GaussianBoundedConstantProductName.data
local notation "Diff" => GaussianNamedDifference.nameF
local notation "diffData" => GaussianNamedDifference.data
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def input (z h R B H : PTm n) : Fm PTm n :=
  GaussianBarnesCanonicalDerivativeInterval.input z h R B (initial R) H

def incrementF : PR 2 := Diff L L
def incrementData (z h R B : PTm n) : PTm n := diffData (ld (add z h) R B) (ld z R B)
def scaledDerivativeF : PR 2 := multiplyF constantF D
def scaledDerivativeData (z h R B : PTm n) : PTm n := multiplyData constantF D (ofGaussian h B) (ld z R B)
def leadingDenominator (R B : PTm n) : PTm n := (B*B)*initial R
def length (p R : PTm n) : PTm n := (two*CofinalLogBound R+CofinalDerivativeBound R)*unit p

@[simp] theorem subst_input {m : ℕ} (σ : Fin n → PTm m) (z h R B H : PTm n) :
    (input z h R B H).subst σ =
      input (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ H) := by simp [input]

@[simp] theorem subst_incrementData {m : ℕ} (σ : Fin n → PTm m) (z h R B : PTm n) :
    Syn.subst σ (incrementData z h R B) =
      incrementData (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ R) (Syn.subst σ B) := by simp [incrementData]

@[simp] theorem subst_scaledDerivativeData {m : ℕ} (σ : Fin n → PTm m) (z h R B : PTm n) :
    Syn.subst σ (scaledDerivativeData z h R B) =
      scaledDerivativeData (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ R) (Syn.subst σ B) := by simp [scaledDerivativeData]

@[simp] theorem subst_leadingDenominator {m : ℕ} (σ : Fin n → PTm m) (R B : PTm n) :
    Syn.subst σ (leadingDenominator R B) = leadingDenominator (Syn.subst σ R) (Syn.subst σ B) := by simp [leadingDenominator]

theorem base_source (z h R B H : PTm n) (hs : Γ ⊢[PRAAx] input z h R B H) :
    Γ ⊢[PRAAx] source z R B :=
  .andI hs.andE₁.andE₁ hs.andE₁.andE₂.andE₂.andE₁

theorem shifted_source (z h R B H : PTm n) (hs : Γ ⊢[PRAAx] input z h R B H) :
    Γ ⊢[PRAAx] source (add z h) R B :=
  .andI hs.andE₂.andE₁.andE₁ hs.andE₂.andE₁.andE₂.andE₂.andE₁

theorem input_bound (z h R B H : PTm n) (hs : Γ ⊢[PRAAx] input z h R B H) :
    Γ ⊢[PRAAx] bounded (ofGaussian h B) one one := by
  have hB := (base_source z h R B H hs).andE₁
  have norm : Γ ⊢[PRAAx] le (normSq h) (H*H) := hs.andE₂.andE₂.andE₁
  have hH := hs.andE₂.andE₂.andE₂.andE₂
  exact bounded_of_cleared _ _ _ _ _ hB (le_refl one) (ofGaussian_represents h B hB)
    (le_congr (by ipra_ring) (by ipra_ring) (le_trans norm (le_mul_mono hH hH)))

theorem leading_denominator_positive (R B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] le one (leadingDenominator R B) :=
  positive_product _ _ (positive_product _ _ hB hB) (initial_positive R)

private theorem diff_prefix_rate (z h R B r : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source (add z h) R B) : Γ ⊢[PRAAx]
    independentRate GaussianBarnesCanonicalDerivativeInterval.incrementF incrementF
      (GaussianBarnesCanonicalDerivativeInterval.incrementData z h R B (initial R) r) (incrementData z h R B)
      ((two*CofinalLogBound R)*leadingDenominator R B) (leadingDenominator R B*(initial R+r)) := by
  let N := initial R
  let K := N+r
  let T := tailDenominator K
  let P := leadingDenominator R B
  let Q := CofinalLogBound R
  have hK : Γ ⊢[PRAAx] le one K := le_trans (initial_positive R) (le_add_right _ _)
  have hT := tail_denominator_positive K hK
  have hP := leading_denominator_positive R B hz.andE₁
  have rf := GaussianBarnesCanonicalLogCofinalRate.finite_tail_rate z R B r hz
  have rg := GaussianBarnesCanonicalLogCofinalRate.finite_tail_rate (add z h) R B r hw
  have h₁ := GaussianBarnesCanonicalFiniteLog.regular (add z h) R B N r
    (GaussianBarnesCanonicalLogCofinalRate.initial_source _ _ _ hw)
  have h₂ := GaussianBarnesCanonicalFiniteLog.regular z R B N r
    (GaussianBarnesCanonicalLogCofinalRate.initial_source _ _ _ hz)
  have diff := GaussianNamedDifferenceRate.original_rate F F L L (fd (add z h) R B N r) (fd z R B N r)
    (ld (add z h) R B) (ld z R B) Q T Q T
    (.andI (.andI hT hT) (.andI (.andI h₁ h₂)
      (.andI (.andI (GaussianBarnesCanonicalLogCofinal.regular _ _ _ hw) (GaussianBarnesCanonicalLogCofinal.regular _ _ _ hz))
        (.andI rg rf))))
  exact GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ (positive_product _ _ hT hT) (positive_product _ _ hP hK)
    (le_of_eq_add (d := num 12*P*Q*K*K) (by
      change Γ ⊢[PRAAx] (two*Q*P)*((num 3*K)*(num 3*K)) ≐
        (Q*(num 3*K)+Q*(num 3*K))*(P*K)+num 12*P*Q*K*K
      ipra_ring)) diff

private theorem constant_product_cross (a v : PTm n) (ha : Γ ⊢[PRAAx] bounded a one one) :
    Γ ⊢[PRAAx] crossEquivalent constantF (Prod constantF) (qmul a v) (prodData one a v) := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _ (constant_regular _)
    (GaussianBoundedConstantProductName.name_regular constantF one a v (.andI (constant_regular v) ha))
  refine .allI ?_
  let s (x : PTm n) := Syn.shift x
  let Δ := Γ.map Fm.shift
  let p : PTm (n+1) := var 0
  let k := GaussianBoundedConstantProductName.clock p one
  have read : Δ ⊢[PRAAx] ap2 (Prod constantF) p (prodData one (s a) (s v)) ≐ qmul (s a) (s v) :=
    (GaussianBoundedConstantProductName.sample_at constantF p one (s a) (s v)).eqTrans
      (qmul_congr (.eqRefl _) (constant_at k (s v)))
  simpa only [GaussianNameConjugation.pointwiseEqual,Syn.shift,s,Δ,p,GaussianRationalHorner.subst_qmul,
    GaussianBoundedConstantProductName.subst_data,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    (constant_at p (qmul (s a) (s v))).eqTrans read.eqSymm

private theorem derivative_prefix_rate (z h R B r : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (ha : Γ ⊢[PRAAx] bounded (ofGaussian h B) one one) : Γ ⊢[PRAAx]
    independentRate constantF (Prod D) (scaledValue z h B (initial R) r) (prodData one (ofGaussian h B) (ld z R B))
      (CofinalDerivativeBound R*leadingDenominator R B) (leadingDenominator R B*(initial R+r)) := by
  let a := ofGaussian h B
  let v := GaussianBarnesCanonicalDerivativeTail.value z B (initial R) r
  let K := initial R+r
  let P := leadingDenominator R B
  let C := CofinalDerivativeBound R
  let x := ld z R B
  have hK : Γ ⊢[PRAAx] le one K := le_trans (initial_positive R) (le_add_right _ _)
  have hP := leading_denominator_positive R B hz.andE₁
  have hr := GaussianBarnesCanonicalDerivativeCofinalRate.finite_rate z R B r hz
  have ra := GaussianBoundedConstantProductRate.original_rate constantF D one a v x C K hK ha hr
  have hx := GaussianBoundedConstantProductName.name_regular D one a x
    (.andI (GaussianBarnesCanonicalDerivativeCofinal.regular z R B hz) ha)
  have rt := GaussianNamedRateTransport.transport (Prod constantF) (Prod D) constantF (Prod D)
    (prodData one a v) (prodData one a x) (qmul a v) (prodData one a x) (one*C) K hK ra
    (constant_product_cross a v ha) (cross_refl _ _ hx)
  exact GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ hK (positive_product _ _ hP hK)
    (le_of_eq_add (d := zero) (by
      change Γ ⊢[PRAAx] (C*P)*K ≐ (one*C)*(P*K)+zero
      ipra_ring)) rt

private theorem observation (p z h R B H : PTm n) (hs : Γ ⊢[PRAAx] input z h R B H) : Γ ⊢[PRAAx]
    distanceBounded (ap2 incrementF p (incrementData z h R B))
      (ap2 (Prod D) p (prodData one (ofGaussian h B) (ld z R B)))
      (diagonalNumerator (errorNumerator R H) (leadingDenominator R B) (num 3) p)
      (diagonalDenominator (leadingDenominator R B) p) := by
  let N := initial R
  let r := length p R
  let P := leadingDenominator R B
  let K := N+r
  let A := errorNumerator R H
  let Q := CofinalLogBound R
  let C := CofinalDerivativeBound R
  let U := unit p
  let a := GaussianBarnesCanonicalDerivativeInterval.incrementData z h R B N r
  let b := scaledValue z h B N r
  let x := incrementData z h R B
  let y := prodData one (ofGaussian h B) (ld z R B)
  have hz := base_source z h R B H hs
  have hw := shifted_source z h R B H hs
  have hP := leading_denominator_positive R B hz.andE₁
  have hK : Γ ⊢[PRAAx] le one K := le_trans (initial_positive R) (le_add_right _ _)
  have hPK : Γ ⊢[PRAAx] le one (P*K) := positive_product _ _ hP hK
  have first := symmetric GaussianBarnesCanonicalDerivativeInterval.incrementF incrementF a x
    ((two*Q)*P) (P*K) hPK (diff_prefix_rate z h R B r hz hw)
  have middle := GaussianNamedDifferenceRate.rate_parameters_congr GaussianBarnesCanonicalDerivativeInterval.incrementF constantF
    a b (A*r) (errorDenominator B N r) (A*r) (P*K) (.eqRefl _)
    (by dsimp only [errorDenominator,GaussianReciprocalSquareInterval.denominator,P,K,leadingDenominator,N]; ipra_ring)
    (GaussianBarnesCanonicalDerivativeInterval.rate z h R B N H r hs)
  have last := derivative_prefix_rate z h R B r hz (input_bound z h R B H hs)
  have joined := same_denominator incrementF constantF (Prod D) x b y ((two*Q)*P+A*r) (P*K) (C*P) hPK
    (same_denominator incrementF GaussianBarnesCanonicalDerivativeInterval.incrementF constantF x a b ((two*Q)*P) (P*K)
      (A*r) hPK first middle) last
  have diagonal := diagonal_rate incrementF (Prod D) x y _ (P*K) p hPK joined
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hPK (unit_positive p))
    (positive_product _ _ hP (unit_positive p))
    (by
      change Γ ⊢[PRAAx] le (((two*Q*P+A*((two*Q+C)*U)+C*P)*U+two*(P*K))*(P*U))
        ((A*U+num 3*P)*(P*K*U))
      have budget : Γ ⊢[PRAAx] le ((two*Q+C)*U) K := le_add_left _ _
      ipra_le (𝔞(P)*𝔞(U)*(𝔞(A)*𝔞(U)+𝔞(P)))*sl budget) diagonal

theorem rate (z h R B H : PTm n) (hs : Γ ⊢[PRAAx] input z h R B H) : Γ ⊢[PRAAx]
    independentRate incrementF scaledDerivativeF (incrementData z h R B) (scaledDerivativeData z h R B)
      (errorNumerator R H) (leadingDenominator R B) := by
  let x := incrementData z h R B
  let a := ofGaussian h B
  let y := prodData one a (ld z R B)
  let M := errorNumerator R H
  let K := leadingDenominator R B
  have hz := base_source z h R B H hs
  have hw := shifted_source z h R B H hs
  have hK := leading_denominator_positive R B hz.andE₁
  have hx := GaussianNamedDifference.name_regular L L (ld (add z h) R B) (ld z R B)
    (GaussianBarnesCanonicalLogCofinal.regular _ _ _ hw) (GaussianBarnesCanonicalLogCofinal.regular _ _ _ hz)
  have hprod := Prf.andI (GaussianBarnesCanonicalDerivativeCofinal.regular z R B hz) (input_bound z h R B H hs)
  have hy := GaussianBoundedConstantProductName.name_regular D one a (ld z R B) hprod
  have env : Γ ⊢[PRAAx] diagonalEnvelope incrementF (Prod D) x y M K (num 3) := by
    refine .allI ?_
    let sh (u : PTm n) := Syn.shift u
    let Δ := Γ.map Fm.shift
    have hh : Δ ⊢[PRAAx] input (sh z) (sh h) (sh R) (sh B) (sh H) := by
      simpa [Fm.shift,Syn.shift,sh,Δ] using hs.shift
    simpa only [diagonalEnvelope,Syn.shift,sh,Δ,x,a,y,M,K,subst_incrementData,
      GaussianBoundedConstantProductName.subst_data,GaussianRationalHorner.subst_ofGaussian,
      GaussianBarnesCanonicalLogCofinal.subst_data,subst_leadingDenominator,
      GaussianBarnesCanonicalDerivativeInterval.subst_errorNumerator,PTm.subst_num,
      one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
      observation (var 0) (sh z) (sh h) (sh R) (sh B) (sh H) hh
  have raw := GaussianNamedLipschitzRate.independent_rate incrementF (Prod D) x y M K (num 3) hK hx hy env
  exact GaussianNamedRateTransport.transport incrementF (Prod D) incrementF scaledDerivativeF x y x
    (scaledDerivativeData z h R B) M K hK raw (cross_refl _ _ hx)
    (cross_symm _ _ _ _ (GaussianBoundedConstantProductName.ordinary_product_identity D one a (ld z R B) hprod))

theorem actual_Barnes_cofinal_logarithm_first_order_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (let z := var 0
     let h := var 1
     let R := var 2
     let B := var 3
     let H := var 4
     input z h R B H ⟶
       independentRate incrementF scaledDerivativeF (incrementData z h R B) (scaledDerivativeData z h R B)
         (errorNumerator R H) (leadingDenominator R B)) :=
  closeUniv 5 (.impI (rate _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDerivativeTailBinding

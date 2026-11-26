import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.FirstDerivative.GaussianBarnesCanonicalPositiveHeadLogarithmRowDerivative
import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.FirstDerivative.GaussianBarnesCanonicalPositiveFirstLogarithmKept
import IPRADerivations.Analysis.Integration.Quadrature.GaussianRationalQuadratureDifference
import IPRADerivations.Analysis.Names.Rates.GaussianNamedLipschitzRate

/-!
# Derivative of the actual finite kept positive Barnes logarithm

Fold the original weighted row increments at their common outer clock.
The model is the physical displacement multiplied by the exact checked
reciprocal sum of the original kept bases.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPositiveHeadLogarithmDerivative

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalPositiveHeadLogarithm (parameters)
open GaussianBarnesCanonicalPositiveHeadLogarithmRowDerivative (rowLinear numerator subst_numerator)
open GaussianBarnesCanonicalThirdDerivativePositiveMargin (source step)
open GaussianBarnesCanonicalThirdLogarithmRows (center)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianHarmonicIntegerExponential (originalExponentF)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedLipschitzRate (diagonalEnvelope diagonalNumerator diagonalDenominator)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalFiniteSum (multiplyBody multiply_body_at sum_multiply)
open GaussianRationalHorner (ofGaussian qmul positive_product)
open GaussianRationalMetric (qsub distanceBounded)
open GaussianRationalQuadratureDifference (differenceBody difference_body_at finite_sum_difference)
open GaussianRationalRiemannRefinement (termsDistance sum_distance)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "F" => GaussianBarnesCanonicalPositiveHeadLogarithm.nameF
local notation "fd" => GaussianBarnesCanonicalPositiveHeadLogarithm.data
local notation "P" => GaussianBarnesCanonicalPositiveHeadLogarithm.body
local notation "S" => GaussianNamedFiniteSumFamily.body originalExponentF P
local notation "U" => GaussianBarnesCanonicalPositiveFirstLogarithmKept.body

def nameF : PR 2 := GaussianNamedDifference.nameF F F
def data (A C B N : PTm n) : PTm n := GaussianNamedDifference.data (fd C B N) (fd A B N)
def linear (A C B N : PTm n) : PTm n := qmul (ofGaussian (step A C) B)
  (GaussianBarnesCanonicalPositiveFirstLogarithmKept.value (center A B) B N)
def observationCost (N : PTm n) : PTm n := num 6+two*(N*N)

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (A C B N : PTm n) :
    Syn.subst σ (data A C B N) = data (Syn.subst σ A) (Syn.subst σ C) (Syn.subst σ B) (Syn.subst σ N) := by simp [data]

@[simp] theorem subst_linear {m : ℕ} (σ : Fin n → PTm m) (A C B N : PTm n) :
    Syn.subst σ (linear A C B N) = linear (Syn.subst σ A) (Syn.subst σ C) (Syn.subst σ B) (Syn.subst σ N) := by simp [linear]

@[simp] theorem subst_observationCost {m : ℕ} (σ : Fin n → PTm m) (N : PTm n) :
    Syn.subst σ (observationCost N) = observationCost (Syn.subst σ N) := by simp [observationCost,two,one]

private theorem difference_entry (p A C B i : PTm n) : Γ ⊢[PRAAx]
    inst2 (differenceBody S S) i (pairT (pairT p (parameters C B)) (pairT p (parameters A B))) ≐
      qsub (ap2 originalExponentF p (GaussianBarnesCanonicalPositiveHeadLogarithm.rowData C B i))
        (ap2 originalExponentF p (GaussianBarnesCanonicalPositiveHeadLogarithm.rowData A B i)) := by
  have term (X : PTm n) : Γ ⊢[PRAAx] inst2 S i (pairT p (parameters X B)) ≐
      ap2 originalExponentF p (GaussianBarnesCanonicalPositiveHeadLogarithm.rowData X B i) :=
    (GaussianNamedFiniteSumFamily.term_at originalExponentF P i p (parameters X B)).eqTrans
      (congrAp2 originalExponentF (.eqRefl p) (GaussianBarnesCanonicalPositiveHeadLogarithm.row_at X B i))
  exact (difference_body_at S S i _ _).eqTrans (qsub_congr (term C) (term A))

private theorem linear_entry (A C B i : PTm n) : Γ ⊢[PRAAx]
    inst2 (multiplyBody U) i (pairT (ofGaussian (step A C) B) (pairT (center A B) B)) ≐ rowLinear A C B i :=
  (multiply_body_at U _ i _).eqTrans
    (qmul_congr (.eqRefl _) (GaussianBarnesCanonicalPositiveFirstLogarithmKept.body_at (center A B) B i))

theorem finite_error (p A C B H K N : PTm n) (h : Γ ⊢[PRAAx] source A C B H K) :
    Γ ⊢[PRAAx] distanceBounded
      (qsub (GaussianNamedFiniteSumFamily.finite originalExponentF P p N (parameters C B))
        (GaussianNamedFiniteSumFamily.finite originalExponentF P p N (parameters A B)))
      (linear A C B N) (N*(numerator K H*unit p+two*N*(B*B))) ((B*B)*unit p) := by
  let x := pairT p (parameters C B)
  let y := pairT p (parameters A B)
  let s := ofGaussian (step A C) B
  let z := pairT (center A B) B
  let M := numerator K H*unit p+two*N*(B*B)
  let D := (B*B)*unit p
  have hD := positive_product (B*B) (unit p) (positive_product _ _ h.andE₁ h.andE₁) (unit_positive p)
  have each : Γ ⊢[PRAAx] termsDistance (differenceBody S S) (multiplyBody U) N (pairT x y) (pairT s z) M D := by
    refine .allI (.impI ?_)
    let sh (v : PTm n) := Syn.shift v
    let i : PTm (n+1) := var 0
    let Δ := lt i (sh N) :: Γ.map Fm.shift
    have hh : Δ ⊢[PRAAx] source (sh A) (sh C) (sh B) (sh H) (sh K) := by
      simpa [Δ,Fm.shift,Syn.shift,sh] using h.shift.wk
    have e := GaussianBarnesCanonicalPositiveHeadLogarithmRowDerivative.observation
      (sh p) (sh A) (sh C) (sh B) (sh H) (sh K) (sh N) i hh Prf.hyp0
    simpa only [termsDistance,Δ,sh,i,Syn.shift,x,y,s,z,M,D,subst_pairT,
      GaussianBarnesCanonicalPositiveHeadLogarithm.subst_parameters,
      GaussianBarnesCanonicalThirdDerivativePositiveMargin.subst_step,
      GaussianBarnesCanonicalThirdLogarithmRows.subst_center,GaussianRationalHorner.subst_ofGaussian,
      GaussianBarnesCanonicalPositiveHeadLogarithmRowDerivative.subst_numerator,
      GaussianCoefficientNameBounds.subst_unit,PTm.subst_mul,PTm.subst_add,two,one,
      ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
        distance_congr (difference_entry (sh p) (sh A) (sh C) (sh B) i).eqSymm
          (linear_entry (sh A) (sh C) (sh B) i).eqSymm (.eqRefl _) (.eqRefl _) e
  exact distance_congr (finite_sum_difference S S N x y) (sum_multiply U s N z) (.eqRefl _) (.eqRefl _)
    (sum_distance _ _ N (pairT x y) (pairT s z) M D hD each)

theorem observation (p A C B H K N : PTm n) (h : Γ ⊢[PRAAx] source A C B H K) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data A C B N)) (linear A C B N)
      (diagonalNumerator (N*numerator K H) (B*B) (observationCost N) p) (diagonalDenominator (B*B) p) := by
  let t := GaussianFastValueCut.exponent N p
  let x := parameters C B
  let y := parameters A B
  let W := B*B
  let clockUnit := unit p
  let V := unit t
  let K₀ := numerator K H
  let M := N*(K₀*clockUnit+two*N*W)
  have hW := positive_product B B h.andE₁ h.andE₁
  have hU := unit_positive (Γ := Γ) p
  have hV := unit_positive (Γ := Γ) t
  have hD := positive_product _ _ hW hU
  have monotone : Γ ⊢[PRAAx] le clockUnit V := GaussianExponentialReference.unit_monotone (le_add_right p _)
  have fit : Γ ⊢[PRAAx] le (N*(K₀*V+two*N*W)*(W*clockUnit)) (M*(W*V)) := by
    ipra_le 2*𝔞 N*𝔞 N*𝔞 W*𝔞 W*sl monotone using dsimp only [M]; ipra_simps; ring
  have bound := distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hW hV) hD fit (finite_error t A C B H K N h)
  have read := qsub_congr (Γ := Γ) (GaussianNamedFiniteSumFamily.sample_at originalExponentF P p N x)
    (GaussianNamedFiniteSumFamily.sample_at originalExponentF P p N y)
  have q := distance_congr read.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) bound
  have rc := GaussianBarnesCanonicalPositiveHeadLogarithm.regular C B N h.andE₂.andE₂.andE₁ h.andE₁
  have ra := GaussianBarnesCanonicalPositiveHeadLogarithm.regular A B N h.andE₂.andE₁ h.andE₁
  have raw := GaussianNamedDifference.sample_error F F (fd C B N) (fd A B N) p rc ra
  have wide : Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data A C B N))
      (qsub (ap2 F p (fd C B N)) (ap2 F p (fd A B N))) (num 6*W) (W*clockUnit) :=
    distance_radius_mono _ _ _ _ _ _ hU hD (le_of_eq_add (d := zero) (by ipra_ring)) raw
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by dsimp only [M,observationCost,diagonalNumerator,W,clockUnit,K₀]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hD wide q)

theorem rate (A C B H K N : PTm n) (h : Γ ⊢[PRAAx] source A C B H K) :
    Γ ⊢[PRAAx] independentRate nameF constantF (data A C B N) (linear A C B N) (N*numerator K H) (B*B) := by
  have rc := GaussianBarnesCanonicalPositiveHeadLogarithm.regular C B N h.andE₂.andE₂.andE₁ h.andE₁
  have ra := GaussianBarnesCanonicalPositiveHeadLogarithm.regular A B N h.andE₂.andE₁ h.andE₁
  apply GaussianNamedLipschitzRate.independent_rate nameF constantF (data A C B N) (linear A C B N)
    (N*numerator K H) (B*B) (observationCost N)
    (positive_product _ _ h.andE₁ h.andE₁) (GaussianNamedDifference.name_regular _ _ _ _ rc ra) (constant_regular _)
  refine .allI ?_
  let sh (v : PTm n) := Syn.shift v
  have hh : Γ.map Fm.shift ⊢[PRAAx] source (sh A) (sh C) (sh B) (sh H) (sh K) := by
    simpa [Fm.shift,Syn.shift,sh] using h.shift
  simpa only [diagonalEnvelope,sh,Syn.shift,subst_data,subst_linear,PTm.subst_mul,
    subst_numerator,subst_observationCost,GaussianNamedLipschitzRate.subst_diagonalNumerator,
    GaussianNamedLipschitzRate.subst_diagonalDenominator] using
    distance_congr (.eqRefl _) (constant_at (var 0) (linear (sh A) (sh C) (sh B) (sh N))).eqSymm
      (.eqRefl _) (.eqRefl _) (observation (var 0) (sh A) (sh C) (sh B) (sh H) (sh K) (sh N) hh)

theorem actual_positive_Barnes_kept_logarithm_first_order_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (let A := var 0
     let C := var 1
     let B := var 2
     let H := var 3
     let K := var 4
     let N := var 5
     source A C B H K ⟶ independentRate nameF constantF (data A C B N) (linear A C B N) (N*numerator K H) (B*B)) :=
  closeUniv 6 (.impI (rate _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPositiveHeadLogarithmDerivative

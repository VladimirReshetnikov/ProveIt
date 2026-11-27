import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.ThirdDerivative.GaussianBarnesCanonicalThirdLogarithmRows
import IPRADerivations.Analysis.Barnes.HeadProducts.ExponentialCorrections.GaussianBarnesCanonicalHeadExponentialFactors
import IPRADerivations.Analysis.Euler.HarmonicLogarithms.GaussianHarmonicIntegerExponential

/-!
# Logarithm of the original kept Barnes powers

On a positive rational chart the base of row (i) is
((A+iB)/(B(i+1))). Sum the actual positive rational logarithms
weighted by (i+1). Exponentiating this finite named sum recovers the
original kept power product exactly as a regular name.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPositiveHeadLogarithm

open_ipra
open GaussianBarnesCanonicalBaseProductShift (powerBody powerProduct power_at)
open GaussianBarnesCanonicalThirdLogarithmRows (base_at center shiftedNumerator shifted_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF)
open GaussianGammaFiniteApproximantName (exponentialInputData)
open GaussianHarmonicIntegerExponential (originalExponentF originalExponentData original_integer_exponential actual_rational_power)
open GaussianNameEquivalence (crossEquivalent cross_trans)
open GaussianNamedFiniteExponentialFold (exponentialBody exponentialBody_at exponential_rows exponential_product_cross)
open GaussianNamedFiniteProductFamily (regularRows)
open GaussianNamedFiniteProductFamilyCongruence (equalRows family_product_cross)
open GaussianRationalHorner (positive_product)
open GaussianRationalReciprocal (powerF)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "F" => originalExponentF
local notation "E" => GaussianRadiusExponentialName.nameF

def rowData (A B i : PTm n) : PTm n := originalExponentData (succ i) (shiftedNumerator A B i) (B*succ i)
def parameters (A B : PTm n) : PTm n := pairT A B
def body : PTm 2 := rowData (fstT (var 1)) (sndT (var 1)) (var 0)
abbrev nameF : PR 2 := GaussianNamedFiniteSumFamily.nameF F body
def data (A B N : PTm n) : PTm n := GaussianNamedFiniteSumFamily.data N (parameters A B)
def expData (A B N : PTm n) : PTm n := exponentialInputData nameF (data A B N)

@[simp] theorem subst_rowData {l : ℕ} (σ : Fin n → PTm l) (A B i : PTm n) :
    Syn.subst σ (rowData A B i) = rowData (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ i) := by
  simp [rowData]

@[simp] theorem subst_parameters {l : ℕ} (σ : Fin n → PTm l) (A B : PTm n) :
    Syn.subst σ (parameters A B) = parameters (Syn.subst σ A) (Syn.subst σ B) := by simp [parameters]

@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (A B N : PTm n) :
    Syn.subst σ (data A B N) = data (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ N) := by simp [data]

theorem row_at (A B i : PTm n) : Γ ⊢[PRAAx] inst2 body i (parameters A B) ≐ rowData A B i := by
  simp only [body,inst2,parameters,subst_rowData,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val]
  ipra_congr (rowData (var 0) (var 1) (var 2) : PTm 3) with [fst_pair A B, snd_pair A B, .eqRefl i]

private theorem row_source (a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] GaussianHarmonicIntegerExponential.source a b b a := by
  have lower := le_congr (one_mul _) (mul_comm _ _) (mul_le_mul_right b ha)
  have upper := le_congr (one_mul _) (mul_comm _ _) (mul_le_mul_right a hb)
  exact .andI hb (.andI (.andI ha hb) (.andI lower upper))

theorem row_regular (A B i : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] pointCN F (rowData A B i) :=
  GaussianHarmonicIntegerExponential.original_exponent_regular (succ i) (shiftedNumerator A B i) (B*succ i)
    (B*succ i) (shiftedNumerator A B i)
    (row_source _ _ (shifted_positive A B i hA) (positive_product _ _ hB (zero_lt_succ i)))

theorem rows_regular (A B N : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] regularRows F body N (parameters A B) := by
  refine .allI (.impI ?_)
  let sh (t : PTm n) := Syn.shift t
  let Δ := lt (var 0) (sh N) :: Γ.map Fm.shift
  have a : Δ ⊢[PRAAx] le one (sh A) := by simpa [Fm.shift,Syn.shift,sh,Δ,one] using hA.shift.wk
  have b : Δ ⊢[PRAAx] le one (sh B) := by simpa [Fm.shift,Syn.shift,sh,Δ,one] using hB.shift.wk
  simpa only [Syn.shift,sh,Δ,subst_parameters] using
    GaussianGammaCompactCutoffSplit.point_data_congr F _ _ (row_at (sh A) (sh B) (var 0)).eqSymm
      (row_regular (sh A) (sh B) (var 0) a b)

theorem regular (A B N : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] pointCN nameF (data A B N) :=
  GaussianNamedFiniteSumFamily.regular F body N (parameters A B) (rows_regular A B N hA hB)

theorem row_exponential (A B i : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] crossEquivalent (E F) constantF (exponentialInputData F (rowData A B i))
      (GaussianBarnesCanonicalFactor.powerValue (center A B) B (succ i)) := by
  let a := shiftedNumerator A B i
  let b := B*succ i
  let k := succ i
  have hb := positive_product _ _ hB (zero_lt_succ i)
  have hr := original_integer_exponential k a b b a (row_source a b (shifted_positive A B i hA) hb)
  have point := (GaussianEulerDecayFactorBounds.fraction_is_radius_point a b hb).eqTrans (base_at A B i hB).eqSymm
  have power := (actual_rational_power a b k hb).eqSymm.eqTrans (congrAp2 powerF (.eqRefl k) point)
  exact GaussianGammaCompactCutoffAlignment.cross_data_congr (E F) constantF _ _ _ _ (.eqRefl _) power hr

private theorem exponential_row_at (A B i : PTm n) :
    Γ ⊢[PRAAx] inst2 (exponentialBody F body) i (parameters A B) ≐ exponentialInputData F (rowData A B i) := by
  rw [exponentialBody_at]
  ipra_congr (exponentialInputData F (var 0) : PTm 1) with [row_at A B i] using [exponentialInputData]

private theorem equal_exponential_rows (A B N : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] equalRows (E F) constantF (exponentialBody F body) powerBody N
      (parameters A B) (GaussianBarnesCanonicalPolynomialShift.data (center A B) B) := by
  refine .allI (.impI ?_)
  let sh (t : PTm n) := Syn.shift t
  let Δ := lt (var 0) (sh N) :: Γ.map Fm.shift
  have a : Δ ⊢[PRAAx] le one (sh A) := by simpa [Fm.shift,Syn.shift,sh,Δ,one] using hA.shift.wk
  have b : Δ ⊢[PRAAx] le one (sh B) := by simpa [Fm.shift,Syn.shift,sh,Δ,one] using hB.shift.wk
  have e := row_exponential (sh A) (sh B) (var 0) a b
  have l := exponential_row_at (Γ := Δ) (sh A) (sh B) (var 0)
  have r := power_at (Γ := Δ) (var 0) (center (sh A) (sh B)) (sh B)
  simpa only [Syn.shift,sh,Δ,subst_parameters,GaussianBarnesCanonicalThirdLogarithmRows.subst_center,
    GaussianBarnesCanonicalPolynomialShift.subst_data] using
    GaussianGammaCompactCutoffAlignment.cross_data_congr (E F) constantF _ _ _ _ l.eqSymm r.eqSymm e

theorem exponential_kept_powers (A B N : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] crossEquivalent (E nameF) constantF (expData A B N) (powerProduct (center A B) B N) := by
  let x := parameters A B
  let y := GaussianBarnesCanonicalPolynomialShift.data (center A B) B
  let t := exponentialBody F body
  have rows := rows_regular A B N hA hB
  have first := exponential_product_cross F body N x rows
  have second := family_product_cross (E F) constantF t powerBody N x y
    (exponential_rows F body N x rows) (GaussianNamedFiniteConstantFolds.rows_regular powerBody N y)
    (equal_exponential_rows A B N hA hB)
  exact cross_trans _ _ _ _ _ _ first (cross_trans _ _ _ _ _ _ second
    (GaussianNamedFiniteConstantFolds.product_cross powerBody N y))

theorem actual_Barnes_kept_power_logarithm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (let A := var 0
     let B := var 1
     let N := var 2
     (le one A ⋏ le one B) ⟶ pointCN nameF (data A B N) ⋏
       crossEquivalent (E nameF) constantF (expData A B N) (powerProduct (center A B) B N)) :=
  closeUniv 3 (.impI (.andI (regular _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂)
    (exponential_kept_powers _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPositiveHeadLogarithm

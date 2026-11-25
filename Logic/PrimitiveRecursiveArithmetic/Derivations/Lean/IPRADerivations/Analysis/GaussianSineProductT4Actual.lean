import IPRADerivations.Analysis.GaussianSineProductT4SharpRow
import IPRADerivations.Analysis.GaussianSineProductSynchronizedMagnitude
import IPRADerivations.Analysis.GaussianSineNormalizedForwardProduct
import IPRADerivations.Analysis.GaussianSineProductT4Finite
import IPRADerivations.Analysis.GaussianSineProductNamedT3

/-!
# T4 at the actual cofinal sine-product observations

A finite sum pays for every head-row synchronization. The literal
ascending row is extended by unit factors so the existing finite T4
estimate applies. The same clock pays to compare the literal value
with the named factorization using the original sinc and sine names.
-/

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianSineProductT4Actual

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaEulerReflectionHead (sineProduct square_factor_at)
open GaussianInverseSquareProductComparison (rowErrors rowErrorDenominator)
open GaussianInverseSquareProductTail (factorBounds)
open GaussianNameArithmetic (multiplyModulus)
open GaussianNamedClearedSincMultipleAngle (rootFactorF rootFactorData root_factor_regular)
open GaussianNamedEvenSinePolynomial (sineDisk original_sine_bounds)
open GaussianNamedSineFromExponential (sine_regular)
open GaussianNamedSineTaylor (imaginaryF imaginary_input)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalFiniteProduct (qprod product_congr_bounded)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalReciprocal (qone)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianSineNormalizedForwardProduct (rowBody forwardProduct agrees_with_backward)
open GaussianSineNormalizedSampleProduct (normalizedProduct)
open GaussianSineProductScaledArguments (nameF)
open GaussianSineProductSynchronizedRow (sincValue angleSineF angleSineData angleData actualFactor argument_input)
open GaussianSineProductT4Budget (halfIndex squareDenominator cutoff cutoff_le_half_index)
open GaussianSineProductT4SharpRow (actual_head_row prefactor_bound)
open GaussianSineProductT6 (factorSize)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def sineSize (z R B K x : PTm n) : PTm n :=
  sineDisk (imaginaryF nameF) one (angleData z R B K x)
def sincData (z R B K x : PTm n) : PTm n := GaussianNamedSinc.data nameF one (angleData z R B K x)
def productData (z R B K x : PTm n) : PTm n := rootFactorData nameF (halfIndex R K) one (angleData z R B K x) x
def namedCost (z R B K x : PTm n) : PTm n :=
  (multiplyModulus (GaussianNamedSinc.nameF nameF) (rootFactorF nameF) (sincData z R B K x) (productData z R B K x)+one)+
    num 4*GaussianSineNormalizedSampleName.budget (halfIndex R K) (sineSize z R B K x)

def headCostData (z R B K x : PTm n) : PTm n := pairT z (pairT R (pairT B (pairT K x)))
def headCostAt (z R B K x i : PTm n) : PTm n :=
  GaussianSineProductSynchronizedRow.budget z R B K i x*rowErrorDenominator (squareDenominator R K) i
def headCostBody : PTm 2 := headCostAt (fstT (var 1)) (fstT (sndT (var 1))) (fstT (sndT (sndT (var 1))))
  (fstT (sndT (sndT (sndT (var 1))))) (sndT (sndT (sndT (sndT (var 1))))) (var 0)
def headCost (z R B K x : PTm n) : PTm n := ap2 (sumF headCostBody) K (headCostData z R B K x)
def startingPrecision (z R B K x p : PTm n) : PTm n := p+headCost z R B K x+namedCost z R B K x
def cofinalClock (z R B K x p : PTm n) : PTm n :=
  GaussianSineProductSynchronizedMagnitude.clock z R B K x (startingPrecision z R B K x p)

@[simp] theorem subst_sineSize {l : ℕ} (σ : Fin n → PTm l) (z R B K x : PTm n) :
    Syn.subst σ (sineSize z R B K x) = sineSize (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ K)
      (Syn.subst σ x) := by simp [sineSize,one]
@[simp] theorem subst_namedCost {l : ℕ} (σ : Fin n → PTm l) (z R B K x : PTm n) :
    Syn.subst σ (namedCost z R B K x) = namedCost (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ K)
      (Syn.subst σ x) := by simp [namedCost,sincData,productData,rootFactorData,one]
@[simp] theorem subst_headCostAt {l : ℕ} (σ : Fin n → PTm l) (z R B K x i : PTm n) :
    Syn.subst σ (headCostAt z R B K x i) = headCostAt (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ K) (Syn.subst σ x) (Syn.subst σ i) := by simp [headCostAt,rowErrorDenominator]
@[simp] theorem subst_headCost {l : ℕ} (σ : Fin n → PTm l) (z R B K x : PTm n) :
    Syn.subst σ (headCost z R B K x) = headCost (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ K)
      (Syn.subst σ x) := by simp [headCost,headCostData]
@[simp] theorem subst_cofinalClock {l : ℕ} (σ : Fin n → PTm l) (z R B K x p : PTm n) :
    Syn.subst σ (cofinalClock z R B K x p) = cofinalClock (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ K) (Syn.subst σ x) (Syn.subst σ p) := by simp [cofinalClock,startingPrecision]

private theorem head_cost_body_at (z R B K x i : PTm n) :
    Γ ⊢[PRAAx] inst2 headCostBody i (headCostData z R B K x) ≐ headCostAt z R B K x i := by
  let u := headCostData z R B K x
  have t1 : Γ ⊢[PRAAx] sndT u ≐ pairT R (pairT B (pairT K x)) := snd_pair _ _
  have t2 := (congrSnd t1).eqTrans (snd_pair _ _)
  have t3 := (congrSnd t2).eqTrans (snd_pair _ _)
  simpa [headCostBody,LeanProofs.IPRA.inst2,u] using Prf.eqCongr (Γ := Γ) (Ax := PRAAx)
    (headCostAt (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6)
    (σ := ![fstT u,fstT (sndT u),fstT (sndT (sndT u)),fstT (sndT (sndT (sndT u))),
      sndT (sndT (sndT (sndT u))),i])
    (σ' := ![z,R,B,K,x,i]) (fun j => by
      fin_cases j
      · exact fst_pair _ _
      · exact (congrFst t1).eqTrans (fst_pair _ _)
      · exact (congrFst t2).eqTrans (fst_pair _ _)
      · exact (congrFst t3).eqTrans (fst_pair _ _)
      · exact (congrSnd t3).eqTrans (snd_pair _ _)
      · exact .eqRefl _)

theorem head_cost_at (z R B K x i : PTm n) (hi : Γ ⊢[PRAAx] lt i K) :
    Γ ⊢[PRAAx] le (headCostAt z R B K x i) (headCost z R B K x) :=
  le_congr (head_cost_body_at z R B K x i) (.eqRefl _)
    (term_le_sum headCostBody (x := headCostData z R B K x) hi)

theorem clock_later (z R B K x p : PTm n) : Γ ⊢[PRAAx] le p (cofinalClock z R B K x p) :=
  le_trans (le_trans (le_add_right _ _) (le_add_right _ _)) (GaussianSineProductSynchronizedMagnitude.clock_later _ _ _ _ _ _)

theorem clock_head (z R B K x i p : PTm n) (hi : Γ ⊢[PRAAx] lt i K) :
    Γ ⊢[PRAAx] le (headCostAt z R B K x i) (unit (cofinalClock z R B K x p)) :=
  le_trans (head_cost_at z R B K x i hi) (le_trans (le_trans (le_add_left _ _) (le_add_right _ _))
    (le_trans (GaussianSineProductSynchronizedMagnitude.clock_later _ _ _ _ _ _)
      (LeanProofs.IPRA.Foundations.DyadicGain.amplitude_absorb _)))

theorem clock_named (z R B K x p : PTm n) :
    Γ ⊢[PRAAx] le (namedCost z R B K x*unit p) (unit (cofinalClock z R B K x p)) := by
  let T := namedCost z R B K x
  have l : Γ ⊢[PRAAx] le (p+T) (startingPrecision z R B K x p) :=
    le_of_eq_add (d := headCost z R B K x) (by unfold startingPrecision; dsimp only [T]; ipra_ring)
  have h := le_mul_mono (le_refl (unit p)) (LeanProofs.IPRA.Foundations.DyadicGain.amplitude_absorb (Γ := Γ) T)
  exact le_trans (le_congr (mul_comm _ _) (pw_add two p T).eqSymm h)
    (GaussianExponentialReference.unit_monotone (le_trans l (GaussianSineProductSynchronizedMagnitude.clock_later _ _ _ _ _ _)))

def sineAt (z R B K x p : PTm n) : PTm n := ap2 angleSineF p (angleSineData z R B K x)
def forwardData (z R B K x p : PTm n) : PTm n :=
  GaussianSineNormalizedSampleProduct.data (GaussianSineSampleRootGuards.clock p (halfIndex R K)) (halfIndex R K) x
    (sineAt z R B K x p)
def rowData (z R B K x p : PTm n) : PTm n := pairT (halfIndex R K) (forwardData z R B K x p)
def paddedRow : PTm 2 := RationalArithmetic.select (sg (monus (fstT (var 1)) (var 0))) qone
  (inst2 rowBody (var 0) (sndT (var 1)))
def synchronizedValue (z R B K x p : PTm n) : PTm n :=
  qmul (sincValue p (angleData z R B K x))
    (forwardProduct (GaussianSineSampleRootGuards.clock p (halfIndex R K)) (halfIndex R K) x (sineAt z R B K x p))
def cofinalValue (z R B K x p : PTm n) : PTm n := synchronizedValue z R B K x (cofinalClock z R B K x p)

@[simp] theorem subst_sineAt {l : ℕ} (σ : Fin n → PTm l) (z R B K x p : PTm n) :
    Syn.subst σ (sineAt z R B K x p) = sineAt (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ K)
      (Syn.subst σ x) (Syn.subst σ p) := by simp [sineAt]
@[simp] theorem subst_forwardData {l : ℕ} (σ : Fin n → PTm l) (z R B K x p : PTm n) :
    Syn.subst σ (forwardData z R B K x p) = forwardData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ K)
      (Syn.subst σ x) (Syn.subst σ p) := by simp [forwardData,GaussianSineNormalizedSampleProduct.data]
@[simp] theorem subst_rowData {l : ℕ} (σ : Fin n → PTm l) (z R B K x p : PTm n) :
    Syn.subst σ (rowData z R B K x p) = rowData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ K)
      (Syn.subst σ x) (Syn.subst σ p) := by simp [rowData]
@[simp] theorem subst_synchronizedValue {l : ℕ} (σ : Fin n → PTm l) (z R B K x p : PTm n) :
    Syn.subst σ (synchronizedValue z R B K x p) = synchronizedValue (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ K) (Syn.subst σ x) (Syn.subst σ p) := by simp [synchronizedValue,sincValue,one]
@[simp] theorem subst_cofinalValue {l : ℕ} (σ : Fin n → PTm l) (z R B K x p : PTm n) :
    Syn.subst σ (cofinalValue z R B K x p) = cofinalValue (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ K) (Syn.subst σ x) (Syn.subst σ p) := by simp [cofinalValue]

private theorem padding_at (z R B K x p i : PTm n) :
    Γ ⊢[PRAAx] inst2 paddedRow i (rowData z R B K x p) ≐
      RationalArithmetic.select (sg (monus (halfIndex R K) i)) qone (inst2 rowBody i (forwardData z R B K x p)) := by
  let d := rowData z R B K x p
  have e := Prf.eqCongr (Γ := Γ) (Ax := PRAAx)
    (RationalArithmetic.select (sg (monus (var 0) (var 2))) qone (inst2 rowBody (var 2) (var 1)) : PTm 3)
      (σ := ![fstT d,sndT d,i]) (σ' := ![halfIndex R K,forwardData z R B K x p,i]) (fun j => by
        fin_cases j
        · exact fst_pair _ _
        · exact snd_pair _ _
        · exact .eqRefl _)
  change Γ ⊢[PRAAx] Syn.subst ![i,d] paddedRow ≐ _
  simpa only [paddedRow,RationalArithmetic.subst_select,sg,one,ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero,PTm.subst_monus,subst_fstT,subst_sndT,
    GaussianRationalReciprocal.subst_qone,subst_inst2,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using e

theorem row_forward_at (z R B K x p i : PTm n) (hi : Γ ⊢[PRAAx] lt i (halfIndex R K)) :
    Γ ⊢[PRAAx] inst2 paddedRow i (rowData z R B K x p) ≐ inst2 rowBody i (forwardData z R B K x p) := by
  have e : Γ ⊢[PRAAx] monus (halfIndex R K) i ≐ ConciseIPRA.PTm.succ (monus (halfIndex R K) (ConciseIPRA.PTm.succ i)) :=
    (congrMonus ((AnalyticNumberTheory.Totatives.split_lt hi).eqTrans (add_comm _ _)) (.eqRefl _)).eqTrans
      (add_monus' _ _)
  exact (padding_at z R B K x p i).eqTrans
    (RationalArithmetic.select_one _ _ _ ((LeanProofs.IPRA.AnalyticNumberTheory.Mobius.congrSg e).eqTrans (sg_succ _)))

theorem actual_row_at (z R B K x p i : PTm n) (hi : Γ ⊢[PRAAx] lt i (halfIndex R K)) :
    Γ ⊢[PRAAx] inst2 paddedRow i (rowData z R B K x p) ≐ actualFactor z R B K i x p :=
  (row_forward_at z R B K x p i hi).eqTrans (GaussianSineNormalizedForwardProduct.row_at _ _ _ _ i)

theorem padding_one (z R B K x p i : PTm n) (hi : Γ ⊢[PRAAx] le (halfIndex R K) i) :
    Γ ⊢[PRAAx] inst2 paddedRow i (rowData z R B K x p) ≐ qone :=
  (padding_at z R B K x p i).eqTrans
    (RationalArithmetic.select_zero _ _ _ ((LeanProofs.IPRA.AnalyticNumberTheory.Mobius.congrSg hi).eqTrans sg_zero))

theorem padded_product (z R B K x p : PTm n) :
    Γ ⊢[PRAAx] qprod paddedRow (halfIndex R K) (rowData z R B K x p) ≐
      forwardProduct (GaussianSineSampleRootGuards.clock p (halfIndex R K)) (halfIndex R K) x (sineAt z R B K x p) := by
  apply product_congr_bounded
  refine .allI (.impI ?_)
  have h := row_forward_at (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift K) (Syn.shift x) (Syn.shift p)
    (var 0) (Prf.hyp0 : (lt (var 0) (halfIndex (Syn.shift R) (Syn.shift K)) :: Γ.map Fm.shift) ⊢[PRAAx]
      lt (var 0) (halfIndex (Syn.shift R) (Syn.shift K)))
  change _ ⊢[PRAAx] inst2 paddedRow (var 0) (Syn.shift (rowData z R B K x p)) ≐
    inst2 rowBody (var 0) (Syn.shift (forwardData z R B K x p))
  simpa only [Syn.shift,subst_rowData,subst_forwardData,GaussianSineProductT4Budget.subst_halfIndex] using h

theorem padded_factor_bounds (z R B K x p : PTm n) (hR : Γ ⊢[PRAAx] le one R)
    (hK : Γ ⊢[PRAAx] le one K) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B))
    (hp : Γ ⊢[PRAAx] GaussianSineProductSynchronizedMagnitude.fine z R B K x p) :
    Γ ⊢[PRAAx] factorBounds paddedRow (rowData z R B K x p) (factorSize R) zero := by
  refine .allI ?_
  let Z := Syn.shift z
  let A := Syn.shift R
  let B' := Syn.shift B
  let N := Syn.shift K
  let X := Syn.shift x
  let P := Syn.shift p
  let i : PTm (n+1) := var 0
  let Δ := Γ.map Fm.shift
  have hr : Δ ⊢[PRAAx] le one A := by simpa [Δ,Fm.shift,Syn.shift,A,one] using hR.shift
  have hk : Δ ⊢[PRAAx] le one N := by simpa [Δ,Fm.shift,Syn.shift,N,one] using hK.shift
  have hb : Δ ⊢[PRAAx] le one B' := by simpa [Δ,Fm.shift,Syn.shift,B',one] using hB.shift
  have hz' : Δ ⊢[PRAAx] ComplexLogarithmRemainder.bounded Z (A*B') :=
    by simpa [Δ,Fm.shift,Syn.shift,Z,A,B'] using hz.shift
  have hp' : Δ ⊢[PRAAx] GaussianSineProductSynchronizedMagnitude.fine Z A B' N X P :=
    by simpa [Δ,Fm.shift,Syn.shift,Z,A,B',N,X,P] using hp.shift
  have h : Δ ⊢[PRAAx] distanceBounded (inst2 paddedRow i (rowData Z A B' N X P)) qone
      (factorSize A) (ConciseIPRA.PTm.succ i*ConciseIPRA.PTm.succ i) := by
    refine .orE (lt_or_le i (halfIndex A N)) ?_ ?_
    · exact distance_congr (actual_row_at Z A B' N X P i Prf.hyp0).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
        (GaussianSineProductSynchronizedMagnitude.factor_bound_at Z A B' N i X P hr.wk hk.wk hb.wk Prf.hyp0 hz'.wk hp'.wk)
    · have den := positive_product _ _ (zero_lt_succ (Γ := le (halfIndex A N) i :: Δ) i) (zero_lt_succ i)
      have h0 := GaussianRationalPowerDifference.distance_refl_zero qone _ den
      exact distance_congr (padding_one Z A B' N X P i Prf.hyp0).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
        (distance_radius_mono _ _ _ _ _ _ den den (le_congr (by ipra_ring) (.eqRefl _) (zero_le _)) h0)
  let j := Syn.shift (zero : PTm n)+i
  have e : Δ ⊢[PRAAx] i ≐ j := by simpa [j,Syn.shift] using (zero_add (Γ := Δ) i).eqSymm
  have hj : Δ ⊢[PRAAx] distanceBounded (inst2 paddedRow j (rowData Z A B' N X P)) qone
      (factorSize A) (ConciseIPRA.PTm.succ j*ConciseIPRA.PTm.succ j) :=
    distance_congr (congrInst2 paddedRow e (.eqRefl _)) (.eqRefl _) (.eqRefl _)
      (congrMul (congrSucc e) (congrSucc e)) h
  change Δ ⊢[PRAAx] distanceBounded (inst2 paddedRow j (Syn.shift (rowData z R B K x p))) qone
    (Syn.shift (factorSize R)) (ConciseIPRA.PTm.succ j*ConciseIPRA.PTm.succ j)
  simpa only [subst_rowData,GaussianSineProductT6.subst_factorSize,Syn.shift,Z,A,B',N,X,P] using hj

theorem head_row_errors (z R B K x p : PTm n) (hR : Γ ⊢[PRAAx] le one R)
    (hK : Γ ⊢[PRAAx] le one K) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) :
    Γ ⊢[PRAAx] rowErrors paddedRow GaussianGammaEulerReflectionHead.body (rowData z R B K x (cofinalClock z R B K x p))
      (pairT z B) (num 96*(R*R)) (R*R) (squareDenominator R K) K := by
  refine .allI (.impI ?_)
  let Z := Syn.shift z
  let A := Syn.shift R
  let B' := Syn.shift B
  let N := Syn.shift K
  let X := Syn.shift x
  let P := Syn.shift p
  let i : PTm (n+1) := var 0
  let t := cofinalClock Z A B' N X P
  let Δ := lt i N :: Γ.map Fm.shift
  have hr : Δ ⊢[PRAAx] le one A := by simpa [Δ,Fm.shift,Syn.shift,A,one] using hR.shift.wk
  have hk : Δ ⊢[PRAAx] le one N := by simpa [Δ,Fm.shift,Syn.shift,N,one] using hK.shift.wk
  have hb : Δ ⊢[PRAAx] le one B' := by simpa [Δ,Fm.shift,Syn.shift,B',one] using hB.shift.wk
  have hz' : Δ ⊢[PRAAx] ComplexLogarithmRemainder.bounded Z (A*B') :=
    by simpa [Δ,Fm.shift,Syn.shift,Z,A,B'] using hz.shift.wk
  have hi : Δ ⊢[PRAAx] lt i N := Prf.hyp0
  have hi' : Δ ⊢[PRAAx] lt i (halfIndex A N) := le_trans hi (cutoff_le_half_index A N hr hk)
  have bound := actual_head_row Z A B' N i X t hr hk hb hi hz' (clock_head Z A B' N X i P hi)
  simpa [rowErrors,Syn.shift,Z,A,B',N,X,P,i,t,Δ] using distance_congr
    (actual_row_at Z A B' N X t i hi').eqSymm (square_factor_at i Z B').eqSymm (.eqRefl _) (.eqRefl _) bound

theorem precision_at (z R B K x p : PTm n) (hR : Γ ⊢[PRAAx] le one R) (hK : Γ ⊢[PRAAx] le one K)
    (hB : Γ ⊢[PRAAx] le one B) (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B))
    (hcut : Γ ⊢[PRAAx] le (cutoff R p) K) :
    Γ ⊢[PRAAx] distanceBounded (cofinalValue z R B K x p) (sineProduct z B K) one (unit p) := by
  let q := cofinalClock z R B K x p
  let s := sincValue q (angleData z R B K x)
  let d := rowData z R B K x q
  have hp : Γ ⊢[PRAAx] GaussianSineProductSynchronizedMagnitude.fine z R B K x q :=
    GaussianSineProductSynchronizedMagnitude.clock_fine _ _ _ _ _ _
  have source : Γ ⊢[PRAAx] GaussianSineProductT4Finite.source paddedRow d s z R B K :=
    .andI (.andI (.andI hR hB) hK)
      (.andI (.andI hz (padded_factor_bounds z R B K x q hR hK hB hz hp))
        (.andI (head_row_errors z R B K x p hR hK hB hz) (prefactor_bound z R B K x q hR hK hB hz)))
  have comparison := GaussianSineProductT4Finite.precision_at paddedRow d s z R B K p source hcut
  exact distance_congr (qmul_congr (.eqRefl s) (padded_product z R B K x q)) (.eqRefl _) (.eqRefl _) (.eqRefl _) comparison

theorem named_error_at (z R B K x p : PTm n) (hR : Γ ⊢[PRAAx] le one R) (hK : Γ ⊢[PRAAx] le one K)
    (hB : Γ ⊢[PRAAx] le one B) (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 GaussianSineProductNamedT3.factoredF p
      (GaussianSineProductNamedT3.factoredDataAt z R B (halfIndex R K) x one)) (synchronizedValue z R B K x p)
      (namedCost z R B K x) (unit p) := by
  let J := halfIndex R K
  let a := angleData z R B K x
  let S := GaussianNamedSinc.nameF nameF
  let G := rootFactorF nameF
  let u := sincData z R B K x
  let v := productData z R B K x
  let C := sineSize z R B K x
  let A := GaussianSineNormalizedSampleName.budget J C
  let t := GaussianSineNormalizedSampleName.precision J C p
  let P := unit p
  let T := unit t
  have input := argument_input z R B K x hR hK hB hz
  have hu := GaussianNamedSinc.name_regular nameF one a input.andE₁
  have hv := root_factor_regular nameF J one a x input.andE₁
  have first := GaussianNameRingLaws.multiply_sample_error S G u v p hu hv
  have imag := imaginary_input nameF one a input.andE₁
  have regular := sine_regular (imaginaryF nameF) one a imag
  have samples := original_sine_bounds (imaginaryF nameF) one a imag
  have pair := GaussianSineNormalizedSampleName.product_pair angleSineF t p J C (angleSineData z R B K x) x regular samples
  have ht : Γ ⊢[PRAAx] le p t := le_add_right _ _
  have grow := GaussianExponentialReference.unit_monotone ht
  have hp := unit_positive (Γ := Γ) p
  have size : Γ ⊢[PRAAx] le (A*(T+P)*P) ((two*A)*(T*P)) := by
    ipra_le 𝔞 A*𝔞 P*sl grow
  have near := distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive t) hp) hp size pair
  have eq := GaussianSineNormalizedSampleName.product_at (Γ := Γ) angleSineF p J C (angleSineData z R B K x) x
  have forward := agrees_with_backward (Γ := Γ) (GaussianSineSampleRootGuards.clock p J) J x (sineAt z R B K x p)
  have cap : Γ ⊢[PRAAx] le (num 4*R) (GaussianArctangentDivisionAngles.modulus J) :=
    le_congr (.eqRefl _) (GaussianSineProductSynchronizedRow.modulus_eq R K).eqSymm
      (GaussianSineProductT4Budget.argument_disk R K hR hK)
  have sb := GaussianNamedSincQuadraticBounds.unit_disk_bound nameF one a (num 4*R) (GaussianArctangentDivisionAngles.modulus J)
    p (zero_lt_succ _) cap input.andE₂
  have second := GaussianApproximateInverseDistance.multiply_distance (sincValue p a) _ _ two (two*A) P hp sb
    (distance_congr eq.eqSymm forward (.eqRefl _) (.eqRefl _) near)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by
    unfold namedCost
    dsimp only [J,S,G,u,v,C,A]
    ipra_ring) (.eqRefl _) (distance_triangle_same _ _ _ _ _ _ hp first second)

theorem named_factored_distance (z R B K x p : PTm n) (hR : Γ ⊢[PRAAx] le one R) (hK : Γ ⊢[PRAAx] le one K)
    (hB : Γ ⊢[PRAAx] le one B) (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 GaussianSineProductNamedT3.factoredF (cofinalClock z R B K x p)
      (GaussianSineProductNamedT3.factoredDataAt z R B (halfIndex R K) x one)) (cofinalValue z R B K x p) one (unit p) :=
  distance_radius_mono _ _ _ _ _ _ (unit_positive _) (unit_positive _)
    (le_congr (.eqRefl _) (one_mul _).eqSymm (clock_named z R B K x p))
    (named_error_at z R B K x (cofinalClock z R B K x p) hR hK hB hz)

theorem actual_synchronized_T4_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (((le one (var 1) ⋏ le one (var 3)) ⋏
      (le one (var 2) ⋏ ComplexLogarithmRemainder.bounded (var 0) (var 1*var 2))) ⟶
      le (cutoff (var 1) (var 5)) (var 3) ⟶
      distanceBounded (cofinalValue (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
        (sineProduct (var 0) (var 2) (var 3)) one (unit (var 5))) :=
  closeUniv 6 (.impI (.impI (precision_at _ _ _ _ _ _ Prf.hyp1.andE₁.andE₁ Prf.hyp1.andE₁.andE₂
    Prf.hyp1.andE₂.andE₁ Prf.hyp1.andE₂.andE₂ Prf.hyp0)))

theorem actual_named_T4_synchronization_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (((le one (var 1) ⋏ le one (var 3)) ⋏
      (le one (var 2) ⋏ ComplexLogarithmRemainder.bounded (var 0) (var 1*var 2))) ⟶
      distanceBounded
        (ap2 GaussianSineProductNamedT3.factoredF (cofinalClock (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
          (GaussianSineProductNamedT3.factoredDataAt (var 0) (var 1) (var 2) (halfIndex (var 1) (var 3)) (var 4) one))
        (cofinalValue (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) one (unit (var 5))) :=
  closeUniv 6 (.impI (named_factored_distance _ _ _ _ _ _ Prf.hyp0.andE₁.andE₁ Prf.hyp0.andE₁.andE₂
    Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianSineProductT4Actual

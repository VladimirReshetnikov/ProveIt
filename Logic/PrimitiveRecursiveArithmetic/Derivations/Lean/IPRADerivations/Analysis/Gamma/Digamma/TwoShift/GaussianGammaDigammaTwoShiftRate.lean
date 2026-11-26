import IPRADerivations.Analysis.Gamma.Digamma.TwoShift.GaussianGammaDigammaTwoShiftWindow
import IPRADerivations.Analysis.Gamma.Digamma.TwoShift.Rational.GaussianGammaDigammaTwoShiftCofinalRate
import IPRADerivations.Analysis.LinearAlgebra.Determinants.GaussianDeterminantSignTransport

/-!
# The logarithmic rate of the original two-shift Gamma quotient

For encoded positive x and rational shifts α, β with absolute values
at most A, derive the named real interval
−4A(A+1)/x ≤ log(Γ(x+α)/(Γ(x+β)x^(α−β))) ≤ 4A(A+1)/x.
The rate and the quotient refer to the same original Gamma instances.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaDigammaTwoShiftCofinalRate (rawSample finiteRate logRate cofinal_rate)
open GaussianGammaDigammaTwoShiftFiniteRate (raw)
open GaussianGammaDigammaTwoShiftSecants (logSample upper_negative negative_mul)
open GaussianGammaDigammaTwoShiftWindow (input coefficient low width cost low_split high_split forward_raw positive_endpoint numerator_mono)
open GaussianHarmonicLogarithmName (sample)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (reversed_difference)
open GaussianRationalHorner (qadd qmul qzero ofGaussian_canonical positive_product)
open GaussianRationalMetric (qsub qnegative)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalSyntheticDivision (qadd_sub_cancel qmul_congr qsub_congr qmul_zero_left)
open GaussianStirlingGammaLogarithm (source)
open RationalValueBounds (upper upper_congr upper_of_order)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}
open GaussianGammaDigammaTwoShiftCofinalRate (subst_rawSample)

def budget (b c d A : PTm n) : PTm n := cost b c d A+cost b d c A

@[simp] theorem subst_budget {m : ℕ} (σ : Fin n → PTm m) (b c d A : PTm n) :
    Syn.subst σ (budget b c d A) = budget (Syn.subst σ b) (Syn.subst σ c) (Syn.subst σ d) (Syn.subst σ A) := by
  simp [budget,cost,low,width,GaussianGammaDigammaTwoShiftFiniteRate.leftError,GaussianGammaDigammaTwoShiftFiniteRate.rightError,
    GaussianGammaDigammaTwoShiftSecants.leftCost,GaussianGammaDigammaTwoShiftSecants.rightCost,
    GaussianStirlingGammaFractionalIncrementObservations.weightedCost,
    GaussianStirlingGammaFractionalIncrementObservations.scaleCost,GaussianNameRingLaws.three,two]

private theorem raw_data_congr (p a b c d c' d' : PTm n) (ec : Γ ⊢[PRAAx] c ≐ c') (ed : Γ ⊢[PRAAx] d ≐ d') :
    Γ ⊢[PRAAx] rawSample p a b c d ≐ rawSample p a b c' d' := by
  have e := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (rawSample (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
    (σ := ![p,a,b,c,d]) (σ' := ![p,a,b,c',d']) (fun i => by
      fin_cases i <;> first | exact ec | exact ed | exact .eqRefl _)
  simpa only [subst_rawSample,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] using e

private theorem coefficient_exact (b d r : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] GaussianGammaDigammaTwoShiftBinding.coefficient b (d+r) d ≐ fraction r b := by
  have ad := GaussianEulerPositivePowerChartCorrectedImage.fraction_sum d b r b hb hb
  have same := GaussianStirlingRationalTelescopers.fraction_same (d*b+r*b) (b*b) (d+r) b
    (GaussianRationalHorner.positive_product _ _ hb hb) hb (by ipra_ring)
  exact (qsub_congr (ad.eqTrans same).eqSymm (.eqRefl _)).eqTrans
    (qadd_sub_cancel _ _ (ofGaussian_canonical _ _ hb))

private theorem raw_positive_coefficient (p a u b r : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] rawSample p a b (u+b+r) (u+b) ≐ raw p a u b r :=
  qsub_congr (.eqRefl _) (qmul_congr (coefficient_exact b (u+b) r hb) (.eqRefl _))

private theorem reversed_raw (p a b c d : PTm n) : Γ ⊢[PRAAx] qnegative (rawSample p a b c d) ≐ rawSample p a b d c := by
  let g := logSample p c b
  let h := logSample p d b
  let l := sample p a b
  let x := qsub g h
  let w := GaussianGammaDigammaTwoShiftBinding.coefficient b c d
  let v := GaussianGammaDigammaTwoShiftBinding.coefficient b d c
  let y := qmul w l
  have eX : Γ ⊢[PRAAx] qnegative x ≐ qsub h g := reversed_difference g h
  have eV : Γ ⊢[PRAAx] qnegative w ≐ v := reversed_difference (fraction c b) (fraction d b)
  have eY : Γ ⊢[PRAAx] qnegative y ≐ qmul v l :=
    (GaussianRationalMatrixFiniteSums.negative_as_minusOne (Γ := Γ) y).eqTrans
      ((qmul_congr (.eqRefl _) (qmul_commutative w l)).eqTrans
        ((GaussianRationalMatrixFiniteSums.negative_as_minusOne (qmul l w)).eqSymm.eqTrans
          ((negative_mul l w).eqTrans ((qmul_congr (.eqRefl _) eV).eqTrans (qmul_commutative _ _)))))
  have invol := GaussianDeterminantSignTransport.negative_involution (Γ := Γ) y (GaussianRationalHorner.qmul_canonical _ _)
  have swap : Γ ⊢[PRAAx] qsub (qnegative x) (qnegative y) ≐ qsub y x :=
    (GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _) invol).eqTrans (GaussianReciprocalHorner.qadd_commutative _ _)
  exact (reversed_difference x y).eqTrans (swap.eqSymm.eqTrans (qsub_congr eX eY))

private theorem same_raw (p a b c : PTm n) : Γ ⊢[PRAAx] rawSample p a b c c ≐ qzero := by
  have e := GaussianCoefficientNormOrder.qsub_self (Γ := Γ) (logSample p c b)
  have w := GaussianCoefficientNormOrder.qsub_self (Γ := Γ) (fraction c b)
  exact (qsub_congr e ((qmul_congr w (.eqRefl _)).eqTrans (qmul_zero_left _))).eqTrans
    (GaussianCoefficientNormOrder.qsub_self qzero)

private theorem forward (p a b c d A : PTm n) (hs : Γ ⊢[PRAAx] input a b c d A)
    (h : Γ ⊢[PRAAx] lt d c) :
    Γ ⊢[PRAAx]
      (upper (fstT qzero) (fstT (rawSample p a b c d)) (coefficient b A*unit p+cost b c d A*a) (a*unit p) ⋏
       upper (fstT (rawSample p a b c d)) (fstT qzero) (coefficient b A*unit p+cost b c d A*a) (a*unit p)) := by
  have hb := hs.andE₁.andE₂
  have hbase := hs.andE₂.andE₂.andE₁
  have hd := hs.andE₂.andE₂.andE₂.andE₂
  have ec := high_split a b A c d hbase hd (le_of_lt h)
  have ed := low_split a b A d hbase hd
  have e := (raw_positive_coefficient p a (low b d) b (width c d) hb).eqSymm.eqTrans (raw_data_congr p a b _ _ c d ec ed)
  have rate := forward_raw p a b c d A hs h
  exact .andI (upper_congr (.eqRefl _) (congrFst e) (.eqRefl _) (.eqRefl _) rate.andE₁)
    (upper_congr (congrFst e) (.eqRefl _) (.eqRefl _) (.eqRefl _) rate.andE₂)

private theorem row (p a b c d A : PTm n) (hs : Γ ⊢[PRAAx] input a b c d A) :
    Γ ⊢[PRAAx]
      (upper (fstT qzero) (fstT (rawSample p a b c d)) (coefficient b A*unit p+budget b c d A*a) (a*unit p) ⋏
       upper (fstT (rawSample p a b c d)) (fstT qzero) (coefficient b A*unit p+budget b c d A*a) (a*unit p)) := by
  let K := coefficient b A*unit p+budget b c d A*a
  let D := a*unit p
  let r := rawSample p a b c d
  have fwd {Δ : List (Fm PTm n)} (h : Δ ⊢[PRAAx] input a b c d A) (hlt : Δ ⊢[PRAAx] lt d c) :
      Δ ⊢[PRAAx] (upper (fstT qzero) (fstT r) K D ⋏ upper (fstT r) (fstT qzero) K D) := by
    have rate := forward p a b c d A h hlt
    have hD := positive_product _ _ h.andE₁.andE₁ (unit_positive p)
    have widen : Δ ⊢[PRAAx] le (coefficient b A*unit p+cost b c d A*a) K :=
      le_of_eq_add (d := cost b d c A*a) (by unfold K budget; ipra_ring)
    exact .andI (numerator_mono _ _ _ _ _ hD widen rate.andE₁)
      (numerator_mono _ _ _ _ _ hD widen rate.andE₂)
  have backward {Δ : List (Fm PTm n)} (h : Δ ⊢[PRAAx] input a b c d A) (hlt : Δ ⊢[PRAAx] lt c d) :
      Δ ⊢[PRAAx] (upper (fstT qzero) (fstT r) K D ⋏ upper (fstT r) (fstT qzero) K D) := by
    have hs' : Δ ⊢[PRAAx] input a b d c A := .andI h.andE₁ (.andI h.andE₂.andE₁ (.andI h.andE₂.andE₂.andE₁
      (.andI h.andE₂.andE₂.andE₂.andE₂ h.andE₂.andE₂.andE₂.andE₁)))
    have t := forward p a b d c A hs' hlt
    have hD := positive_product _ _ h.andE₁.andE₁ (unit_positive p)
    have e := reversed_raw (Γ := Δ) p a b d c
    have nz : Δ ⊢[PRAAx] qnegative qzero ≐ qzero :=
      (GaussianRationalMatrixFiniteSums.negative_as_minusOne _).eqTrans (GaussianRationalSyntheticDivision.qmul_zero_right _)
    have w : Δ ⊢[PRAAx] le (coefficient b A*unit p+cost b d c A*a) K :=
      le_of_eq_add (d := cost b c d A*a) (by unfold K budget; ipra_ring)
    have l := upper_congr (congrFst nz) (congrFst e) (.eqRefl _) (.eqRefl _) (upper_negative _ _ _ _ t.andE₂)
    have u := upper_congr (congrFst e) (congrFst nz) (.eqRefl _) (.eqRefl _) (upper_negative _ _ _ _ t.andE₁)
    exact .andI (numerator_mono _ _ _ _ _ hD w l)
      (numerator_mono _ _ _ _ _ hD w u)
  have coincident {Δ : List (Fm PTm n)} (e : Δ ⊢[PRAAx] c ≐ d) :
      Δ ⊢[PRAAx] (upper (fstT qzero) (fstT r) K D ⋏ upper (fstT r) (fstT qzero) K D) := by
    have same := (raw_data_congr p a b c d d d e (.eqRefl _)).eqTrans (same_raw p a b d)
    have o := upper_of_order (Γ := Δ) (fstT (qzero : PTm n)) (fstT qzero) K D (le_refl _)
    exact .andI (upper_congr (.eqRefl _) (congrFst same.eqSymm) (.eqRefl _) (.eqRefl _) o)
      (upper_congr (congrFst same.eqSymm) (.eqRefl _) (.eqRefl _) (.eqRefl _) o)
  refine .orE (le_total c d) ?_ ?_
  · exact .orE (lt_or_eq_of_le Prf.hyp0) (backward hs.wk.wk Prf.hyp0) (coincident Prf.hyp0)
  · exact .orE (lt_or_eq_of_le Prf.hyp0) (fwd hs.wk.wk Prf.hyp0) (coincident Prf.hyp0.eqSymm)

theorem two_shift_log_rate (a b c d A : PTm n) (hs : Γ ⊢[PRAAx] input a b c d A) :
    Γ ⊢[PRAAx] logRate a b c d (coefficient b A) := by
  have sb := hs.andE₁.andE₂
  have ha := hs.andE₁
  have H := hs.andE₂.andE₂.andE₁
  have hc := positive_endpoint a b A c sb H hs.andE₂.andE₂.andE₂.andE₁
  have hd := positive_endpoint a b A d sb H hs.andE₂.andE₂.andE₂.andE₂
  apply cofinal_rate a b c d (coefficient b A) (budget b c d A) ha hc hd
  have hx : Γ.map Fm.shift ⊢[PRAAx] input (Syn.shift a) (Syn.shift b) (Syn.shift c) (Syn.shift d) (Syn.shift A) :=
    by simpa only [Fm.shift,GaussianGammaDigammaTwoShiftWindow.subst_input,Syn.shift] using hs.shift
  refine .allI ?_
  simpa only [finiteRate,Syn.shift,GaussianGammaDigammaTwoShiftWindow.subst_coefficient,subst_budget] using
    row (var 0) (Syn.shift a) (Syn.shift b) (Syn.shift c) (Syn.shift d) (Syn.shift A) hx

theorem actual_original_Gamma_two_shift_logarithmic_rate_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
        logRate (var 0) (var 1) (var 2) (var 3) (coefficient (var 1) (var 4))) :=
  closeUniv 5 (.impI (two_shift_log_rate _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftRate

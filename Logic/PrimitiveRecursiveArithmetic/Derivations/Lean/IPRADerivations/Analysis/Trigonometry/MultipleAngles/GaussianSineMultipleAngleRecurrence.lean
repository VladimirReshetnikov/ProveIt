import IPRADerivations.Analysis.Names.Order.GaussianFastValueCut
import IPRADerivations.Analysis.Polynomials.Coefficients.GaussianRationalCoefficientScaling
import IPRADerivations.Analysis.RationalArithmetic.Complex.GaussianRationalInverseQuadraticAlgebra
import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.GaussianRationalSumAlgebra
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianPowers.GaussianRationalRoundedPower

/-!
# A zero-safe multiple-angle recurrence

The state holds the previous and current values of the three-term
recurrence, starting at zero and one. With inverse Gaussian points A
and B, its trace is A+B. The invariant compares both state components
times A−B with the corresponding differences of powers.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianSineMultipleAngleRecurrence

open_ipra
open GaussianRationalCoefficientScaling (qmul_add)
open GaussianRationalHorner (qzero qadd qmul canonical canonical_congr qmul_canonical)
open GaussianRationalMetric (qsub qsub_canonical)
open GaussianRationalPowerAlgebra (qmul_commutative power_one)
open GaussianRationalReciprocal (qone power power_zero power_succ power_canonical)
open GaussianRationalRoundedPower (multiplication_difference)
open GaussianRationalInverseQuadraticAlgebra (subtract_sum)
open GaussianRationalSumAlgebra (qadd_swap_tail)
open GaussianRationalSyntheticDivision (qadd_congr qsub_congr qmul_congr qmul_zero_right)
open GaussianReciprocalHorner (qmul_associative qmul_one_right qadd_commutative qsub_add_cancel)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def baseBody : PTm 1 := pairT qzero qone
def stepBody : PTm 3 := pairT (sndT (var 1))
  (qsub (qmul (var 2) (sndT (var 1))) (fstT (var 1)))
def stateF : PR 2 := rec2 baseBody stepBody
def state (S k : PTm n) : PTm n := ap2 stateF k S
def previous (S k : PTm n) : PTm n := fstT (state S k)
def value (S k : PTm n) : PTm n := sndT (state S k)
def difference (A B k : PTm n) : PTm n := qsub (power A k) (power B k)

ipra_subst state
ipra_subst previous
ipra_subst value
ipra_subst difference

theorem state_zero (S : PTm n) : Γ ⊢[PRAAx] state S zero ≐ pairT qzero qone := by
  simpa [state,stateF,baseBody] using rec2_zero (Γ := Γ) baseBody stepBody S

theorem state_succ (S k : PTm n) :
    Γ ⊢[PRAAx] state S (succ k) ≐ pairT (value S k) (qsub (qmul S (value S k)) (previous S k)) := by
  simpa only [state,stateF,stepBody,value,previous,subst_pairT,subst_sndT,subst_fstT,
    GaussianRationalMetric.subst_qsub,GaussianRationalHorner.subst_qmul,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons] using
    rec2_succ (Γ := Γ) baseBody stepBody k S

theorem previous_zero (S : PTm n) : Γ ⊢[PRAAx] previous S zero ≐ qzero :=
  (state_zero S).fstE

theorem value_zero (S : PTm n) : Γ ⊢[PRAAx] value S zero ≐ qone :=
  (state_zero S).sndE

theorem previous_succ (S k : PTm n) : Γ ⊢[PRAAx] previous S (succ k) ≐ value S k :=
  (state_succ S k).fstE

theorem value_succ (S k : PTm n) :
    Γ ⊢[PRAAx] value S (succ k) ≐ qsub (qmul S (value S k)) (previous S k) :=
  (state_succ S k).sndE

theorem value_one (S : PTm n) (hS : Γ ⊢[PRAAx] canonical S) : Γ ⊢[PRAAx] value S one ≐ S :=
  (value_succ S zero).eqTrans
    ((qsub_congr ((qmul_congr (.eqRefl _) (value_zero S)).eqTrans (qmul_one_right S hS)) (previous_zero S)).eqTrans
      (GaussianRationalReconstruction.qsub_zero_right S hS))

theorem recurrence (S k : PTm n) :
    Γ ⊢[PRAAx] value S (succ (succ k)) ≐ qsub (qmul S (value S (succ k))) (value S k) :=
  (value_succ S (succ k)).eqTrans (qsub_congr (.eqRefl _) (previous_succ S k))

private theorem trace_action (A B a : PTm n)
    (ha : Γ ⊢[PRAAx] canonical a) (hAB : Γ ⊢[PRAAx] qmul A B ≐ qone) :
    Γ ⊢[PRAAx] qsub (qmul (qadd A B) (qmul a A)) a ≐ qmul (qmul a A) A := by
  have inverse := (qmul_associative a A B).eqTrans
    ((qmul_congr (.eqRefl _) hAB).eqTrans (qmul_one_right a ha))
  have expand : Γ ⊢[PRAAx] qmul (qadd A B) (qmul a A) ≐ qadd (qmul (qmul a A) A) a :=
    (qmul_commutative (qadd A B) (qmul a A)).eqTrans
      ((qmul_add (qmul a A) A B).eqTrans (qadd_congr (.eqRefl _) inverse))
  exact (qsub_congr expand (.eqRefl _)).eqTrans (qsub_add_cancel _ _ (qmul_canonical _ _))

theorem power_difference_recurrence (A B k : PTm n) (hAB : Γ ⊢[PRAAx] qmul A B ≐ qone) :
    Γ ⊢[PRAAx] qsub (qmul (qadd A B) (difference A B (succ k))) (difference A B k) ≐
      difference A B (succ (succ k)) := by
  let a := power A k
  let b := power B k
  let S := qadd A B
  have hBA := (qmul_commutative B A).eqTrans hAB
  have left := trace_action A B a (power_canonical _ _) hAB
  have right : Γ ⊢[PRAAx] qsub (qmul S (qmul b B)) b ≐ qmul (qmul b B) B :=
    (qsub_congr (qmul_congr (qadd_commutative A B) (.eqRefl _)) (.eqRefl _)).eqTrans
      (trace_action B A b (power_canonical _ _) hBA)
  have advance := qsub_congr (power_succ (Γ := Γ) A k) (power_succ B k)
  have expand := (multiplication_difference (Γ := Γ) S (qmul a A) (qmul b B)).eqSymm
  have compare := qsub_congr
    (qmul_congr (power_succ (Γ := Γ) A k).eqSymm (.eqRefl A))
    (qmul_congr (power_succ (Γ := Γ) B k).eqSymm (.eqRefl B))
  exact (qsub_congr ((qmul_congr (.eqRefl S) advance).eqTrans expand) (.eqRefl _)).eqTrans
    ((GaussianFastValueCut.difference_identity (qmul S (qmul a A)) (qmul S (qmul b B)) a b).eqTrans
      ((qsub_congr left right).eqTrans (compare.eqTrans
        (qsub_congr (power_succ A (succ k)).eqSymm (power_succ B (succ k)).eqSymm))))

def invariant (A B k : PTm n) : Fm PTm n :=
  (qmul (qsub A B) (previous (qadd A B) k) ≐ difference A B k) ⋏
    (qmul (qsub A B) (value (qadd A B) k) ≐ difference A B (succ k))

ipra_subst invariant

private theorem invariant_zero (A B : PTm n) (hA : Γ ⊢[PRAAx] canonical A)
    (hB : Γ ⊢[PRAAx] canonical B) : Γ ⊢[PRAAx] invariant A B zero := by
  let S := qadd A B
  let d := qsub A B
  have differenceZero : Γ ⊢[PRAAx] difference A B zero ≐ qzero :=
    (qsub_congr (power_zero A) (power_zero B)).eqTrans (GaussianCoefficientNormOrder.qsub_self _)
  have differenceOne : Γ ⊢[PRAAx] difference A B one ≐ d :=
    qsub_congr (power_one A hA) (power_one B hB)
  exact .andI
    ((qmul_congr (.eqRefl _) (previous_zero S)).eqTrans
      ((qmul_zero_right d).eqTrans differenceZero.eqSymm))
    ((qmul_congr (.eqRefl _) (value_zero S)).eqTrans
      ((qmul_one_right d (qsub_canonical _ _)).eqTrans differenceOne.eqSymm))

private theorem invariant_succ (A B k : PTm n) (hAB : Γ ⊢[PRAAx] qmul A B ≐ qone)
    (h : Γ ⊢[PRAAx] invariant A B k) : Γ ⊢[PRAAx] invariant A B (succ k) := by
  let S := qadd A B
  let d := qsub A B
  let u := value S k
  let v := previous S k
  have middle : Γ ⊢[PRAAx] qmul d (qmul S u) ≐ qmul S (qmul d u) :=
    GaussianRationalPowerAlgebra.commute_nested d S u
  have expand := (multiplication_difference (Γ := Γ) d (qmul S u) v).eqSymm.eqTrans
    (qsub_congr middle (.eqRefl _))
  exact .andI ((qmul_congr (.eqRefl _) (previous_succ S k)).eqTrans h.andE₂)
    ((qmul_congr (.eqRefl _) (value_succ S k)).eqTrans
      (expand.eqTrans ((qsub_congr (qmul_congr (.eqRefl _) h.andE₂) h.andE₁).eqTrans
        (power_difference_recurrence A B k hAB))))

theorem invariant_all (A B k : PTm n) (hA : Γ ⊢[PRAAx] canonical A) (hB : Γ ⊢[PRAAx] canonical B)
    (hAB : Γ ⊢[PRAAx] qmul A B ≐ qone) : Γ ⊢[PRAAx] invariant A B k := by
  have all : Γ ⊢[PRAAx] .all (invariant (Syn.shift A) (Syn.shift B) (var 0)) := by
    ipra_qfind (⟨trivial,trivial⟩) [subst_invariant]
    · exact invariant_zero A B hA hB
    · have hs : Γ.map Fm.shift ⊢[PRAAx] qmul (Syn.shift A) (Syn.shift B) ≐ qone := by
        simpa only [Fm.shift,Fm.subst_eq,GaussianRationalHorner.subst_qmul,
          GaussianRationalReciprocal.subst_qone,Syn.shift] using hAB.shift
      exact invariant_succ _ _ _ hs.wk Prf.hyp0
  simpa only [subst_invariant,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k

theorem power_difference (A B k : PTm n) (hA : Γ ⊢[PRAAx] canonical A) (hB : Γ ⊢[PRAAx] canonical B)
    (hAB : Γ ⊢[PRAAx] qmul A B ≐ qone) :
    Γ ⊢[PRAAx] qmul (qsub A B) (value (qadd A B) k) ≐
      qsub (power A (succ k)) (power B (succ k)) :=
  (invariant_all A B k hA hB hAB).andE₂

theorem actual_sine_multiple_angle_trace_initial_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (value (qadd (var 0) (var 1)) zero ≐ qone ⋏
      (value (qadd (var 0) (var 1)) one ≐ qadd (var 0) (var 1))) :=
  closeUniv 2 (.andI (value_zero _) (value_one _ (GaussianRationalHorner.qadd_canonical _ _)))

theorem actual_sine_multiple_angle_recurrence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (value (var 0) zero ≐ qone ⋏
      (value (var 0) (succ (succ (var 1))) ≐
        qsub (qmul (var 0) (value (var 0) (succ (var 1)))) (value (var 0) (var 1)))) :=
  closeUniv 2 (.andI (value_zero _) (recurrence _ _))

theorem actual_sine_multiple_angle_difference_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((canonical (var 0) ⋏ canonical (var 1)) ⟶ (qmul (var 0) (var 1) ≐ qone) ⟶
      qmul (qsub (var 0) (var 1)) (value (qadd (var 0) (var 1)) (var 2)) ≐
        qsub (power (var 0) (succ (var 2))) (power (var 1) (succ (var 2)))) :=
  closeUniv 3 (.impI (.impI (power_difference _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))

def twoPoint : PTm n := qadd qone qone
def evenCoefficient (S : PTm n) : PTm n := qsub (qmul S S) twoPoint
def evenValue (S J : PTm n) : PTm n := value S (two*J)

private theorem value_index_congr (S : PTm n) {i k : PTm n} (h : Γ ⊢[PRAAx] i ≐ k) :
    Γ ⊢[PRAAx] value S i ≐ value S k :=
  congrSnd (congrAp2 stateF h (.eqRefl S))

private theorem double_point_product (u : PTm n) (hu : Γ ⊢[PRAAx] canonical u) :
    Γ ⊢[PRAAx] qmul twoPoint u ≐ qadd u u :=
  (qmul_commutative twoPoint u).eqTrans
    ((qmul_add u qone qone).eqTrans (qadd_congr (qmul_one_right u hu) (qmul_one_right u hu)))

private theorem even_coefficient_product (S u : PTm n) (hu : Γ ⊢[PRAAx] canonical u) :
    Γ ⊢[PRAAx] qmul (evenCoefficient S) u ≐ qsub (qmul (qmul S S) u) (qadd u u) :=
  (qmul_commutative (evenCoefficient S) u).eqTrans
    ((multiplication_difference u (qmul S S) twoPoint).eqSymm.eqTrans
      (qsub_congr (qmul_commutative _ _) ((qmul_commutative _ _).eqTrans (double_point_product u hu))))

/-- Taking two steps at a time changes the trace from S to S²−2. -/
theorem stride_two (S k : PTm n) :
    Γ ⊢[PRAAx] value S (succ (succ (succ (succ k)))) ≐
      qsub (qmul (evenCoefficient S) (value S (succ (succ k)))) (value S k) := by
  let u := value S k
  let v := value S (succ k)
  let w := value S (succ (succ k))
  let P := qmul (qmul S S) w
  have hw : Γ ⊢[PRAAx] canonical w :=
    canonical_congr (recurrence S k) (qsub_canonical _ _)
  have cancel : Γ ⊢[PRAAx] qmul S v ≐ qadd w u :=
    (GaussianRationalLinearProduct.add_sub_right u (qmul S v) (qmul_canonical _ _)).eqSymm.eqTrans
      ((qadd_congr (.eqRefl _) (recurrence S k).eqSymm).eqTrans (qadd_commutative _ _))
  have expand : Γ ⊢[PRAAx] qmul S (value S (succ (succ (succ k)))) ≐ qsub P (qadd w u) :=
    (qmul_congr (.eqRefl _) (recurrence S (succ k))).eqTrans
      ((multiplication_difference S (qmul S w) v).eqSymm.eqTrans
        (qsub_congr (qmul_associative S S w).eqSymm cancel))
  have left := (recurrence (Γ := Γ) S (succ (succ k))).eqTrans
    ((qsub_congr expand (.eqRefl _)).eqTrans (subtract_sum P (qadd w u) w))
  have right := (qsub_congr (even_coefficient_product S w hw) (.eqRefl u)).eqTrans
    (subtract_sum P (qadd w w) u)
  have regroup := qadd_swap_tail (Γ := Γ) w u w
  exact left.eqTrans ((qsub_congr (.eqRefl P) regroup).eqTrans right.eqSymm)

theorem even_zero (S : PTm n) : Γ ⊢[PRAAx] evenValue S zero ≐ qone :=
  (value_index_congr S (mul_zero two)).eqTrans (value_zero S)

theorem even_one (S : PTm n) (hS : Γ ⊢[PRAAx] canonical S) :
    Γ ⊢[PRAAx] evenValue S one ≐ qsub (qmul S S) qone :=
  (value_index_congr S (by ipra_ring : Γ ⊢[PRAAx] two*one ≐ two)).eqTrans
    ((recurrence S zero).eqTrans (qsub_congr (qmul_congr (.eqRefl _) (value_one S hS)) (value_zero S)))

theorem even_recurrence (S J : PTm n) :
    Γ ⊢[PRAAx] evenValue S (succ (succ J)) ≐ qsub (qmul (evenCoefficient S) (evenValue S (succ J))) (evenValue S J) := by
  have e₂ : Γ ⊢[PRAAx] two*succ J ≐ succ (succ (two*J)) := by ipra_ring
  have e₄ : Γ ⊢[PRAAx] two*succ (succ J) ≐ succ (succ (succ (succ (two*J)))) := by ipra_ring
  exact (value_index_congr S e₄).eqTrans
    ((stride_two S (two*J)).eqTrans (qsub_congr (qmul_congr (.eqRefl _) (value_index_congr S e₂.eqSymm)) (.eqRefl _)))

theorem actual_sine_multiple_angle_even_recurrence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (evenValue (var 0) zero ≐ qone ⋏
      (evenValue (var 0) (succ (succ (var 1))) ≐ qsub (qmul (evenCoefficient (var 0))
        (evenValue (var 0) (succ (var 1)))) (evenValue (var 0) (var 1)))) :=
  closeUniv 2 (.andI (even_zero _) (even_recurrence _ _))

end LeanProofs.IPRA.Analysis.GaussianSineMultipleAngleRecurrence

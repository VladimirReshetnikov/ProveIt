import IPRADerivations.Analysis.RationalArithmetic.Representations.RationalNormalForm
import IPRADerivations.Analysis.RationalArithmetic.RationalArithmetic
import IPRADerivations.AnalyticNumberTheory.RSA

/-!
# Source size bounds for the actual denominator-cleared rational matrix

Treat the original matrix as a list of rows with a numerical column count.
Use the original rational coordinate codes, the same positive product of all
decoded denominators, and the same actual integer output matrix. Bounds on
the original numerators and denominators give the cited bounds for both the
common denominator and each scaled integer coordinate.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalMatrixClearingBounds

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open RationalSupMetric
  (coordinate rationalNumerator rationalDenominator denominatorBody denominatorBody_at rowDenominator
    denominatorRows denominatorRows_at commonDenominator commonDenominator_one_le normalizedList
    normalized_coordinate normalized_coordinate_value cofactor cofactor_clears)
open LeanProofs.IPRA.Foundations.GapDecision (zabs zabs_congr)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def inputRow (v d H : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift d) ⟶
    le (zabs (rationalNumerator (Syn.shift v) (var 0))) (Syn.shift H) ⋏
      le (rationalDenominator (Syn.shift v) (var 0)) (Syn.shift H))

def inputMatrix (P d H : PTm n) : Fm PTm n := .all
  (lt (var 0) (length (Syn.shift P)) ⟶ inputRow (entry (Syn.shift P) (var 0)) (Syn.shift d) (Syn.shift H))

def entryCap (P d H : PTm n) : PTm n := pw H (succ (length P*d))

@[simp] theorem subst_inputRow {k : ℕ} (σ : Fin n → PTm k) (v d H : PTm n) :
    (inputRow v d H).subst σ = inputRow (Syn.subst σ v) (Syn.subst σ d) (Syn.subst σ H) := by
  simp only [inputRow,Fm.subst_all,Fm.subst_imp,Fm.subst_and,subst_lt,subst_le,
    Foundations.GapDecision.subst_zabs,RationalSupMetric.subst_rationalNumerator,RationalSupMetric.subst_rationalDenominator,
    Syn.subst_var,Syn.up_zero,Syn.up_succ,Syn.subst_shift,Syn.shift_subst]

ipra_subst inputMatrix [Syn.subst_shift, Syn.shift_subst]

ipra_subst entryCap

theorem input_row_at (P d H j : PTm n) (h : Γ ⊢[PRAAx] inputMatrix P d H) (hj : Γ ⊢[PRAAx] lt j (length P)) :
    Γ ⊢[PRAAx] inputRow (entry P j) d H := by
  have all : Γ ⊢[PRAAx] lt j (length P) ⟶ inputRow (entry P j) d H := by simpa [inputMatrix] using h.allE j
  exact .impE all hj

theorem input_coordinate_at (v d H i : PTm n) (h : Γ ⊢[PRAAx] inputRow v d H) (hi : Γ ⊢[PRAAx] lt i d) :
    Γ ⊢[PRAAx] le (zabs (rationalNumerator v i)) H ⋏ le (rationalDenominator v i) H := by
  have all : Γ ⊢[PRAAx] lt i d ⟶ le (zabs (rationalNumerator v i)) H ⋏ le (rationalDenominator v i) H := by
    simpa only [inputRow,Fm.subst_imp,Fm.subst_and,subst_lt,subst_le,Foundations.GapDecision.subst_zabs,
      RationalSupMetric.subst_rationalNumerator,RationalSupMetric.subst_rationalDenominator,
      Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE i
  exact .impE all hi

private theorem product_bound (f : PTm 2) (x N H : PTm n)
    (h : Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift N) ⟶ le (inst2 f (var 0) (Syn.shift x)) (Syn.shift H))) :
    Γ ⊢[PRAAx] le (ap2 (prodF f) N x) (pw H N) := by
  have all : Γ ⊢[PRAAx] .all (le (var 0) (Syn.shift N) ⟶
      le (ap2 (prodF f) (var 0) (Syn.shift x)) (pw (Syn.shift H) (var 0))) := by
    ipra_qfind (⟨le_QF _ _,le_QF _ _⟩) [subst_le, subst_ap2]
    · exact .impI (le_congr (prod_zero _ _).eqSymm (pw_zero _).eqSymm (le_refl one))
    · refine .impI ?_
      let k : PTm (n+1) := var 0
      let Δ := le (succ k) (Syn.shift N) ::
        (le k (Syn.shift N) ⟶ le (ap2 (prodF f) k (Syn.shift x)) (pw (Syn.shift H) k)) :: Γ.map Fm.shift
      have next : Δ ⊢[PRAAx] le (inst2 f k (Syn.shift x)) (Syn.shift H) := Prf.impE h.allOpen.wk.wk Prf.hyp0
      have previous : Δ ⊢[PRAAx] le (ap2 (prodF f) k (Syn.shift x)) (pw (Syn.shift H) k) :=
        Prf.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)
      exact le_congr (Probability.ProductReplacement.prod_succ' _ _ _).eqSymm (pw_succ _ _).eqSymm
        (le_mul_mono previous next)
  have atN : Γ ⊢[PRAAx] le N N ⟶ le (ap2 (prodF f) N x) (pw H N) := by
    simpa only [Fm.subst_imp,subst_le,subst_ap2,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N
  exact .impE atN (le_refl N)

theorem row_denominator_bound (v d H : PTm n) (h : Γ ⊢[PRAAx] inputRow v d H) :
    Γ ⊢[PRAAx] le (rowDenominator v d) (pw H d) := by
  apply product_bound
  refine .allI (.impI ?_)
  rw [denominatorBody_at]
  exact .andE₂ (.impE h.allOpen.wk Prf.hyp0)

theorem denominator_bound (P d H : PTm n) (h : Γ ⊢[PRAAx] inputMatrix P d H) :
    Γ ⊢[PRAAx] le (commonDenominator P d) (pw H (length P*d)) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] inputMatrix (Syn.shift P) (Syn.shift d) (Syn.shift H) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  have rows : Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift (length P)) ⟶
      le (inst2 denominatorRows (var 0) (Syn.shift (pairT d P))) (Syn.shift (pw H d))) := by
    refine .allI (.impI ?_)
    let P' := Syn.shift P
    let d' := Syn.shift d
    let H' := Syn.shift H
    let Δ := lt (var 0) (length P') :: Γ.map Fm.shift
    have rb : Δ ⊢[PRAAx] le (rowDenominator (entry P' (var 0)) d') (pw H' d') :=
      row_denominator_bound _ _ _ (input_row_at P' d' H' (var 0) hs.wk Prf.hyp0)
    simpa [Δ,P',d',H',Syn.shift] using le_congr (denominatorRows_at _ _ _).eqSymm (.eqRefl _) rb
  have bound := product_bound denominatorRows (pairT d P) (length P) (pw H d) rows
  exact le_congr (.eqRefl _) ((AnalyticNumberTheory.RSA.pw_mul H d (length P)).eqTrans
    (congrAp2 powF (mul_comm d (length P)) (.eqRefl H))) bound

theorem cofactor_bound (P d j i : PTm n) (hj : Γ ⊢[PRAAx] lt j (length P)) (hi : Γ ⊢[PRAAx] lt i d) :
    Γ ⊢[PRAAx] le (cofactor P d j i) (commonDenominator P d) := by
  have hp := RationalArgmin.denominator_positive (Γ := Γ) (entry (entry P j) i)
  exact le_congr (one_mul _) (cofactor_clears P d j i hj hi) (mul_le_mul_right (cofactor P d j i) hp)

theorem cleared_entry_bound (P d H j i : PTm n) (h : Γ ⊢[PRAAx] inputMatrix P d H)
    (hj : Γ ⊢[PRAAx] lt j (length P)) (hi : Γ ⊢[PRAAx] lt i d) :
    Γ ⊢[PRAAx] le (zabs (coordinate (entry (normalizedList P d) j) i)) (entryCap P d H) := by
  have abs := (zabs_congr (normalized_coordinate_value (Γ := Γ) P d j i hj hi)).eqTrans
    (RationalNormalForm.absolute_scale_right (rationalNumerator (entry P j) i) (cofactor P d j i))
  have bounds := input_coordinate_at (entry P j) d H i (input_row_at P d H j h hj) hi
  have hc := le_trans (cofactor_bound P d j i hj hi) (denominator_bound P d H h)
  exact le_congr abs.eqSymm ((mul_comm H _).eqTrans (pw_succ H _).eqSymm) (le_mul_mono (.andE₁ bounds) hc)

theorem cleared_representation (P d j i : PTm n) (hj : Γ ⊢[PRAAx] lt j (length P))
    (hi : Γ ⊢[PRAAx] lt i d) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (entry (entry P j) i) (coordinate (entry (normalizedList P d) j) i)
      (commonDenominator P d) := by
  apply ZT.derive
  have h := ZT.toZ_eq (normalized_coordinate (Γ := Γ) P d j i hj hi)
  simp only [ZT.toZ_mul,RationalSupMetric.rationalNumerator,
    RationalSupMetric.rationalDenominator] at h ⊢
  exact (_root_.mul_comm _ _).trans (h.trans (_root_.mul_comm _ _))

def output (P d : PTm n) : PTm n := pairT (commonDenominator P d) (normalizedList P d)
def outputF : PR 2 := PTm.toPR (output (var 0) (var 1))
def run (P d : PTm n) : PTm n := ap2 outputF P d

theorem program_at (P d : PTm n) : Γ ⊢[PRAAx] run P d ≐ output P d := by
  simpa [run,ap2,outputF,output] using toPR_eq (Γ := Γ) (output (var 0) (var 1) : PTm 2) ![P,d]

theorem returned_denominator (P d : PTm n) : Γ ⊢[PRAAx] fstT (run P d) ≐ commonDenominator P d :=
  (program_at P d).fstE

theorem returned_matrix (P d : PTm n) : Γ ⊢[PRAAx] sndT (run P d) ≐ normalizedList P d :=
  (program_at P d).sndE

theorem actual_common_denominator_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (inputMatrix (var 0) (var 1) (var 2) ⟶ le one (commonDenominator (var 0) (var 1)) ⋏
      le (commonDenominator (var 0) (var 1)) (pw (var 2) (length (var 0)*var 1))) :=
  closeUniv 3 (.impI (.andI (commonDenominator_one_le _ _) (denominator_bound _ _ _ Prf.hyp0)))

theorem actual_cleared_entry_representation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 2) (length (var 0)) ⟶ lt (var 3) (var 1) ⟶
      RationalArithmetic.represents (entry (entry (var 0) (var 2)) (var 3))
        (coordinate (entry (normalizedList (var 0) (var 1)) (var 2)) (var 3)) (commonDenominator (var 0) (var 1))) :=
  closeUniv 4 (.impI (.impI (cleared_representation (var 0) (var 1) (var 2) (var 3) Prf.hyp1 Prf.hyp0)))

theorem actual_cleared_entry_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (inputMatrix (var 0) (var 1) (var 2) ⟶ lt (var 3) (length (var 0)) ⟶ lt (var 4) (var 1) ⟶
      le (zabs (coordinate (entry (normalizedList (var 0) (var 1)) (var 3)) (var 4)))
        (entryCap (var 0) (var 1) (var 2))) :=
  closeUniv 5 (.impI (.impI (.impI (cleared_entry_bound (var 0) (var 1) (var 2) (var 3) (var 4)
    (.hyp (by simp)) Prf.hyp1 Prf.hyp0))))

theorem actual_returned_matrix_clearing_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (fstT (run (var 0) (var 1)) ≐ commonDenominator (var 0) (var 1) ⋏
      sndT (run (var 0) (var 1)) ≐ normalizedList (var 0) (var 1)) :=
  closeUniv 2 (.andI (returned_denominator _ _) (returned_matrix _ _))

end LeanProofs.IPRA.Analysis.RationalMatrixClearingBounds

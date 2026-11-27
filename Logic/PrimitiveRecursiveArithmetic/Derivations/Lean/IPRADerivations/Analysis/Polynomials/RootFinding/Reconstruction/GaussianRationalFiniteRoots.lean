import IPRADerivations.Analysis.Polynomials.Division.GaussianRationalSyntheticCoefficientValues
import IPRADerivations.Analysis.RationalArithmetic.Norms.GaussianProductNorm
import IPRADerivations.Foundations.BoundedSyntaxInduction

/-!
# A runtime-degree finite root bound over exact Gaussian rationals

The original coefficient and root lists and every degree/count/index are
numerical. A nonzero recoded leading coefficient supplies an honest exact
stored degree; arbitrary leading-zero trimming is a separate adapter. Root
list distinctness means nonzero actual normalized differences, rather than
inequality of possibly noncanonical raw point codes. The actual iterated
synthetic quotients preserve all later roots by derived field cancellation.
No quotient, degree bound or desired output invariant is an input contract.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalFiniteRoots

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalHorner
  (qzero qadd qmul canonical evaluate hornerF canonical_unique represents_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision
  (qone qadd_congr qmul_congr qzero_canonical quotient quotient_length)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qsub qsub_canonical)
open LeanProofs.IPRA.Analysis.GaussianRationalL1 (rawGaussian rawDen raw_den_positive raw_represents)
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal (normNumerator reciprocal reciprocal_identity)
open LeanProofs.IPRA.Analysis.GaussianTranslatedNonconstant (recode recode_congr recode_canonical recode_eq)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open LeanProofs.IPRA.Foundations.BoundedSyntax (BFm formula)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- A proved zero norm determines the actual zero field value. Original
canonicality is required only for this literal code recovery. -/
theorem canonical_zero_of_norm_zero (q : PTm n) (hq : Γ ⊢[PRAAx] canonical q)
    (h0 : Γ ⊢[PRAAx] normNumerator q ≐ zero) : Γ ⊢[PRAAx] q ≐ qzero := by
  have values := GaussianProductNorm.norm_zero_values (rawGaussian q) h0
  have same : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (rawGaussian q) ComplexLogarithmRemainder.zeroCode := by
    apply GaussianRootAlgebra.equal_of_values
    · exact values.1.trans GaussianRootAlgebra.re_zero.symm
    · exact values.2.trans GaussianRootAlgebra.im_zero.symm
  exact canonical_unique q qzero ComplexLogarithmRemainder.zeroCode (rawDen q) hq qzero_canonical (raw_den_positive q)
    (represents_congr (.eqRefl _) same (.eqRefl _) (raw_represents q)) (GaussianRationalHorner.zero_represents _)

theorem norm_positive_of_nonzero (q : PTm n) (hq : Γ ⊢[PRAAx] canonical q)
    (hne : Γ ⊢[PRAAx] neg (q ≐ qzero)) : Γ ⊢[PRAAx] le one (normNumerator q) := by
  refine .orE (zero_or_succ (normNumerator q)) ?_ ?_
  · exact .botE _ (.impE hne.wk (canonical_zero_of_norm_zero q hq.wk Prf.hyp0))
  · exact le_of_eq_add (d := pred (normNumerator q)) (Prf.hyp0.eqTrans (by ipra_ring))

/-- No-zero-divisors for the actual normalized arithmetic follows by its
computed reciprocal, not by a supplied host field/domain axiom. -/
theorem product_zero_reflect (d v : PTm n) (hd : Γ ⊢[PRAAx] canonical d)
    (hv : Γ ⊢[PRAAx] canonical v) (hne : Γ ⊢[PRAAx] neg (d ≐ qzero))
    (h0 : Γ ⊢[PRAAx] qmul d v ≐ qzero) : Γ ⊢[PRAAx] v ≐ qzero := by
  have inverse : Γ ⊢[PRAAx] qmul (reciprocal d) d ≐ qone :=
    (GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans (reciprocal_identity d (norm_positive_of_nonzero d hd hne))
  have back : Γ ⊢[PRAAx] qmul (reciprocal d) (qmul d v) ≐ v :=
    (GaussianReciprocalHorner.qmul_associative _ _ _).eqSymm.eqTrans
      ((qmul_congr inverse (.eqRefl _)).eqTrans
        ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans (GaussianReciprocalHorner.qmul_one_right v hv)))
  exact back.eqSymm.eqTrans ((qmul_congr (.eqRefl _) h0).eqTrans (GaussianRationalSyntheticDivision.qmul_zero_right _))

theorem quotient_root_transfer (C b c N : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hb : Γ ⊢[PRAAx] evaluate C b ≐ qzero) (hc : Γ ⊢[PRAAx] evaluate C c ≐ qzero)
    (hbc : Γ ⊢[PRAAx] neg (qsub c b ≐ qzero)) : Γ ⊢[PRAAx]
    evaluate (quotient C b N) c ≐ qzero := by
  have division := GaussianRationalSyntheticDivision.division_evaluation C b c N hC
  have product : Γ ⊢[PRAAx] qmul (qsub c b) (evaluate (quotient C b N) c) ≐ qzero :=
    ((GaussianReciprocalHorner.qadd_zero_right _ (GaussianRationalHorner.qmul_canonical _ _)).eqSymm.eqTrans
      ((qadd_congr (.eqRefl _) hb.eqSymm).eqTrans division.eqSymm)).eqTrans hc
  exact product_zero_reflect _ _ (qsub_canonical _ _) (GaussianRationalHorner.horner_canonical _ _ _) hbc product

def remaining (N i : PTm n) : PTm n := monus N i
def stageStep : PTm 5 := quotient (var 1) (entry (var 4) (var 0)) (remaining (var 3) (var 0))
def recursorF : PR 4 := recDef (var 0 : PTm 3) stageStep
def stage (C N R i : PTm n) : PTm n := PTm.app recursorF ![i,C,N,R]
def head (C : PTm n) : PTm n := recode (entry C zero)
def nonzeroHead (C : PTm n) : Fm PTm n := neg (head C ≐ qzero)
def roots (C R : PTm n) : Fm PTm n := .all
  (lt (var 0) (length (Syn.shift R)) ⟶ evaluate (Syn.shift C) (entry (Syn.shift R) (var 0)) ≐ qzero)
def distinctFrom (R i : PTm n) : Fm PTm n := .all
  (lt (var 0) (length (Syn.shift R)) ⟶ lt (Syn.shift i) (var 0) ⟶
    neg (qsub (entry (Syn.shift R) (var 0)) (entry (Syn.shift R) (Syn.shift i)) ≐ qzero))
def distinct (R : PTm n) : Fm PTm n := .all
  (lt (var 0) (length (Syn.shift R)) ⟶ distinctFrom (Syn.shift R) (var 0))
def laterRoots (C R i : PTm n) : Fm PTm n := .all
  (lt (var 0) (length (Syn.shift R)) ⟶ le (Syn.shift i) (var 0) ⟶
    evaluate (Syn.shift C) (entry (Syn.shift R) (var 0)) ≐ qzero)

ipra_subst remaining
ipra_subst stage
ipra_subst head
ipra_subst nonzeroHead
ipra_subst roots [Syn.subst_shift, Syn.shift_subst]
ipra_subst distinctFrom [Syn.subst_shift, Syn.shift_subst]
ipra_subst distinct [Syn.subst_shift, Syn.shift_subst]
ipra_subst laterRoots [Syn.subst_shift, Syn.shift_subst]

theorem stage_zero (C N R : PTm n) : Γ ⊢[PRAAx] stage C N R zero ≐ C := by
  have h := rec_zero_vecCons (Γ := Γ) (var 0 : PTm 3) stageStep ![C,N,R]
  simpa only [stage,recursorF,Syn.subst_var,Matrix.cons_val_zero] using h

theorem stage_succ (C N R i : PTm n) : Γ ⊢[PRAAx]
    stage C N R (succ i) ≐ quotient (stage C N R i) (entry R i) (remaining N i) := by
  have h := rec_succ_vecCons (Γ := Γ) (var 0 : PTm 3) stageStep i ![C,N,R]
  simpa only [stage,recursorF,stageStep,GaussianRationalSyntheticDivision.subst_quotient,subst_remaining,
    subst_entry,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] using h

theorem stage_index_congr (C N R : PTm n) {i j : PTm n} (h : Γ ⊢[PRAAx] i ≐ j) : Γ ⊢[PRAAx]
    stage C N R i ≐ stage C N R j := by
  apply congrApp recursorF
  intro t
  fin_cases t
  · exact h
  · exact .eqRefl _
  · exact .eqRefl _
  · exact .eqRefl _

theorem roots_at (C R i : PTm n) (h : Γ ⊢[PRAAx] roots C R) (hi : Γ ⊢[PRAAx] lt i (length R)) : Γ ⊢[PRAAx]
    evaluate C (entry R i) ≐ qzero := by
  have gate : Γ ⊢[PRAAx] lt i (length R) ⟶ evaluate C (entry R i) ≐ qzero := by
    simpa only [roots,Fm.subst_imp,Fm.subst_eq,subst_lt,subst_length,GaussianRationalHorner.subst_evaluate,
      subst_entry,GaussianRationalHorner.subst_qzero,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE i
  exact .impE gate hi

theorem later_roots_at (C R i j : PTm n) (h : Γ ⊢[PRAAx] laterRoots C R i)
    (hj : Γ ⊢[PRAAx] lt j (length R)) (hij : Γ ⊢[PRAAx] le i j) : Γ ⊢[PRAAx]
    evaluate C (entry R j) ≐ qzero := by
  have gate : Γ ⊢[PRAAx] lt j (length R) ⟶ le i j ⟶ evaluate C (entry R j) ≐ qzero := by
    simpa only [laterRoots,Fm.subst_imp,Fm.subst_eq,subst_lt,subst_le,subst_length,GaussianRationalHorner.subst_evaluate,
      subst_entry,GaussianRationalHorner.subst_qzero,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE j
  exact .impE (.impE gate hj) hij

theorem distinct_at (R i j : PTm n) (h : Γ ⊢[PRAAx] distinct R)
    (hi : Γ ⊢[PRAAx] lt i (length R)) (hj : Γ ⊢[PRAAx] lt j (length R)) (hij : Γ ⊢[PRAAx] lt i j) : Γ ⊢[PRAAx]
    neg (qsub (entry R j) (entry R i) ≐ qzero) := by
  have outer : Γ ⊢[PRAAx] lt i (length R) ⟶ distinctFrom R i := by
    simpa only [distinct,Fm.subst_imp,subst_lt,subst_length,subst_distinctFrom,
      Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE i
  have inner := (Prf.impE outer hi).allE j
  have gate : Γ ⊢[PRAAx] lt j (length R) ⟶ lt i j ⟶ neg (qsub (entry R j) (entry R i) ≐ qzero) := by
    simpa [distinctFrom,neg] using inner
  exact .impE (.impE gate hj) hij

theorem evaluate_congr {C E z w : PTm n} (hC : Γ ⊢[PRAAx] C ≐ E) (hz : Γ ⊢[PRAAx] z ≐ w) : Γ ⊢[PRAAx]
    evaluate C z ≐ evaluate E w := congrAp3 hornerF (congrFst hC) hC hz

theorem remaining_step (N i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    remaining N i ≐ succ (remaining N (succ i)) := GaussianRationalTranslationStages.remaining_step N i hi

theorem remaining_positive (N i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    le one (remaining N i) := GaussianRationalTranslationStages.remaining_positive N i hi

def lengthLaw (C N R i : PTm n) : Fm PTm n := le i N ⟶ length (stage C N R i) ≐ succ (remaining N i)
ipra_subst lengthLaw

theorem stage_length (C N R i : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx] length (stage C N R i) ≐ succ (remaining N i) := by
  have all : Γ ⊢[PRAAx] .all (lengthLaw (Syn.shift C) (Syn.shift N) (Syn.shift R) (var 0)) := by
    ipra_qfind (⟨le_QF _ _,trivial⟩) [subst_lengthLaw]
    · exact .impI (((congrFst (stage_zero C N R)).eqTrans hC).eqTrans (congrSucc (monus_zero N)).eqSymm).wk
    · refine .impI ?_
      exact (congrFst (stage_succ (Syn.shift C) (Syn.shift N) (Syn.shift R) (var 0))).eqTrans
        ((quotient_length _ _ _).eqTrans (remaining_step _ _ Prf.hyp0))
  have rule : Γ ⊢[PRAAx] lengthLaw C N R i := by
    simpa only [subst_lengthLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE i
  exact .impE rule hi

def headLaw (C N R i : PTm n) : Fm PTm n := le i N ⟶ head (stage C N R i) ≐ head C
ipra_subst headLaw

theorem stage_head (C N R i : PTm n) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    head (stage C N R i) ≐ head C := by
  have all : Γ ⊢[PRAAx] .all (headLaw (Syn.shift C) (Syn.shift N) (Syn.shift R) (var 0)) := by
    ipra_qfind (⟨le_QF _ _,trivial⟩) [subst_headLaw]
    · exact .impI (recode_congr (entry_congr (stage_zero C N R) (.eqRefl _))).wk
    · refine .impI ?_
      exact (recode_congr (entry_congr (stage_succ (Syn.shift C) (Syn.shift N) (Syn.shift R) (var 0)) (.eqRefl _))).eqTrans
        ((GaussianRationalSyntheticCoefficientValues.leading_coefficient _ _ _ (remaining_positive _ _ Prf.hyp0)).eqSymm.eqTrans
          (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)))
  have rule : Γ ⊢[PRAAx] headLaw C N R i := by
    simpa only [subst_headLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE i
  exact .impE rule hi

theorem later_roots_congr {C E : PTm n} (R i : PTm n) (hC : Γ ⊢[PRAAx] C ≐ E)
    (hRoots : Γ ⊢[PRAAx] laterRoots C R i) : Γ ⊢[PRAAx] laterRoots E R i := by
  have transport := Prf.eqSubst (Ax := PRAAx) (Γ := Γ) (laterRoots (var 0) (var 1) (var 2) : Fm PTm 3)
    ![C,R,i] ![E,R,i] (fun j => by fin_cases j; exact hC; exact .eqRefl _; exact .eqRefl _)
    (by simpa only [subst_laterRoots,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using hRoots)
  simpa only [subst_laterRoots,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using transport

theorem roots_to_later (C R : PTm n) (h : Γ ⊢[PRAAx] roots C R) : Γ ⊢[PRAAx] laterRoots C R zero := by
  refine .allI (.impI (.impI ?_))
  have hs : Γ.map Fm.shift ⊢[PRAAx] roots (Syn.shift C) (Syn.shift R) := by
    simpa only [Fm.shift,subst_roots,Syn.shift] using h.shift
  exact roots_at _ _ _ hs.wk.wk Prf.hyp1

/-- A local root-list transition is derived from the actual synthetic
identity and true field-value distinctness. It is not a quotient law input. -/
theorem later_roots_divide (C R N i : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hRoots : Γ ⊢[PRAAx] laterRoots C R i) (hDistinct : Γ ⊢[PRAAx] distinct R) : Γ ⊢[PRAAx]
    laterRoots (quotient C (entry R i) N) R (succ i) := by
  have cs : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C) ≐ succ (Syn.shift N) := by
    simpa only [Fm.shift,Fm.subst_eq,subst_length,ConciseIPRA.PTm.subst_succ,Syn.shift] using hC.shift
  have rs : Γ.map Fm.shift ⊢[PRAAx] laterRoots (Syn.shift C) (Syn.shift R) (Syn.shift i) := by
    simpa only [Fm.shift,subst_laterRoots,Syn.shift] using hRoots.shift
  have ds : Γ.map Fm.shift ⊢[PRAAx] distinct (Syn.shift R) := by
    simpa only [Fm.shift,subst_distinct,Syn.shift] using hDistinct.shift
  refine .allI (.impI (.impI ?_))
  let Δ := le (succ (Syn.shift i)) (var 0) :: lt (var 0) (length (Syn.shift R)) :: Γ.map Fm.shift
  have irange : Δ ⊢[PRAAx] lt (Syn.shift i) (length (Syn.shift R)) := lt_of_lt_of_le Prf.hyp0 (le_of_lt Prf.hyp1)
  have hiRoot := later_roots_at (Γ := Δ) (Syn.shift C) (Syn.shift R) (Syn.shift i) (Syn.shift i) rs.wk.wk irange (le_refl _)
  have hjRoot := later_roots_at (Γ := Δ) (Syn.shift C) (Syn.shift R) (Syn.shift i) (var 0) rs.wk.wk Prf.hyp1 (le_of_lt Prf.hyp0)
  have pair := distinct_at (Γ := Δ) (Syn.shift R) (Syn.shift i) (var 0) ds.wk.wk irange Prf.hyp1 Prf.hyp0
  simpa only [Δ,Syn.shift,GaussianRationalSyntheticDivision.subst_quotient,subst_entry,ConciseIPRA.PTm.subst_succ] using
    quotient_root_transfer (Γ := Δ) (Syn.shift C) (entry (Syn.shift R) (Syn.shift i)) (entry (Syn.shift R) (var 0))
      (Syn.shift N) cs.wk.wk hiRoot hjRoot pair

def rootsLaw (C N R i : PTm n) : Fm PTm n := le i N ⟶ laterRoots (stage C N R i) R i
def laterSyntax (C R i : PTm n) : BFm n := .all (length R)
  (.imp (.le (Syn.shift i) (var 0)) (.eq (evaluate (Syn.shift C) (entry (Syn.shift R) (var 0))) qzero))
def rootsSyntax (C N R i : PTm n) : BFm n := .imp (.le i N) (laterSyntax (stage C N R i) R i)
theorem roots_formula (C N R i : PTm n) : formula (rootsSyntax C N R i) = rootsLaw C N R i := by
  simp only [rootsSyntax,laterSyntax,formula,BFm.le,rootsLaw,laterRoots,Syn.shift,subst_length,le]
ipra_subst rootsLaw

/-- The bounded remaining-root formula is proved by real QF induction on
its compiled bit. The only global hypotheses are the original listed roots
and their original pairwise nonzero field differences. -/
theorem stage_roots (C N R i : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hRoots : Γ ⊢[PRAAx] roots C R) (hDistinct : Γ ⊢[PRAAx] distinct R)
    (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx] laterRoots (stage C N R i) R i := by
  have cs : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C) ≐ succ (Syn.shift N) := by
    simpa only [Fm.shift,Fm.subst_eq,subst_length,ConciseIPRA.PTm.subst_succ,Syn.shift] using hC.shift
  have ds : Γ.map Fm.shift ⊢[PRAAx] distinct (Syn.shift R) := by
    simpa only [Fm.shift,subst_distinct,Syn.shift] using hDistinct.shift
  have all : Γ ⊢[PRAAx] .all (rootsLaw (Syn.shift C) (Syn.shift N) (Syn.shift R) (var 0)) := by
    simpa only [roots_formula] using Foundations.BoundedSyntaxInduction.induction
      (rootsSyntax (Syn.shift C) (Syn.shift N) (Syn.shift R) (var 0))
      (Γ := Γ)
      (by
        simp only [roots_formula,subst_rootsLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
        exact .impI (later_roots_congr R zero (stage_zero C N R).eqSymm (roots_to_later C R hRoots)).wk)
      (by
        simp only [roots_formula,subst_rootsLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
        refine .impI ?_
        let I := rootsLaw (Syn.shift C) (Syn.shift N) (Syn.shift R) (var 0)
        let Δ := le (succ (var 0)) (Syn.shift N) :: I :: Γ.map Fm.shift
        have previous : Δ ⊢[PRAAx] laterRoots (stage (Syn.shift C) (Syn.shift N) (Syn.shift R) (var 0)) (Syn.shift R) (var 0) :=
          .impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)
        have shape := stage_length (Γ := Δ) (Syn.shift C) (Syn.shift N) (Syn.shift R) (var 0) cs.wk.wk
          (le_trans (le_succ_self _) Prf.hyp0)
        exact later_roots_congr (Syn.shift R) (succ (var 0)) (stage_succ (Syn.shift C) (Syn.shift N) (Syn.shift R) (var 0)).eqSymm
          (later_roots_divide _ _ _ _ shape previous ds.wk.wk))
  have rule : Γ ⊢[PRAAx] rootsLaw C N R i := by
    simpa only [subst_rootsLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE i
  exact .impE rule hi

/-- A supplied finite list of genuinely distinct field roots has length at
most the runtime exact degree. N=0 and the empty root list are included. -/
theorem finite_root_bound (C N R : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hHead : Γ ⊢[PRAAx] nonzeroHead C) (hRoots : Γ ⊢[PRAAx] roots C R)
    (hDistinct : Γ ⊢[PRAAx] distinct R) : Γ ⊢[PRAAx] le (length R) N := by
  refine .orE (lt_or_le N (length R)) ?_ Prf.hyp0
  let Δ := lt N (length R) :: Γ
  have constantShape : Δ ⊢[PRAAx] length (stage C N R N) ≐ one :=
    (stage_length C N R N hC.wk (le_refl _)).eqTrans (congrSucc (monus_self N))
  have zeroValue : Δ ⊢[PRAAx] evaluate (stage C N R N) (entry R N) ≐ qzero :=
    later_roots_at _ _ _ _ (stage_roots C N R N hC.wk hRoots.wk hDistinct.wk (le_refl _)) Prf.hyp0 (le_refl _)
  have bad : Δ ⊢[PRAAx] head C ≐ qzero :=
    (stage_head C N R N (le_refl _)).eqSymm.eqTrans
      ((GaussianRationalSyntheticCoefficientValues.singleton_evaluation _ _ constantShape).eqTrans zeroValue)
  exact .botE _ (.impE hHead.wk bad)

def input (C N R : PTm n) : Fm PTm n := (length C ≐ succ N) ⋏ (nonzeroHead C ⋏ (roots C R ⋏ distinct R))
def originalRootsSyntax (C R : PTm n) : BFm n := .all (length R)
  (.eq (evaluate (Syn.shift C) (entry (Syn.shift R) (var 0))) qzero)
def distinctFromSyntax (R i : PTm n) : BFm n := .all (length R)
  (.imp (.lt (Syn.shift i) (var 0)) (.not (.eq (qsub (entry (Syn.shift R) (var 0)) (entry (Syn.shift R) (Syn.shift i))) qzero)))
def distinctSyntax (R : PTm n) : BFm n := .all (length R) (distinctFromSyntax (Syn.shift R) (var 0))
def inputSyntax (C N R : PTm n) : BFm n := .and (.eq (length C) (succ N))
  (.and (.not (.eq (head C) qzero)) (.and (originalRootsSyntax C R) (distinctSyntax R)))
ipra_subst input

theorem input_formula (C N R : PTm n) : formula (inputSyntax C N R) = input C N R := by
  simp only [inputSyntax,originalRootsSyntax,distinctSyntax,distinctFromSyntax,input,formula,BFm.lt,BFm.le,
    nonzeroHead,roots,distinct,distinctFrom,neg,le,lt,Syn.shift,subst_length]

def checkerF : PR 3 := Foundations.BoundedSyntax.bitF (inputSyntax (var 0) (var 1) (var 2))
def check (C N R : PTm n) : PTm n := PTm.app checkerF ![C,N,R]
ipra_subst check

theorem eq_one_iff {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] Fm.iff (a ≐ one) (b ≐ one) :=
  .andI (.impI (h.wk.eqSymm.eqTrans Prf.hyp0)) (.impI (h.wk.eqTrans Prf.hyp0))

theorem checker_reflection (C N R : PTm n) : Γ ⊢[PRAAx] Fm.iff (check C N R ≐ one) (input C N R) := by
  have e := Foundations.BoundedSyntax.program_correct (inputSyntax (var 0) (var 1) (var 2)) ![C,N,R] (Γ := Γ)
  have r := Foundations.BoundedSyntax.bounded_reflection (inputSyntax (var 0) (var 1) (var 2)) ![C,N,R] (Γ := Γ)
  simpa only [check,checkerF,input_formula,subst_input,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using (eq_one_iff e).iffTrans r

theorem checker_sound (C N R : PTm n) (h : Γ ⊢[PRAAx] check C N R ≐ one) : Γ ⊢[PRAAx] le (length R) N := by
  have source := (checker_reflection C N R).iffMp h
  exact finite_root_bound C N R (.andE₁ source) (.andE₁ (.andE₂ source))
    (.andE₁ (.andE₂ (.andE₂ source))) (.andE₂ (.andE₂ (.andE₂ source)))

def quotientF : PR 4 := PTm.toPR (stage (var 0) (var 1) (var 2) (var 3))
def run (C N R i : PTm n) : PTm n := PTm.app quotientF ![C,N,R,i]
ipra_subst run

theorem program_at (C N R i : PTm n) : Γ ⊢[PRAAx] run C N R i ≐ stage C N R i := by
  simpa only [run,quotientF,subst_stage,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
      toPR_eq (Γ := Γ) (stage (var 0) (var 1) (var 2) (var 3) : PTm 4) ![C,N,R,i]
theorem returned_length (C N R i : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    length (run C N R i) ≐ succ (remaining N i) := (congrFst (program_at C N R i)).eqTrans (stage_length C N R i hC hi)
theorem returned_head (C N R i : PTm n) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx] head (run C N R i) ≐ head C :=
  (recode_congr (entry_congr (program_at C N R i) (.eqRefl _))).eqTrans (stage_head C N R i hi)
theorem returned_later_roots (C N R i : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hRoots : Γ ⊢[PRAAx] roots C R) (hDistinct : Γ ⊢[PRAAx] distinct R) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    laterRoots (run C N R i) R i := later_roots_congr R i (program_at C N R i).eqSymm (stage_roots C N R i hC hRoots hDistinct hi)

theorem runtime_finite_root_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (length (var 0) ≐ succ (var 1) ⟶ nonzeroHead (var 0) ⟶ roots (var 0) (var 2) ⟶ distinct (var 2) ⟶
      le (length (var 2)) (var 1)) :=
  closeUniv 3 (.impI (.impI (.impI (.impI (finite_root_bound _ _ _ hyp2.wk hyp2 Prf.hyp1 Prf.hyp0)))))
theorem actual_quotient_stage_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ stage (var 0) (var 1) (var 2) (var 3)) := closeUniv 4 (program_at _ _ _ _)
theorem actual_quotient_stage_length_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 1) ⟶ le (var 3) (var 1) ⟶
      length (run (var 0) (var 1) (var 2) (var 3)) ≐ succ (remaining (var 1) (var 3))) :=
  closeUniv 4 (.impI (.impI (returned_length _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_quotient_stage_head_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (var 3) (var 1) ⟶ head (run (var 0) (var 1) (var 2) (var 3)) ≐ head (var 0)) :=
  closeUniv 4 (.impI (returned_head _ _ _ _ Prf.hyp0))
theorem actual_remaining_root_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 1) ⟶ roots (var 0) (var 2) ⟶ distinct (var 2) ⟶ le (var 3) (var 1) ⟶
      laterRoots (run (var 0) (var 1) (var 2) (var 3)) (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (returned_later_roots _ _ _ _ hyp2.wk hyp2 Prf.hyp1 Prf.hyp0)))))
theorem actual_field_cancellation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (canonical (var 0) ⟶ canonical (var 1) ⟶ neg (var 0 ≐ qzero) ⟶ qmul (var 0) (var 1) ≐ qzero ⟶ var 1 ≐ qzero) :=
  closeUniv 2 (.impI (.impI (.impI (.impI (product_zero_reflect _ _ hyp2.wk hyp2 Prf.hyp1 Prf.hyp0)))))
theorem actual_synthetic_root_transfer_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 3) ⟶ evaluate (var 0) (var 1) ≐ qzero ⟶ evaluate (var 0) (var 2) ≐ qzero ⟶
      neg (qsub (var 2) (var 1) ≐ qzero) ⟶ evaluate (quotient (var 0) (var 1) (var 3)) (var 2) ≐ qzero) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (quotient_root_transfer _ _ _ _ hyp2.wk hyp2 Prf.hyp1 Prf.hyp0)))))
theorem actual_root_list_checker_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((Fm.iff (check (var 0) (var 1) (var 2) ≐ one) (input (var 0) (var 1) (var 2))) ⋏
      (check (var 0) (var 1) (var 2) ≐ one ⟶ le (length (var 2)) (var 1))) :=
  closeUniv 3 (.andI (checker_reflection _ _ _) (.impI (checker_sound _ _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianRationalFiniteRoots

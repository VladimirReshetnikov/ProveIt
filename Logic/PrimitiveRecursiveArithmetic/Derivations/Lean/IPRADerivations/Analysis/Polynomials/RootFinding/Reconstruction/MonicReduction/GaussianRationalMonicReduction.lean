import IPRADerivations.Analysis.Polynomials.RootFinding.Reconstruction.MonicReduction.GaussianRationalMonicCompanion
import IPRADerivations.Analysis.Polynomials.Division.GaussianRationalSyntheticCoefficientValues

/-!
# Actual runtime division by a monic rational polynomial

A numerical Horner loop produces both a quotient and a remainder. The
remainder always has D stored coefficients. The quotient deliberately keeps
one harmless leading zero: after M+1 input coefficients its length is M+2.
No minimal quotient degree is claimed. Its exact evaluator identity is
proved from the real companion update, not supplied as an input contract.
All lists, degrees, loop counters and query points are numerical. This is
an exact Q(i) reduction dependency; coefficient reconstruction, quotient
field interpretation and the norm/determinant construction remain separate.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalMonicReduction

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero qadd qmul canonical horner hornerF evaluate)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision
  (qone qadd_congr qmul_congr qzero_canonical qmul_zero_left qmul_zero_right qzero_add canonicalCoefficients)
open LeanProofs.IPRA.Analysis.GaussianRationalPolynomialBuffers
  (zeros zeros_length zeros_lookup zeros_evaluation appendZero append_length append_evaluation
    leftPad pad_length pad_evaluation added added_length added_lookup added_evaluation)
open LeanProofs.IPRA.Analysis.GaussianRationalMonicCompanion
  (lead companionY companion_length companion_canonical companion_evaluation)
open LeanProofs.IPRA.Analysis.GaussianTranslatedNonconstant (recode recode_canonical)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticCoefficientValues (qadd_recode_right)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def singleton (a : PTm n) : PTm n := sequence (var 1) one a
def constant (a L : PTm n) : PTm n := leftPad (singleton a) (pred L)
def quotientNext (Q R r : PTm n) : PTm n :=
  added (appendZero Q) (constant (lead R) (succ (succ r))) (succ (succ r))
def remainderNext (P R D a : PTm n) : PTm n := added (companionY P R D) (constant a D) D

def data (P S D : PTm n) : PTm n := pairT P (pairT S D)
def update (P S D r c : PTm n) : PTm n := pairT
  (quotientNext (fstT c) (sndT c) r) (remainderNext P (sndT c) D (entry S r))
def updateF : PR 5 := PTm.toPR (update (var 0) (var 1) (var 2) (var 3) (var 4))
def initial : PTm 1 := pairT (zeros one) (zeros (sndT (sndT (var 0))))
def stepBody : PTm 3 := PTm.app updateF
  ![fstT (var 2),fstT (sndT (var 2)),sndT (sndT (var 2)),var 0,var 1]
def stageF : PR 2 := rec2 initial stepBody
def stage (P S D r : PTm n) : PTm n := ap2 stageF r (data P S D)
def quotient (P S D r : PTm n) : PTm n := fstT (stage P S D r)
def remainder (P S D r : PTm n) : PTm n := sndT (stage P S D r)

ipra_subst singleton
ipra_subst constant
ipra_subst quotientNext
ipra_subst remainderNext
ipra_subst data
ipra_subst update
ipra_subst stage
ipra_subst quotient
ipra_subst remainder

theorem singleton_length (a : PTm n) : Γ ⊢[PRAAx] length (singleton a) ≐ one := Foundations.MasterCertificate.sequence_length _ _ _
theorem singleton_lookup (a : PTm n) : Γ ⊢[PRAAx] entry (singleton a) zero ≐ a := by
  simpa only [singleton,inst2,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,Matrix.tail_cons] using
    Foundations.MasterCertificate.sequence_decode (var 1 : PTm 2) (x := a) (le_refl one)
theorem singleton_evaluation (a z : PTm n) : Γ ⊢[PRAAx] evaluate (singleton a) z ≐ recode a :=
  (congrAp3 hornerF (singleton_length a) (.eqRefl _) (.eqRefl _)).eqTrans
    ((GaussianRationalHorner.horner_succ _ _ zero).eqTrans
      (qadd_congr ((qmul_congr (GaussianRationalHorner.horner_zero _ _) (.eqRefl _)).eqTrans (qmul_zero_left _))
        (singleton_lookup a)))
theorem constant_length (a L : PTm n) (hL : Γ ⊢[PRAAx] le one L) : Γ ⊢[PRAAx] length (constant a L) ≐ L :=
  (pad_length _ _).eqTrans ((congrAdd (.eqRefl _) (singleton_length a)).eqTrans
    ((succ_eq_add_one _).eqSymm.eqTrans (RationalIntegerNormalization.positive_form hL).eqSymm))
theorem constant_evaluation (a L z : PTm n) : Γ ⊢[PRAAx] evaluate (constant a L) z ≐ recode a :=
  (pad_evaluation _ _ _).eqTrans (singleton_evaluation a z)

theorem zeros_congr {L L' : PTm n} (h : Γ ⊢[PRAAx] L ≐ L') : Γ ⊢[PRAAx] zeros L ≐ zeros L' := by
  ipra_congr (zeros (var 0) : PTm 1) with [h]
theorem update_at (P S D r c : PTm n) : Γ ⊢[PRAAx] PTm.app updateF ![P,S,D,r,c] ≐ update P S D r c := by
  simpa only [updateF,subst_update,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] using
      toPR_eq (Γ := Γ) (update (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![P,S,D,r,c]

theorem stage_zero (P S D : PTm n) : Γ ⊢[PRAAx] stage P S D zero ≐ pairT (zeros one) (zeros D) := by
  have e := rec2_zero (Γ := Γ) initial stepBody (data P S D)
  simp only [initial,subst_pairT,GaussianRationalPolynomialBuffers.subst_zeros,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] at e
  exact e.eqTrans (congrPairT (.eqRefl _) (zeros_congr ((congrSnd (snd_pair P (pairT S D))).eqTrans (snd_pair S D))))

theorem stage_succ (P S D r : PTm n) : Γ ⊢[PRAAx] stage P S D (succ r) ≐ update P S D r (stage P S D r) := by
  have step := rec2_succ (Γ := Γ) initial stepBody r (data P S D)
  simp only [stepBody, ConciseIPRA.PTm.subst_app, subst_vecCons, subst_vecEmpty,
    subst_fstT, subst_sndT, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two] at step
  have field (i : Fin 3) : Γ ⊢[PRAAx]
      pairVectorField 2 (data P S D) i ≐ ![P,S,D] i :=
    pairVectorField_eq 2 ![P,S,D] (.eqRefl _) i
  exact step.eqTrans ((congrApp updateF (fun i => by
    fin_cases i
    · exact field 0
    · exact field 1
    · exact field 2
    · exact .eqRefl _
    · exact .eqRefl _)).eqTrans (update_at _ _ _ _ _))

theorem quotient_zero (P S D : PTm n) : Γ ⊢[PRAAx] quotient P S D zero ≐ zeros one :=
  (stage_zero P S D).fstE
theorem remainder_zero (P S D : PTm n) : Γ ⊢[PRAAx] remainder P S D zero ≐ zeros D :=
  (stage_zero P S D).sndE
theorem quotient_succ (P S D r : PTm n) : Γ ⊢[PRAAx]
    quotient P S D (succ r) ≐ quotientNext (quotient P S D r) (remainder P S D r) r :=
  (stage_succ P S D r).fstE
theorem remainder_succ (P S D r : PTm n) : Γ ⊢[PRAAx]
    remainder P S D (succ r) ≐ remainderNext P (remainder P S D r) D (entry S r) :=
  (stage_succ P S D r).sndE

theorem quotient_length (P S D r : PTm n) : Γ ⊢[PRAAx] length (quotient P S D r) ≐ succ r := by
  have all : Γ ⊢[PRAAx] .all (length (quotient (Syn.shift P) (Syn.shift S) (Syn.shift D) (var 0)) ≐ succ (var 0)) := by
    ipra_qfind [subst_length, subst_quotient]
    · exact (congrFst (quotient_zero P S D)).eqTrans (zeros_length one)
    · exact (congrFst (quotient_succ (Syn.shift P) (Syn.shift S) (Syn.shift D) (var 0))).eqTrans (added_length _ _ _)
  simpa only [Fm.subst_eq,subst_length,subst_quotient,ConciseIPRA.PTm.subst_succ,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE r

theorem remainder_length (P S D r : PTm n) : Γ ⊢[PRAAx] length (remainder P S D r) ≐ D := by
  have all : Γ ⊢[PRAAx] .all (length (remainder (Syn.shift P) (Syn.shift S) (Syn.shift D) (var 0)) ≐ Syn.shift D) := by
    ipra_qfind [subst_length, subst_remainder]
    · exact (congrFst (remainder_zero P S D)).eqTrans (zeros_length D)
    · exact (congrFst (remainder_succ (Syn.shift P) (Syn.shift S) (Syn.shift D) (var 0))).eqTrans (added_length _ _ _)
  simpa only [Fm.subst_eq,subst_length,subst_remainder,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE r

theorem evaluate_congr {C E z w : PTm n} (hC : Γ ⊢[PRAAx] C ≐ E) (hz : Γ ⊢[PRAAx] z ≐ w) : Γ ⊢[PRAAx]
    evaluate C z ≐ evaluate E w :=
  (GaussianRationalHorner.evaluate_program_at C z).eqSymm.eqTrans
    ((congrAp2 GaussianRationalHorner.evaluateF hC hz).eqTrans (GaussianRationalHorner.evaluate_program_at E w))

theorem quotient_next_evaluation (Q R r z : PTm n) (hQ : Γ ⊢[PRAAx] length Q ≐ succ r) : Γ ⊢[PRAAx]
    evaluate (quotientNext Q R r) z ≐ qadd (qmul (evaluate Q z) z) (lead R) :=
  (added_evaluation _ _ _ z ((append_length Q).eqTrans (congrSucc hQ))
    (constant_length _ _ (zero_lt_succ _))).eqTrans
      ((qadd_congr (append_evaluation Q z) (constant_evaluation _ _ z)).eqTrans (qadd_recode_right _ _))

theorem remainder_next_evaluation (P R D a z : PTm n) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    evaluate (remainderNext P R D a) z ≐ qadd (evaluate (companionY P R D) z) a :=
  (added_evaluation _ _ _ z (companion_length _ _ _) (constant_length _ _ hD)).eqTrans
    ((qadd_congr (.eqRefl _) (constant_evaluation _ _ z)).eqTrans (qadd_recode_right _ _))

/-- A finite ring rearrangement that uses the actual companion identity. -/
theorem reconstruction_step (p q r c l a z : PTm n)
    (h : Γ ⊢[PRAAx] qmul z r ≐ qadd (qmul p l) c) : Γ ⊢[PRAAx]
    qadd (qmul (qadd (qmul p q) r) z) a ≐
      qadd (qmul p (qadd (qmul q z) l)) (qadd c a) := by
  have first : Γ ⊢[PRAAx] qadd (qmul (qadd (qmul p q) r) z) a ≐
      qadd (qadd (qmul p (qmul q z)) (qadd (qmul p l) c)) a :=
    qadd_congr ((GaussianRationalPolynomialBuffers.distribute_right _ _ _).eqTrans
      (qadd_congr (GaussianReciprocalHorner.qmul_associative _ _ _)
        ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans h))) (.eqRefl _)
  exact first.eqTrans
    ((qadd_congr (GaussianRationalSumAlgebra.qadd_associative _ _ _).eqSymm (.eqRefl _)).eqTrans
      ((GaussianRationalSumAlgebra.qadd_associative _ _ _).eqTrans
        (qadd_congr (GaussianRationalCoefficientScaling.qmul_add _ _ _).eqSymm (.eqRefl _))))

theorem quotient_evaluation_succ (P S D r z : PTm n) : Γ ⊢[PRAAx]
    evaluate (quotient P S D (succ r)) z ≐
      qadd (qmul (evaluate (quotient P S D r) z) z) (lead (remainder P S D r)) :=
  (evaluate_congr (quotient_succ P S D r) (.eqRefl _)).eqTrans
    (quotient_next_evaluation _ _ r z (quotient_length P S D r))
theorem remainder_evaluation_succ (P S D r z : PTm n) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    evaluate (remainder P S D (succ r)) z ≐
      qadd (evaluate (companionY P (remainder P S D r) D) z) (entry S r) :=
  (evaluate_congr (remainder_succ P S D r) (.eqRefl _)).eqTrans
    (remainder_next_evaluation _ _ D _ z hD)

def reconstructionLaw (P S D z r : PTm n) : Fm PTm n :=
  horner S z r ≐ qadd (qmul (evaluate P z) (evaluate (quotient P S D r) z)) (evaluate (remainder P S D r) z)
ipra_subst reconstructionLaw

/-- The actual quotient and remainder reconstruct every numeric Horner
prefix. This is one genuine QF induction; neither a prefix invariant nor
an evaluator/reduction contract is an input. -/
theorem prefix_reconstruction (P S D z r : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hP : Γ ⊢[PRAAx] length P ≐ succ D) (hMonic : Γ ⊢[PRAAx] entry P zero ≐ qone) : Γ ⊢[PRAAx]
    reconstructionLaw P S D z r := by
  have ds : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift D) := by
    simpa only [Fm.shift,subst_le,Syn.shift,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using hD.shift
  have ps : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift P) ≐ succ (Syn.shift D) := by
    simpa only [Fm.shift,Fm.subst_eq,subst_length,Syn.shift,ConciseIPRA.PTm.subst_succ] using hP.shift
  have ms : Γ.map Fm.shift ⊢[PRAAx] entry (Syn.shift P) zero ≐ qone := by
    simpa only [Fm.shift,Fm.subst_eq,subst_entry,Syn.shift,ConciseIPRA.PTm.subst_zero,
      GaussianRationalSyntheticDivision.subst_qone] using hMonic.shift
  have all : Γ ⊢[PRAAx] .all (reconstructionLaw (Syn.shift P) (Syn.shift S) (Syn.shift D) (Syn.shift z) (var 0)) := by
    ipra_qfind [subst_reconstructionLaw]
    · have q : Γ ⊢[PRAAx] evaluate (quotient P S D zero) z ≐ qzero :=
        (evaluate_congr (quotient_zero P S D) (.eqRefl _)).eqTrans (zeros_evaluation _ _)
      have r : Γ ⊢[PRAAx] evaluate (remainder P S D zero) z ≐ qzero :=
        (evaluate_congr (remainder_zero P S D) (.eqRefl _)).eqTrans (zeros_evaluation _ _)
      have rhs : Γ ⊢[PRAAx]
          qadd (qmul (evaluate P z) (evaluate (quotient P S D zero) z)) (evaluate (remainder P S D zero) z) ≐ qzero :=
        (qadd_congr ((qmul_congr (.eqRefl _) q).eqTrans (qmul_zero_right _)) r).eqTrans
          (qzero_add qzero qzero_canonical)
      exact (GaussianRationalHorner.horner_zero S z).eqTrans rhs.eqSymm
    · let Δ := reconstructionLaw (Syn.shift P) (Syn.shift S) (Syn.shift D) (Syn.shift z) (var 0) :: Γ.map Fm.shift
      have actual := companion_evaluation (Γ := Δ) (Syn.shift P)
        (remainder (Syn.shift P) (Syn.shift S) (Syn.shift D) (var 0)) (Syn.shift D) (Syn.shift z)
        ds.wk ps.wk ms.wk (remainder_length _ _ _ _)
      exact (GaussianRationalHorner.horner_succ _ _ _).eqTrans
        ((qadd_congr (qmul_congr Prf.hyp0 (.eqRefl _)) (.eqRefl _)).eqTrans
          ((reconstruction_step _ _ _ _ _ _ _ actual).eqTrans
            (qadd_congr (qmul_congr (.eqRefl _) (quotient_evaluation_succ _ _ _ _ _).eqSymm)
              (remainder_evaluation_succ _ _ _ _ _ ds.wk).eqSymm)))
  simpa only [subst_reconstructionLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE r

/-- Generated zero and addition buffers are canonical independently of
original raw codes and list shapes. -/
theorem zeros_canonical (L : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (zeros L) := by
  refine .allI (.impI ?_)
  have h : lt (var 0) (length (Syn.shift (zeros L))) :: Γ.map Fm.shift ⊢[PRAAx] lt (var 0) (Syn.shift L) :=
    lt_congr (.eqRefl _) (zeros_length _) (by simpa only [Syn.shift,GaussianRationalPolynomialBuffers.subst_zeros] using Prf.hyp0)
  simpa only [Syn.shift,GaussianRationalPolynomialBuffers.subst_zeros] using
    GaussianRationalHorner.canonical_congr (zeros_lookup _ _ h) qzero_canonical

theorem added_canonical (C E L : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (added C E L) := by
  refine .allI (.impI ?_)
  have h : lt (var 0) (length (Syn.shift (added C E L))) :: Γ.map Fm.shift ⊢[PRAAx] lt (var 0) (Syn.shift L) :=
    lt_congr (.eqRefl _) (added_length _ _ _) (by simpa only [Syn.shift,GaussianRationalPolynomialBuffers.subst_added] using Prf.hyp0)
  simpa only [Syn.shift,GaussianRationalPolynomialBuffers.subst_added] using
    GaussianRationalHorner.canonical_congr (added_lookup _ _ _ _ h) (GaussianRationalHorner.qadd_canonical _ _)

theorem canonical_coefficients_congr {C E : PTm n} (h : Γ ⊢[PRAAx] C ≐ E)
    (hE : Γ ⊢[PRAAx] canonicalCoefficients E) : Γ ⊢[PRAAx] canonicalCoefficients C := by
  have p := Prf.eqSubst (Ax := PRAAx) (Γ := Γ) (canonicalCoefficients (var 0) : Fm PTm 1)
    ![E] ![C] (fun i => by fin_cases i; exact h.eqSymm) (by simpa using hE)
  simpa using p

theorem quotient_canonical (P S D r : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (quotient P S D r) := by
  refine .orE (zero_or_succ r) ?_ ?_
  · exact canonical_coefficients_congr
      ((congrFst (congrAp2 stageF Prf.hyp0 (.eqRefl _))).eqTrans (quotient_zero P S D)) (zeros_canonical one)
  · exact canonical_coefficients_congr
      ((congrFst (congrAp2 stageF Prf.hyp0 (.eqRefl _))).eqTrans (quotient_succ P S D (pred r)))
      (added_canonical _ _ _)

theorem remainder_canonical (P S D r : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (remainder P S D r) := by
  refine .orE (zero_or_succ r) ?_ ?_
  · exact canonical_coefficients_congr
      ((congrSnd (congrAp2 stageF Prf.hyp0 (.eqRefl _))).eqTrans (remainder_zero P S D)) (zeros_canonical D)
  · exact canonical_coefficients_congr
      ((congrSnd (congrAp2 stageF Prf.hyp0 (.eqRefl _))).eqTrans (remainder_succ P S D (pred r)))
      (added_canonical _ _ _)

def reducedQuotient (P S D M : PTm n) : PTm n := quotient P S D (succ M)
def reducedRemainder (P S D M : PTm n) : PTm n := remainder P S D (succ M)
def output (P S D M : PTm n) : PTm n := pairT (reducedQuotient P S D M) (reducedRemainder P S D M)
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (P S D M : PTm n) : PTm n := PTm.app outputF ![P,S,D,M]
ipra_subst reducedQuotient
ipra_subst reducedRemainder
ipra_subst output
ipra_subst run

theorem reduction_evaluation (P S D M z : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hP : Γ ⊢[PRAAx] length P ≐ succ D) (hMonic : Γ ⊢[PRAAx] entry P zero ≐ qone)
    (hS : Γ ⊢[PRAAx] length S ≐ succ M) : Γ ⊢[PRAAx]
    evaluate S z ≐ qadd (qmul (evaluate P z) (evaluate (reducedQuotient P S D M) z))
      (evaluate (reducedRemainder P S D M) z) :=
  (congrAp3 hornerF hS (.eqRefl _) (.eqRefl _)).eqTrans (prefix_reconstruction P S D z (succ M) hD hP hMonic)

theorem program_at (P S D M : PTm n) : Γ ⊢[PRAAx] run P S D M ≐ output P S D M := by
  simpa only [run,outputF,subst_output,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
      toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![P,S,D,M]
theorem returned_quotient (P S D M : PTm n) : Γ ⊢[PRAAx] fstT (run P S D M) ≐ reducedQuotient P S D M :=
  (program_at P S D M).fstE
theorem returned_remainder (P S D M : PTm n) : Γ ⊢[PRAAx] sndT (run P S D M) ≐ reducedRemainder P S D M :=
  (program_at P S D M).sndE
theorem returned_quotient_length (P S D M : PTm n) : Γ ⊢[PRAAx] length (fstT (run P S D M)) ≐ succ (succ M) :=
  (congrFst (returned_quotient P S D M)).eqTrans (quotient_length _ _ _ _)
theorem returned_remainder_length (P S D M : PTm n) : Γ ⊢[PRAAx] length (sndT (run P S D M)) ≐ D :=
  (congrFst (returned_remainder P S D M)).eqTrans (remainder_length _ _ _ _)
theorem returned_quotient_canonical (P S D M : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (fstT (run P S D M)) :=
  canonical_coefficients_congr (returned_quotient P S D M) (quotient_canonical _ _ _ _)
theorem returned_remainder_canonical (P S D M : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (sndT (run P S D M)) :=
  canonical_coefficients_congr (returned_remainder P S D M) (remainder_canonical _ _ _ _)
theorem returned_evaluation (P S D M z : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hP : Γ ⊢[PRAAx] length P ≐ succ D) (hMonic : Γ ⊢[PRAAx] entry P zero ≐ qone)
    (hS : Γ ⊢[PRAAx] length S ≐ succ M) : Γ ⊢[PRAAx]
    evaluate S z ≐ qadd (qmul (evaluate P z) (evaluate (fstT (run P S D M)) z))
      (evaluate (sndT (run P S D M)) z) :=
  (reduction_evaluation P S D M z hD hP hMonic hS).eqTrans
    (qadd_congr (qmul_congr (.eqRefl _) (evaluate_congr (returned_quotient P S D M).eqSymm (.eqRefl _)))
      (evaluate_congr (returned_remainder P S D M).eqSymm (.eqRefl _)))

theorem actual_prefix_reconstruction_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 2) ⟶ length (var 0) ≐ succ (var 2) ⟶ entry (var 0) zero ≐ qone ⟶
      reconstructionLaw (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (.impI (.impI (prefix_reconstruction _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))
theorem actual_monic_reduction_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 2) ⟶ length (var 0) ≐ succ (var 2) ⟶ entry (var 0) zero ≐ qone ⟶ length (var 1) ≐ succ (var 3) ⟶
      evaluate (var 1) (var 4) ≐ qadd (qmul (evaluate (var 0) (var 4))
        (evaluate (reducedQuotient (var 0) (var 1) (var 2) (var 3)) (var 4)))
          (evaluate (reducedRemainder (var 0) (var 1) (var 2) (var 3)) (var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (reduction_evaluation _ _ _ _ _ hyp2.wk hyp2 Prf.hyp1 Prf.hyp0)))))
theorem actual_monic_reduction_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((fstT (run (var 0) (var 1) (var 2) (var 3)) ≐ reducedQuotient (var 0) (var 1) (var 2) (var 3)) ⋏
      (sndT (run (var 0) (var 1) (var 2) (var 3)) ≐ reducedRemainder (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.andI (returned_quotient _ _ _ _) (returned_remainder _ _ _ _))
theorem actual_monic_reduction_shapes_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((length (fstT (run (var 0) (var 1) (var 2) (var 3))) ≐ succ (succ (var 3))) ⋏
      (length (sndT (run (var 0) (var 1) (var 2) (var 3))) ≐ var 2)) :=
  closeUniv 4 (.andI (returned_quotient_length _ _ _ _) (returned_remainder_length _ _ _ _))
theorem actual_monic_reduction_canonical_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((canonicalCoefficients (fstT (run (var 0) (var 1) (var 2) (var 3)))) ⋏
      (canonicalCoefficients (sndT (run (var 0) (var 1) (var 2) (var 3))))) :=
  closeUniv 4 (.andI (returned_quotient_canonical _ _ _ _) (returned_remainder_canonical _ _ _ _))
theorem actual_returned_reduction_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 2) ⟶ length (var 0) ≐ succ (var 2) ⟶ entry (var 0) zero ≐ qone ⟶ length (var 1) ≐ succ (var 3) ⟶
      evaluate (var 1) (var 4) ≐ qadd (qmul (evaluate (var 0) (var 4))
        (evaluate (fstT (run (var 0) (var 1) (var 2) (var 3))) (var 4)))
          (evaluate (sndT (run (var 0) (var 1) (var 2) (var 3))) (var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (returned_evaluation _ _ _ _ _ hyp2.wk hyp2 Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianRationalMonicReduction

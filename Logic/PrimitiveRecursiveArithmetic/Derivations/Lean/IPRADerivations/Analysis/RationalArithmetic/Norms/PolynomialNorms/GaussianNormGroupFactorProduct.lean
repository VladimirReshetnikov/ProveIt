import IPRADerivations.Analysis.Polynomials.Division.GaussianPolynomialRowQuotient
import IPRADerivations.Analysis.Polynomials.Products.GaussianRationalPolynomialProductDegree
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianPowers.GaussianRationalPowerNonzero

/-!
# Actual accumulated factors of the original numerical abscissa groups

The count is the actual prefix sum of the existing grouping size body.
The polynomial recursor multiplies the preceding actual product by the
actual repeated-root polynomial of the next original group. Its length,
canonical coefficients and monic head are derived from real producers.
All list codes, grouping data and group counters are numerical. This
constructs the factor product, not a quotient or global divisibility law.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianNormGroupFactorProduct

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero qmul evaluate)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qone qone_canonical canonicalCoefficients qmul_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalMonicReduction (singleton singleton_length singleton_lookup canonical_coefficients_congr)
open LeanProofs.IPRA.Analysis.GaussianPolynomialRowQuotient (H H_length H_canonical H_monic H_evaluation)
open LeanProofs.IPRA.Analysis.GaussianRationalPolynomialProduct (product product_length product_canonical)
open LeanProofs.IPRA.Analysis.GaussianRationalFiberGrouping (xKeyF fiberCount groupCount)
open LeanProofs.IPRA.Analysis.GaussianRationalCurveFibers (selectedX)
open LeanProofs.IPRA.Analysis.GaussianTranslatedNonconstant (recode recode_congr recode_eq zeroPrefix)
open LeanProofs.IPRA.Analysis.GaussianRationalPolynomialDegree (first degree nonzeroCoefficients)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (L p : PTm n) : PTm n := Foundations.FiniteFiberGrouping.data L p
def T (L p g : PTm n) : PTm n := ap2 (sumF (Foundations.FiniteFiberGrouping.sizeBody xKeyF)) g (data L p)
def update (Q L p g : PTm n) : PTm n := product Q (H (selectedX L p g) (fiberCount L p g)) (T L p g) (fiberCount L p g)
def stepBody : PTm 3 := update (var 1) (fstT (var 2)) (sndT (var 2)) (var 0)
def productF : PR 2 := rec2 (singleton qone : PTm 1) stepBody
def C (L p g : PTm n) : PTm n := ap2 productF g (data L p)

ipra_subst data
ipra_subst T
ipra_subst update
ipra_subst C

theorem size_body_at (L p g : PTm n) : Γ ⊢[PRAAx]
    inst2 (Foundations.FiniteFiberGrouping.sizeBody xKeyF) g (data L p) ≐ fiberCount L p g := by
  simp only [Foundations.FiniteFiberGrouping.sizeBody,inst2,Foundations.FiniteFiberGrouping.subst_fiberCount,
    subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  ipra_congr (fiberCount (var 0) (var 1) (var 2) : PTm 3) with
    [(show _ ⊢[PRAAx] fstT (data L p) ≐ L from fst_pair _ _),
      (show _ ⊢[PRAAx] sndT (data L p) ≐ p from snd_pair _ _), .eqRefl g]
theorem T_zero (L p : PTm n) : Γ ⊢[PRAAx] T L p zero ≐ zero := sum_zero _ _
theorem T_succ (L p g : PTm n) : Γ ⊢[PRAAx] T L p (succ g) ≐ T L p g+fiberCount L p g :=
  (sum_succ _ _ _).eqTrans (congrAdd (.eqRefl _) (size_body_at _ _ _))
theorem T_total (L p : PTm n) : Γ ⊢[PRAAx] T L p (groupCount L p) ≐ length L :=
  GaussianRationalFiberGrouping.cardinal_partition _ _
theorem T_monotone (L p g h : PTm n) (hg : Γ ⊢[PRAAx] le g h) : Γ ⊢[PRAAx] le (T L p g) (T L p h) :=
  le_of_eq_add ((congrAp2 (sumF (Foundations.FiniteFiberGrouping.sizeBody xKeyF)) (eq_add_of_le hg) (.eqRefl _)).eqTrans
    (sum_split _ _ _ _))
theorem T_bound (L p g : PTm n) (hg : Γ ⊢[PRAAx] le g (groupCount L p)) : Γ ⊢[PRAAx] le (T L p g) (length L) :=
  le_congr (.eqRefl _) (T_total _ _) (T_monotone _ _ _ _ hg)
theorem update_congr {Q Q' L L' p p' g g' : PTm n} (hQ : Γ ⊢[PRAAx] Q ≐ Q')
    (hL : Γ ⊢[PRAAx] L ≐ L') (hp : Γ ⊢[PRAAx] p ≐ p') (hg : Γ ⊢[PRAAx] g ≐ g') : Γ ⊢[PRAAx]
    update Q L p g ≐ update Q' L' p' g' := by
  ipra_congr (update (var 0) (var 1) (var 2) (var 3) : PTm 4) with [hQ, hL, hp, hg]
theorem C_index_congr (L p : PTm n) {g h : PTm n} (he : Γ ⊢[PRAAx] g ≐ h) : Γ ⊢[PRAAx]
    C L p g ≐ C L p h := congrAp2 productF he (.eqRefl _)
theorem C_zero (L p : PTm n) : Γ ⊢[PRAAx] C L p zero ≐ singleton qone := by
  simpa only [C,productF,GaussianRationalMonicReduction.subst_singleton,GaussianRationalSyntheticDivision.subst_qone] using
    rec2_zero (Γ := Γ) (singleton qone : PTm 1) stepBody (data L p)
theorem C_succ (L p g : PTm n) : Γ ⊢[PRAAx]
    C L p (succ g) ≐ product (C L p g) (H (selectedX L p g) (fiberCount L p g)) (T L p g) (fiberCount L p g) := by
  have e := rec2_succ (Γ := Γ) (singleton qone : PTm 1) stepBody g (data L p)
  simp only [stepBody,subst_update,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] at e
  exact e.eqTrans (update_congr (.eqRefl _) (fst_pair _ _) (snd_pair _ _) (.eqRefl _))

theorem C_length (L p g : PTm n) : Γ ⊢[PRAAx] length (C L p g) ≐ succ (T L p g) := by
  have all : Γ ⊢[PRAAx] .all (length (C (Syn.shift L) (Syn.shift p) (var 0)) ≐ succ (T (Syn.shift L) (Syn.shift p) (var 0))) := by
    ipra_qfind [subst_length, subst_C, subst_T]
    · exact ((congrFst (C_zero _ _)).eqTrans (singleton_length _)).eqTrans (congrSucc (T_zero _ _)).eqSymm
    · exact (congrFst (C_succ _ _ _)).eqTrans ((product_length _ _ _ _).eqTrans (congrSucc (T_succ _ _ _)).eqSymm)
  ipra_simpa_inst [Fm.subst_eq,subst_length,subst_C,subst_T,ConciseIPRA.PTm.subst_succ] using all.allE g
theorem C_canonical (L p g : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (C L p g) := by
  refine .orE (zero_or_succ g) ?_ ?_
  · exact canonical_coefficients_congr ((C_index_congr _ _ Prf.hyp0).eqTrans (C_zero _ _))
      GaussianRationalReconstruction.singleton_canonical
  · exact canonical_coefficients_congr ((C_index_congr _ _ Prf.hyp0).eqTrans (C_succ _ _ _)) (product_canonical _ _ _ _)

theorem empty_zero_prefix (P : PTm n) : Γ ⊢[PRAAx] zeroPrefix P zero := by
  simp only [zeroPrefix,Syn.shift,ConciseIPRA.PTm.subst_zero]
  exact .allI (.impI (not_succ_le_self (var 0) _ (le_trans Prf.hyp0 (zero_le _))))
theorem product_head (P Q N M : PTm n) : Γ ⊢[PRAAx] entry (product P Q N M) zero ≐
    qmul (recode (entry P zero)) (recode (entry Q zero)) :=
  (Foundations.SequenceComposition.entry_congr (.eqRefl _) (add_zero zero).eqSymm).eqTrans
    (GaussianRationalPolynomialProductDegree.product_entry_at _ _ _ _ _ _ (empty_zero_prefix _) (empty_zero_prefix _) (zero_le _) (zero_le _))
theorem C_monic (L p g : PTm n) : Γ ⊢[PRAAx] entry (C L p g) zero ≐ qone := by
  have all : Γ ⊢[PRAAx] .all (entry (C (Syn.shift L) (Syn.shift p) (var 0)) zero ≐ qone) := by
    ipra_qfind [subst_entry, subst_C, GaussianRationalSyntheticDivision.subst_qone]
    · exact (Foundations.SequenceComposition.entry_congr (C_zero _ _) (.eqRefl _)).eqTrans (singleton_lookup _)
    · exact (Foundations.SequenceComposition.entry_congr (C_succ _ _ _) (.eqRefl _)).eqTrans
        ((product_head _ _ _ _).eqTrans ((qmul_congr
          ((recode_congr Prf.hyp0).eqTrans (recode_eq _ qone_canonical))
          ((recode_congr (H_monic _ _)).eqTrans (recode_eq _ qone_canonical))).eqTrans
            (GaussianReciprocalHorner.qmul_one_right _ qone_canonical)))
  ipra_simpa_inst [Fm.subst_eq,subst_entry,subst_C,ConciseIPRA.PTm.subst_zero,GaussianRationalSyntheticDivision.subst_qone] using all.allE g

theorem C_recoded_head (L p g : PTm n) : Γ ⊢[PRAAx] recode (entry (C L p g) zero) ≐ qone :=
  (recode_congr (C_monic _ _ _)).eqTrans (recode_eq _ qone_canonical)
theorem C_head_nonzero (L p g : PTm n) : Γ ⊢[PRAAx] neg (recode (entry (C L p g) zero) ≐ qzero) :=
  .impI (.impE GaussianRationalCurveFibers.gaussian_one_nonzero ((C_recoded_head _ _ _).wk.eqSymm.eqTrans Prf.hyp0))
theorem C_nonzero (L p g : PTm n) : Γ ⊢[PRAAx] nonzeroCoefficients (C L p g) (T L p g) := by
  refine .exI zero ?_
  have witness : Γ ⊢[PRAAx] lt zero (succ (T L p g)) ⋏ neg (recode (entry (C L p g) zero) ≐ qzero) :=
    .andI ((succ_monus_succ zero (T L p g)).eqTrans (zero_le (T L p g))) (C_head_nonzero L p g)
  simpa only [Fm.subst_and,subst_lt,GaussianTranslatedNonconstant.subst_recode,subst_entry,subst_C,subst_T,ConciseIPRA.PTm.subst_zero,
    ConciseIPRA.PTm.subst_succ,neg,Fm.subst_imp,Fm.subst_eq,Fm.subst_bot,GaussianRationalHorner.subst_qzero,
    Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using witness
theorem C_first (L p g : PTm n) : Γ ⊢[PRAAx] first (C L p g) (T L p g) ≐ zero :=
  GaussianRationalPolynomialProductDegree.first_exact _ _ _ (zero_le _) (empty_zero_prefix _) (C_head_nonzero _ _ _)
theorem C_degree (L p g : PTm n) : Γ ⊢[PRAAx] degree (C L p g) (T L p g) ≐ T L p g :=
  (congrMonus (.eqRefl _) (C_first _ _ _)).eqTrans (monus_zero _)
theorem C_evaluation_zero (L p z : PTm n) : Γ ⊢[PRAAx] evaluate (C L p zero) z ≐ qone :=
  (GaussianRationalMonicReduction.evaluate_congr (C_zero _ _) (.eqRefl _)).eqTrans
    (GaussianRationalReconstruction.singleton_evaluation _)
theorem C_evaluation_succ (L p g z : PTm n) : Γ ⊢[PRAAx] evaluate (C L p (succ g)) z ≐
    qmul (evaluate (C L p g) z) (GaussianRationalReciprocal.power (GaussianRationalMetric.qsub z (selectedX L p g)) (fiberCount L p g)) :=
  (GaussianRationalMonicReduction.evaluate_congr (C_succ _ _ _) (.eqRefl _)).eqTrans
    ((GaussianRationalPolynomialProduct.product_evaluation _ _ _ _ _ (C_length _ _ _) (H_length _ _)).eqTrans
      (qmul_congr (.eqRefl _) (H_evaluation _ _ _)))

theorem earlier_difference_nonzero (L p g h : PTm n) (hh : Γ ⊢[PRAAx] lt h (groupCount L p))
    (hg : Γ ⊢[PRAAx] lt g h) : Γ ⊢[PRAAx]
    neg (GaussianRationalMetric.qsub (selectedX L p h) (selectedX L p g) ≐ qzero) := by
  have neq : Γ ⊢[PRAAx] neg (GaussianRationalValueEquality.valueEqual (selectedX L p h) (selectedX L p g)) :=
    GaussianRationalFiberGrouping.distinct_group_abscissae _ _ _ _ hh (lt_of_lt_of_le hg (le_of_lt hh))
      (GaussianRationalMonicReconstruction.different_of_gt hg)
  exact .impI (.impE neq.wk ((GaussianRationalValueEquality.difference_zero_iff _ _).wk.iffMp Prf.hyp0))
theorem next_value_step (L p g h : PTm n) (hh : Γ ⊢[PRAAx] lt h (groupCount L p))
    (hg : Γ ⊢[PRAAx] lt g h)
    (hOld : Γ ⊢[PRAAx] neg (evaluate (C L p g) (selectedX L p h) ≐ qzero)) : Γ ⊢[PRAAx]
    neg (evaluate (C L p (succ g)) (selectedX L p h) ≐ qzero) := by
  have positive := GaussianRationalPowerNonzero.power_nonzero (Γ := Γ)
    (GaussianRationalMetric.qsub (selectedX L p h) (selectedX L p g)) (fiberCount L p g)
    (GaussianRationalMetric.qsub_canonical _ _) (earlier_difference_nonzero _ _ _ _ hh hg)
  have actual := GaussianRationalPolynomialProductDegree.multiply_nonzero (Γ := Γ)
    (evaluate (C L p g) (selectedX L p h))
    (GaussianRationalReciprocal.power (GaussianRationalMetric.qsub (selectedX L p h) (selectedX L p g)) (fiberCount L p g))
    (GaussianRationalHorner.horner_canonical _ _ _) (GaussianRationalReciprocal.power_canonical _ _) hOld positive
  exact .impI (.impE actual.wk ((C_evaluation_succ _ _ _ _).wk.eqSymm.eqTrans Prf.hyp0))

/-- Actual earlier factors have nonzero values at the later original group.
The proof derives every factor difference from exact grouping, not raw-code
inequality or a supplied polynomial nonvanishing invariant. -/
theorem prefix_value_nonzero (L p g h : PTm n) (hh : Γ ⊢[PRAAx] lt h (groupCount L p))
    (hg : Γ ⊢[PRAAx] le g h) : Γ ⊢[PRAAx] neg (evaluate (C L p g) (selectedX L p h) ≐ qzero) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift h) (groupCount (Syn.shift L) (Syn.shift p)) := by
    simpa only [Fm.shift,subst_lt,Foundations.FiniteFiberGrouping.subst_groupCount,Syn.shift] using hh.shift
  have all : Γ ⊢[PRAAx] .all (le (var 0) (Syn.shift h) ⟶
      neg (evaluate (C (Syn.shift L) (Syn.shift p) (var 0)) (selectedX (Syn.shift L) (Syn.shift p) (Syn.shift h)) ≐ qzero)) := by
    ipra_qfind (⟨le_QF _ _,by trivial⟩) [Fm.subst_bot, neg, subst_le, GaussianRationalHorner.subst_evaluate, subst_C,
        GaussianRationalCurveFibers.subst_selectedX, GaussianRationalHorner.subst_qzero]
    · exact .impI (.impI (.impE GaussianRationalCurveFibers.gaussian_one_nonzero
        ((C_evaluation_zero _ _ _).wk.wk.eqSymm.eqTrans Prf.hyp0)))
    · refine .impI ?_
      exact next_value_step _ _ _ _ hs.wk.wk Prf.hyp0 (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0))
  have rule : Γ ⊢[PRAAx] le g h ⟶ neg (evaluate (C L p g) (selectedX L p h) ≐ qzero) := by
    ipra_simpa_inst [Fm.subst_imp,Fm.subst_eq,Fm.subst_bot,neg,subst_le,GaussianRationalHorner.subst_evaluate,subst_C,
      GaussianRationalCurveFibers.subst_selectedX,GaussianRationalHorner.subst_qzero] using all.allE g
  exact .impE rule hg
theorem next_group_nonzero (L p g : PTm n) (hg : Γ ⊢[PRAAx] lt g (groupCount L p)) : Γ ⊢[PRAAx]
    neg (evaluate (C L p g) (selectedX L p g) ≐ qzero) := prefix_value_nonzero _ _ _ _ hg (le_refl _)

/-! Actual PR3 fields retain the polynomial, its count and the next
ORIGINAL abscissa/multiplicity. No quotient or factorization is returned. -/
def CProgramF : PR 3 := PTm.toPR (C (var 0) (var 1) (var 2))
def TProgramF : PR 3 := PTm.toPR (T (var 0) (var 1) (var 2))
def output (L p g : PTm n) : PTm n := pairT (C L p g) (pairT (T L p g) (pairT (selectedX L p g) (fiberCount L p g)))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (L p g : PTm n) : PTm n := ap3 outputF L p g
ipra_subst output
ipra_subst run
theorem C_program_at (L p g : PTm n) : Γ ⊢[PRAAx] ap3 CProgramF L p g ≐ C L p g := by
  simpa [CProgramF,ap3] using toPR_eq (Γ := Γ) (C (var 0) (var 1) (var 2) : PTm 3) ![L,p,g]
theorem T_program_at (L p g : PTm n) : Γ ⊢[PRAAx] ap3 TProgramF L p g ≐ T L p g := by
  simpa [TProgramF,ap3] using toPR_eq (Γ := Γ) (T (var 0) (var 1) (var 2) : PTm 3) ![L,p,g]
theorem program_at (L p g : PTm n) : Γ ⊢[PRAAx] run L p g ≐ output L p g := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![L,p,g]
theorem returned_C (L p g : PTm n) : Γ ⊢[PRAAx] fstT (run L p g) ≐ C L p g :=
  (program_at _ _ _).fstE
theorem returned_T (L p g : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run L p g)) ≐ T L p g :=
  (program_at _ _ _).sndE.fstE
theorem returned_x (L p g : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run L p g))) ≐ selectedX L p g :=
  (program_at _ _ _).sndE.sndE.fstE
theorem returned_t (L p g : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run L p g))) ≐ fiberCount L p g :=
  (program_at _ _ _).sndE.sndE.sndE
theorem returned_length (L p g : PTm n) : Γ ⊢[PRAAx] length (fstT (run L p g)) ≐ succ (fstT (sndT (run L p g))) :=
  (congrFst (returned_C _ _ _)).eqTrans ((C_length _ _ _).eqTrans (congrSucc (returned_T _ _ _)).eqSymm)
theorem returned_next_nonzero (L p g : PTm n) (hg : Γ ⊢[PRAAx] lt g (groupCount L p)) : Γ ⊢[PRAAx]
    neg (evaluate (fstT (run L p g)) (fstT (sndT (sndT (run L p g)))) ≐ qzero) :=
  .impI (.impE (next_group_nonzero _ _ _ hg).wk
    ((GaussianRationalMonicReduction.evaluate_congr (returned_C _ _ _) (returned_x _ _ _)).wk.eqSymm.eqTrans Prf.hyp0))

/-! Every original point-list code, grouping datum, group counter and
query point is internally quantified in ordinary PRA proofs. -/
theorem actual_count_recursion_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((T (var 0) (var 1) zero ≐ zero) ⋏
      (T (var 0) (var 1) (succ (var 2)) ≐ T (var 0) (var 1) (var 2)+fiberCount (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.andI (T_zero _ _) (T_succ _ _ _))
theorem actual_total_count_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (T (var 0) (var 1) (groupCount (var 0) (var 1)) ≐ length (var 0)) := closeUniv 2 (T_total _ _)
theorem actual_prefix_count_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 2) (groupCount (var 0) (var 1)) ⟶ le (T (var 0) (var 1) (var 2)) (length (var 0))) :=
  closeUniv 3 (.impI (T_bound _ _ _ Prf.hyp0))
theorem actual_factor_recursion_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((C (var 0) (var 1) zero ≐ singleton qone) ⋏
      (C (var 0) (var 1) (succ (var 2)) ≐ product (C (var 0) (var 1) (var 2))
        (H (selectedX (var 0) (var 1) (var 2)) (fiberCount (var 0) (var 1) (var 2)))
        (T (var 0) (var 1) (var 2)) (fiberCount (var 0) (var 1) (var 2)))) :=
  closeUniv 3 (.andI (C_zero _ _) (C_succ _ _ _))
theorem actual_factor_structure_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((length (C (var 0) (var 1) (var 2)) ≐ succ (T (var 0) (var 1) (var 2))) ⋏
      (canonicalCoefficients (C (var 0) (var 1) (var 2)) ⋏
        ((entry (C (var 0) (var 1) (var 2)) zero ≐ qone) ⋏
          (nonzeroCoefficients (C (var 0) (var 1) (var 2)) (T (var 0) (var 1) (var 2)) ⋏
            ((first (C (var 0) (var 1) (var 2)) (T (var 0) (var 1) (var 2)) ≐ zero) ⋏
              (degree (C (var 0) (var 1) (var 2)) (T (var 0) (var 1) (var 2)) ≐ T (var 0) (var 1) (var 2))))))) :=
  closeUniv 3 (.andI (C_length _ _ _) (.andI (C_canonical _ _ _) (.andI (C_monic _ _ _)
    (.andI (C_nonzero _ _ _) (.andI (C_first _ _ _) (C_degree _ _ _))))))
theorem actual_factor_evaluation_step_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (evaluate (C (var 0) (var 1) (succ (var 2))) (var 3) ≐
      qmul (evaluate (C (var 0) (var 1) (var 2)) (var 3))
        (GaussianRationalReciprocal.power (GaussianRationalMetric.qsub (var 3) (selectedX (var 0) (var 1) (var 2)))
          (fiberCount (var 0) (var 1) (var 2)))) := closeUniv 4 (C_evaluation_succ _ _ _ _)
theorem actual_distinct_group_difference_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (groupCount (var 0) (var 1)) ⟶ lt (var 2) (var 3) ⟶
      neg (GaussianRationalMetric.qsub (selectedX (var 0) (var 1) (var 3)) (selectedX (var 0) (var 1) (var 2)) ≐ qzero)) :=
  closeUniv 4 (.impI (.impI (earlier_difference_nonzero _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_prefix_value_nonzero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (groupCount (var 0) (var 1)) ⟶ le (var 2) (var 3) ⟶
      neg (evaluate (C (var 0) (var 1) (var 2)) (selectedX (var 0) (var 1) (var 3)) ≐ qzero)) :=
  closeUniv 4 (.impI (.impI (prefix_value_nonzero _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_next_group_nonzero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (groupCount (var 0) (var 1)) ⟶
      neg (evaluate (C (var 0) (var 1) (var 2)) (selectedX (var 0) (var 1) (var 2)) ≐ qzero)) :=
  closeUniv 3 (.impI (next_group_nonzero _ _ _ Prf.hyp0))
theorem actual_factor_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((ap3 CProgramF (var 0) (var 1) (var 2) ≐ C (var 0) (var 1) (var 2)) ⋏
      ((ap3 TProgramF (var 0) (var 1) (var 2) ≐ T (var 0) (var 1) (var 2)) ⋏
        (run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)))) :=
  closeUniv 3 (.andI (C_program_at _ _ _) (.andI (T_program_at _ _ _) (program_at _ _ _)))
theorem actual_returned_original_group_fields_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((fstT (run (var 0) (var 1) (var 2)) ≐ C (var 0) (var 1) (var 2)) ⋏
      ((fstT (sndT (run (var 0) (var 1) (var 2))) ≐ T (var 0) (var 1) (var 2)) ⋏
        ((fstT (sndT (sndT (run (var 0) (var 1) (var 2)))) ≐ selectedX (var 0) (var 1) (var 2)) ⋏
          (sndT (sndT (sndT (run (var 0) (var 1) (var 2)))) ≐ fiberCount (var 0) (var 1) (var 2))))) :=
  closeUniv 3 (.andI (returned_C _ _ _) (.andI (returned_T _ _ _) (.andI (returned_x _ _ _) (returned_t _ _ _))))
theorem actual_returned_next_value_nonzero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (groupCount (var 0) (var 1)) ⟶
      neg (evaluate (fstT (run (var 0) (var 1) (var 2))) (fstT (sndT (sndT (run (var 0) (var 1) (var 2))))) ≐ qzero)) :=
  closeUniv 3 (.impI (returned_next_nonzero _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNormGroupFactorProduct

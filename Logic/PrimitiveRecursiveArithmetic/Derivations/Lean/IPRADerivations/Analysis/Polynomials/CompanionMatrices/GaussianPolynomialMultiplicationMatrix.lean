import IPRADerivations.Analysis.Polynomials.CompanionMatrices.GaussianPolynomialMonicCompanion
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianPowers.GaussianRationalPowerExpansion
import IPRADerivations.Foundations.BoundedSyntaxInduction

/-!
# An actual internally sized polynomial multiplication matrix

The companion is iterated on polynomial-valued rows. Every matrix entry
remains an actual X-polynomial code. Source rows use ascending Y powers:
row r reads descending remainder slot m-1-r; column j remains ascending.
All dimensions, degree bounds, lists and indices are numerical. The source
evaluation-row equation is derived from the actual companion computation.
No determinant, norm, field quotient or fiber-count theorem is asserted.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialMultiplicationMatrix

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero qadd qmul canonical evaluate horner hornerF)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision
  (qone qadd_congr qmul_congr canonicalCoefficients canonical_coefficient_at)
open LeanProofs.IPRA.Analysis.GaussianPolynomialMonicCompanion
  (normalizedRow rowShape row_shape_at normalized_length normalized_canonical normalized_evaluation
    companion companion_length actual_row_length actual_row_canonical values values_length values_lookup
    monicValues evaluation_congr values_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalPolynomialBuffers (leftPad pad_length pad_evaluation)
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal (power power_zero power_succ)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open LeanProofs.IPRA.Foundations.BoundedSyntax (BFm formula)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def bound (a c j : PTm n) : PTm n := a+j*c
def normalizeBody : PTm 2 := normalizedRow (entry (var 1) (var 0))
def normalizedRows (G m : PTm n) : PTm n := sequence normalizeBody m G
def data (F G m a c : PTm n) : PTm n := GaussianPolynomialMonicCompanion.data F G m a c
def advance (F m a c j H : PTm n) : PTm n := companion F H m (bound a c j) c
def advanceF : PR 6 := PTm.toPR (advance (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
def initial : PTm 1 := normalizedRows (fstT (sndT (var 0))) (fstT (sndT (sndT (var 0))))
def stepBody : PTm 3 := app advanceF ![fstT (var 2),fstT (sndT (sndT (var 2))),
  fstT (sndT (sndT (sndT (var 2)))),sndT (sndT (sndT (sndT (var 2)))),var 0,var 1]
def stageF : PR 2 := rec2 initial stepBody
def stage (F G m a c j : PTm n) : PTm n := ap2 stageF j (data F G m a c)

ipra_subst bound
ipra_subst normalizedRows
ipra_subst data
ipra_subst advance
ipra_subst stage

theorem bound_zero (a c : PTm n) : Γ ⊢[PRAAx] bound a c zero ≐ a := by unfold bound; ipra_ring
theorem bound_succ (a c j : PTm n) : Γ ⊢[PRAAx] bound a c (succ j) ≐ bound a c j+c := by unfold bound; ipra_ring
theorem normalized_rows_length (G m : PTm n) : Γ ⊢[PRAAx] length (normalizedRows G m) ≐ m := sequence_length _ _ _
theorem normalized_rows_lookup (G m r : PTm n) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    entry (normalizedRows G m) r ≐ normalizedRow (entry G r) := by
  simpa only [normalizedRows,normalizeBody,inst2,GaussianPolynomialMonicCompanion.subst_normalizedRow,subst_entry,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using sequence_decode normalizeBody (x := G) hr

theorem advance_program (F m a c j H : PTm n) : Γ ⊢[PRAAx]
    app advanceF ![F,m,a,c,j,H] ≐ advance F m a c j H := by
  simpa [advanceF] using
    toPR_eq (Γ := Γ) (advance (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) ![F,m,a,c,j,H]

theorem stage_zero (F G m a c : PTm n) : Γ ⊢[PRAAx]
    stage F G m a c zero ≐ normalizedRows G m := by
  have e := rec2_zero (Γ := Γ) initial stepBody (data F G m a c)
  simp only [initial,subst_normalizedRows,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero] at e
  have tail := snd_pair (Γ := Γ) F (pairT G (pairT m (pairT a c)))
  have rest := (congrSnd tail).eqTrans (snd_pair G (pairT m (pairT a c)))
  have h : Γ ⊢[PRAAx] normalizedRows (fstT (sndT (data F G m a c)))
      (fstT (sndT (sndT (data F G m a c)))) ≐ normalizedRows G m := by
    simpa only [subst_normalizedRows,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
      Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (normalizedRows (var 0) (var 1) : PTm 2)
        (σ := ![fstT (sndT (data F G m a c)),fstT (sndT (sndT (data F G m a c)))])
        (σ' := ![G,m]) (fun i => by
          fin_cases i
          · exact tail.fstE
          · exact rest.fstE)
  exact e.eqTrans h

theorem stage_succ (F G m a c j : PTm n) : Γ ⊢[PRAAx]
    stage F G m a c (succ j) ≐ companion F (stage F G m a c j) m (bound a c j) c := by
  let d := data F G m a c
  let R := stage F G m a c j
  have e : Γ ⊢[PRAAx] stage F G m a c (succ j) ≐ app advanceF
      ![fstT d,fstT (sndT (sndT d)),fstT (sndT (sndT (sndT d))),sndT (sndT (sndT (sndT d))),j,R] :=
    rec2_succ_app initial advanceF
      ![fstT (var 2),fstT (sndT (sndT (var 2))),fstT (sndT (sndT (sndT (var 2)))),
        sndT (sndT (sndT (sndT (var 2)))),var 0,var 1]
      j d _ (by funext i; fin_cases i <;> simp <;> rfl)
  have tail := snd_pair (Γ := Γ) F (pairT G (pairT m (pairT a c)))
  have rest := (congrSnd tail).eqTrans (snd_pair G (pairT m (pairT a c)))
  have last := (congrSnd rest).eqTrans (snd_pair m (pairT a c))
  have h : Γ ⊢[PRAAx] app advanceF ![fstT (data F G m a c),fstT (sndT (sndT (data F G m a c))),
        fstT (sndT (sndT (sndT (data F G m a c)))),sndT (sndT (sndT (sndT (data F G m a c)))),j,stage F G m a c j] ≐
      app advanceF ![F,m,a,c,j,stage F G m a c j] := by
    apply congrApp advanceF
    intro i
    fin_cases i
    · exact fst_pair _ _
    · exact rest.fstE
    · exact last.fstE
    · exact last.sndE
    · exact .eqRefl _
    · exact .eqRefl _
  exact e.eqTrans (h.eqTrans (advance_program _ _ _ _ _ _))

/-! The source row invariants are bounded syntax. The actual induction
predicate below is the compiled bit=1, as proved by BoundedSyntaxInduction. -/
def wellFormedSyntax (v : PTm n) : BFm n :=
  .and (.eq v (RationalSupMetric.rationalCode (RationalSupMetric.numeratorOf v) (RationalSupMetric.denominatorOf v)))
    (.and (.or (.eq (RationalSupMetric.numeratorOf v).pos zero) (.eq (RationalSupMetric.numeratorOf v).neg zero))
      (.eq (gcd (Foundations.GapDecision.zabs (RationalSupMetric.numeratorOf v))
        (RationalSupMetric.denominatorOf v)) one))
def scalarSyntax (q : PTm n) : BFm n :=
  .and (.eq q (pairT (fstT q) (sndT q)))
    (.and (wellFormedSyntax (fstT q)) (wellFormedSyntax (sndT q)))
def coefficientsSyntax (C : PTm n) : BFm n :=
  .all (length C) (scalarSyntax (entry (Syn.shift C) (var 0)))
def storedSyntax (H m b : PTm n) : BFm n := .and (.eq (length H) m)
  (.and (.all m (.eq (length (entry (Syn.shift H) (var 0))) (succ (Syn.shift b))))
    (.all m (coefficientsSyntax (entry (Syn.shift H) (var 0)))))
def stored (H m b : PTm n) : Fm PTm n :=
  length H ≐ m ⋏ (rowShape H m b ⋏ .all (lt (var 0) (Syn.shift m) ⟶ canonicalCoefficients (entry (Syn.shift H) (var 0))))
theorem formula_stored (H m b : PTm n) : formula (storedSyntax H m b) = stored H m b := by
  simp only [storedSyntax,formula,coefficientsSyntax,scalarSyntax,wellFormedSyntax,
    stored,rowShape,canonicalCoefficients,canonical,RationalNormalForm.wellFormed,Syn.shift,subst_length]
ipra_subst stored [Syn.subst_shift, Syn.shift_subst]

theorem stored_congr {H H' m m' b b' : PTm n} (hH : Γ ⊢[PRAAx] H ≐ H')
    (hm : Γ ⊢[PRAAx] m ≐ m') (hb : Γ ⊢[PRAAx] b ≐ b') (h : Γ ⊢[PRAAx] stored H m b) : Γ ⊢[PRAAx]
    stored H' m' b' := by
  simpa only [subst_stored,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqSubst (Ax := PRAAx) (Γ := Γ) (stored (var 0) (var 1) (var 2) : Fm PTm 3)
      ![H,m,b] ![H',m',b'] (fun i => by fin_cases i; exact hH; exact hm; exact hb)
      (by simpa only [subst_stored,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
        Matrix.head_cons,Matrix.tail_cons] using h)

theorem normalized_rows_stored (G m a : PTm n) (hG : Γ ⊢[PRAAx] rowShape G m a) : Γ ⊢[PRAAx]
    stored (normalizedRows G m) m a := by
  refine .andI (normalized_rows_length _ _) (.andI ?_ ?_)
  · refine .allI (.impI ?_)
    have hs : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift G) (Syn.shift m) (Syn.shift a) := by
      simpa only [Fm.shift,GaussianPolynomialMonicCompanion.subst_rowShape,Syn.shift] using hG.shift
    simpa only [Syn.shift,subst_normalizedRows,length] using
      (congrFst (normalized_rows_lookup (Syn.shift G) (Syn.shift m) (var 0) Prf.hyp0)).eqTrans
        ((normalized_length _).eqTrans (row_shape_at _ _ _ _ hs.wk Prf.hyp0))
  · refine .allI (.impI ?_)
    simpa only [Syn.shift,subst_normalizedRows] using
      GaussianRationalMonicReduction.canonical_coefficients_congr
        (normalized_rows_lookup (Syn.shift G) (Syn.shift m) (var 0) Prf.hyp0) (normalized_canonical _)

theorem companion_stored (F H m b c : PTm n) : Γ ⊢[PRAAx] stored (companion F H m b c) m (b+c) := by
  refine .andI (companion_length _ _ _ _ _) (.andI ?_ ?_)
  · refine .allI (.impI ?_)
    simpa only [Syn.shift,GaussianPolynomialMonicCompanion.subst_companion,LeanProofs.IPRA.PTm.subst_add] using
      actual_row_length (Syn.shift F) (Syn.shift H) (Syn.shift m) (Syn.shift b) (Syn.shift c) (var 0) Prf.hyp0
  · refine .allI (.impI ?_)
    simpa only [Syn.shift,GaussianPolynomialMonicCompanion.subst_companion] using
      actual_row_canonical (Syn.shift F) (Syn.shift H) (Syn.shift m) (Syn.shift b) (Syn.shift c) (var 0) Prf.hyp0

theorem stage_stored (F G m a c j : PTm n) (hG : Γ ⊢[PRAAx] rowShape G m a) : Γ ⊢[PRAAx]
    stored (stage F G m a c j) m (bound a c j) := by
  let A := storedSyntax (stage (Syn.shift F) (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift c) (var 0))
    (Syn.shift m) (bound (Syn.shift a) (Syn.shift c) (var 0))
  have all : Γ ⊢[PRAAx] .all (formula A) := by
    apply Foundations.BoundedSyntaxInduction.induction
    · simpa only [A,formula_stored,subst_stored,subst_stage,subst_bound,Syn.subst_var,
        Syn.inst_zero,Syn.subst_inst_shift] using
        stored_congr (stage_zero F G m a c).eqSymm (.eqRefl _) (bound_zero a c).eqSymm (normalized_rows_stored G m a hG)
    · simp only [A,formula_stored,subst_stored,subst_stage,subst_bound,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact stored_congr (stage_succ (Syn.shift F) (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift c) (var 0)).eqSymm
        (.eqRefl _) (bound_succ (Syn.shift a) (Syn.shift c) (var 0)).eqSymm
        (companion_stored _ _ _ _ _)
  simpa only [A,formula_stored,subst_stored,subst_stage,subst_bound,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j

theorem stage_length (F G m a c j : PTm n) (hG : Γ ⊢[PRAAx] rowShape G m a) : Γ ⊢[PRAAx]
    length (stage F G m a c j) ≐ m := .andE₁ (stage_stored _ _ _ _ _ _ hG)
theorem stage_shape (F G m a c j : PTm n) (hG : Γ ⊢[PRAAx] rowShape G m a) : Γ ⊢[PRAAx]
    rowShape (stage F G m a c j) m (bound a c j) := .andE₁ (.andE₂ (stage_stored _ _ _ _ _ _ hG))
theorem stage_row_canonical (F G m a c j r : PTm n)
    (hG : Γ ⊢[PRAAx] rowShape G m a) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    canonicalCoefficients (entry (stage F G m a c j) r) := by
  have h := Prf.andE₂ (Prf.andE₂ (stage_stored F G m a c j hG))
  have gate : Γ ⊢[PRAAx] lt r m ⟶ canonicalCoefficients (entry (stage F G m a c j) r) := by
    simpa only [Fm.subst_imp,subst_lt,GaussianRationalSyntheticDivision.subst_canonicalCoefficients,subst_entry,
      Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE r
  exact .impE gate hr

theorem normalized_values_entry (G m r x : PTm n) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    entry (values (normalizedRows G m) m x) r ≐ entry (values G m x) r :=
  (values_lookup _ _ _ _ hr).eqTrans
    ((evaluation_congr (normalized_rows_lookup _ _ _ hr) (.eqRefl _)).eqTrans
      ((normalized_evaluation _ _).eqTrans (values_lookup _ _ _ _ hr).eqSymm))
theorem normalized_values_evaluation (G m x y : PTm n) : Γ ⊢[PRAAx]
    evaluate (values (normalizedRows G m) m x) y ≐ evaluate (values G m x) y := by
  have entries : Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift m) ⟶
      entry (Syn.shift (values (normalizedRows G m) m x)) (var 0) ≐ entry (Syn.shift (values G m x)) (var 0)) := by
    refine .allI (.impI ?_)
    simpa only [Syn.shift,GaussianPolynomialMonicCompanion.subst_values,subst_normalizedRows] using
      normalized_values_entry (Syn.shift G) (Syn.shift m) (var 0) (Syn.shift x) Prf.hyp0
  exact (congrAp3 hornerF (values_length _ _ _) (.eqRefl _) (.eqRefl _)).eqTrans
    ((GaussianRationalLinearProduct.horner_ext _ _ _ _ _ entries (le_refl _)).eqTrans
      (congrAp3 hornerF (values_length _ _ _).eqSymm (.eqRefl _) (.eqRefl _)))

def evaluationLaw (F G m a c x y j : PTm n) : Fm PTm n :=
  evaluate (values (stage F G m a c j) m x) y ≐ qmul (evaluate (values G m x) y) (power y j)
ipra_subst evaluationLaw

theorem multiply_power_step (v y j : PTm n) : Γ ⊢[PRAAx]
    qmul y (qmul v (power y j)) ≐ qmul v (power y (succ j)) :=
  (GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
    ((GaussianReciprocalHorner.qmul_associative _ _ _).eqTrans
      (qmul_congr (.eqRefl _) (power_succ y j).eqSymm))

theorem stage_evaluation (F G m a c x y j : PTm n)
    (hm : Γ ⊢[PRAAx] le one m) (hF : Γ ⊢[PRAAx] rowShape F m c)
    (hG : Γ ⊢[PRAAx] rowShape G m a)
    (hCurve : Γ ⊢[PRAAx] evaluate (monicValues F m x) y ≐ qzero) : Γ ⊢[PRAAx]
    evaluationLaw F G m a c x y j := by
  have ms : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift m) := by
    simpa only [Fm.shift,subst_le,Syn.shift,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using hm.shift
  have fs : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift F) (Syn.shift m) (Syn.shift c) := by
    simpa only [Fm.shift,GaussianPolynomialMonicCompanion.subst_rowShape,Syn.shift] using hF.shift
  have gs : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift G) (Syn.shift m) (Syn.shift a) := by
    simpa only [Fm.shift,GaussianPolynomialMonicCompanion.subst_rowShape,Syn.shift] using hG.shift
  have curve : Γ.map Fm.shift ⊢[PRAAx] evaluate (monicValues (Syn.shift F) (Syn.shift m) (Syn.shift x)) (Syn.shift y) ≐ qzero := by
    simpa only [Fm.shift,Fm.subst_eq,GaussianRationalHorner.subst_evaluate,GaussianPolynomialMonicCompanion.subst_monicValues,
      GaussianRationalHorner.subst_qzero,Syn.shift] using hCurve.shift
  have all : Γ ⊢[PRAAx] .all (evaluationLaw (Syn.shift F) (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift c)
      (Syn.shift x) (Syn.shift y) (var 0)) := by
    ipra_qfind [subst_evaluationLaw]
    · exact (evaluation_congr (values_congr (stage_zero F G m a c) (.eqRefl _) (.eqRefl _)) (.eqRefl _)).eqTrans
        ((normalized_values_evaluation G m x y).eqTrans
          ((GaussianReciprocalHorner.qmul_one_right _ (GaussianRationalHorner.horner_canonical _ _ _)).eqSymm.eqTrans
            (qmul_congr (.eqRefl _) (power_zero y).eqSymm)))
    · let Δ := evaluationLaw (Syn.shift F) (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift c)
        (Syn.shift x) (Syn.shift y) (var 0) :: Γ.map Fm.shift
      have shape := stage_shape (Γ := Δ) (Syn.shift F) (Syn.shift G) (Syn.shift m)
        (Syn.shift a) (Syn.shift c) (var 0) gs.wk
      exact (evaluation_congr (values_congr (stage_succ (Syn.shift F) (Syn.shift G) (Syn.shift m)
          (Syn.shift a) (Syn.shift c) (var 0)) (.eqRefl _) (.eqRefl _)) (.eqRefl _)).eqTrans
        ((GaussianPolynomialMonicCompanion.curve_step _ _ _ _ _ _ _ ms.wk fs.wk shape curve.wk).eqSymm.eqTrans
          ((qmul_congr (.eqRefl _) (Prf.hyp0 : Δ ⊢[PRAAx] evaluationLaw _ _ _ _ _ _ _ _)).eqTrans
            (multiply_power_step _ _ _)))
  simpa only [subst_evaluationLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j

def slot (m r : PTm n) : PTm n := monus m (succ r)
def width (m a c : PTm n) : PTm n := a+pred m*c
def padding (m a c j : PTm n) : PTm n := monus (width m a c) (bound a c j)
def matrixEntry (F G m a c r j : PTm n) : PTm n :=
  leftPad (entry (stage F G m a c j) (slot m r)) (padding m a c j)

ipra_subst slot
ipra_subst width
ipra_subst padding
ipra_subst matrixEntry

theorem index_le_pred (m j : PTm n) (hm : Γ ⊢[PRAAx] le one m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    le j (pred m) := (succ_monus_succ _ _).eqSymm.eqTrans
      (le_congr (.eqRefl _) (RationalIntegerNormalization.positive_form hm) hj)
theorem slot_pred (m r : PTm n) (hm : Γ ⊢[PRAAx] le one m) : Γ ⊢[PRAAx]
    slot m r ≐ monus (pred m) r :=
  (congrMonus (RationalIntegerNormalization.positive_form hm) (.eqRefl _)).eqTrans (succ_monus_succ _ _)
theorem slot_range (m r : PTm n) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx] lt (slot m r) m :=
  le_of_eq_add (d := r) ((eq_add_of_le hr).eqTrans (by unfold slot; ipra_ring))
theorem slot_complement (m r : PTm n) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    slot m (slot m r) ≐ r := by
  have e := eq_add_of_le hr
  have eq : Γ ⊢[PRAAx] m ≐ succ (slot m r)+r := e.eqTrans (by unfold slot; ipra_ring)
  exact (congrMonus eq (.eqRefl _)).eqTrans (add_monus' _ _)
theorem stage_bound (m a c j : PTm n) (hm : Γ ⊢[PRAAx] le one m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    le (bound a c j) (width m a c) := by
  have h := AnalyticNumberTheory.PhiLower.le_mul_mono (index_le_pred m j hm hj) (le_refl c)
  exact add_le_add_left a h

theorem matrix_entry_length (F G m a c r j : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hG : Γ ⊢[PRAAx] rowShape G m a) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    length (matrixEntry F G m a c r j) ≐ succ (width m a c) := by
  have shape := row_shape_at _ _ _ _ (stage_shape F G m a c j hG) (slot_range m r hr)
  exact (pad_length _ _).eqTrans ((congrAdd (.eqRefl _) shape).eqTrans
    ((by ipra_ring : Γ ⊢[PRAAx] padding m a c j+succ (bound a c j) ≐ succ (padding m a c j+bound a c j)).eqTrans
      (congrSucc ((add_comm _ _).eqTrans (eq_add_of_le (stage_bound m a c j hm hj)).eqSymm))))
theorem matrix_entry_canonical (F G m a c r j : PTm n)
    (hG : Γ ⊢[PRAAx] rowShape G m a) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    canonicalCoefficients (matrixEntry F G m a c r j) :=
  GaussianPolynomialMonicCompanion.pad_canonical _ _ (stage_row_canonical _ _ _ _ _ _ _ hG (slot_range m r hr))
theorem matrix_entry_coefficient (F G m a c r j s : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hG : Γ ⊢[PRAAx] rowShape G m a) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m)
    (hs : Γ ⊢[PRAAx] le s (width m a c)) : Γ ⊢[PRAAx]
    entry (matrixEntry F G m a c r j) s ≐ GaussianRationalPolynomialBuffers.padCoefficient
      (entry (stage F G m a c j) (slot m r)) (padding m a c j) s := by
  apply GaussianRationalPolynomialBuffers.pad_lookup
  exact lt_congr (.eqRefl _) (pad_length _ _)
    (lt_congr (.eqRefl _) (matrix_entry_length F G m a c r j hm hG hr hj).eqSymm
      ((succ_monus_succ _ _).eqTrans hs))
theorem matrix_entry_evaluation (F G m a c r j x : PTm n) : Γ ⊢[PRAAx]
    evaluate (matrixEntry F G m a c r j) x ≐ evaluate (entry (stage F G m a c j) (slot m r)) x :=
  pad_evaluation _ _ _

/-! Actual outer columns and the row-major matrix retain polynomial codes.
The fixed packed bodies carry numerical dimensions rather than host Fin m. -/
def packedBody (f : PR 6) : PTm 2 := app f ![fstT (var 1),fstT (sndT (var 1)),
  fstT (sndT (sndT (var 1))),fstT (sndT (sndT (sndT (var 1)))),sndT (sndT (sndT (sndT (var 1)))),var 0]
def columnProgram : PR 6 := PTm.toPR (stage (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
def columns (F G m a c : PTm n) : PTm n := sequence (packedBody columnProgram) m (data F G m a c)
def entryProgram : PR 7 := PTm.toPR (matrixEntry (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
def entryBody : PTm 2 := app entryProgram ![fstT (sndT (var 1)),fstT (sndT (sndT (var 1))),
  fstT (sndT (sndT (sndT (var 1)))),fstT (sndT (sndT (sndT (sndT (var 1))))),
  sndT (sndT (sndT (sndT (sndT (var 1))))),fstT (var 1),var 0]
def matrixRow (F G m a c r : PTm n) : PTm n := sequence entryBody m (pairT r (data F G m a c))
def rowProgram : PR 6 := PTm.toPR (matrixRow (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
def matrix (F G m a c : PTm n) : PTm n := sequence (packedBody rowProgram) m (data F G m a c)

ipra_subst columns
ipra_subst matrixRow
ipra_subst matrix

theorem packed_body_at (f : PR 6) (F G m a c i : PTm n) : Γ ⊢[PRAAx]
    inst2 (packedBody f) i (data F G m a c) ≐ app f ![F,G,m,a,c,i] := by
  have vector : (fun j => Syn.subst ![i,data F G m a c]
      ((![fstT (var 1),fstT (sndT (var 1)),fstT (sndT (sndT (var 1))),
        fstT (sndT (sndT (sndT (var 1)))),sndT (sndT (sndT (sndT (var 1)))),var 0] : Fin 6 → PTm 2) j)) =
      ![fstT (data F G m a c),fstT (sndT (data F G m a c)),fstT (sndT (sndT (data F G m a c))),
        fstT (sndT (sndT (sndT (data F G m a c)))),sndT (sndT (sndT (sndT (data F G m a c)))),i] := by
    funext j
    fin_cases j <;> simp
  change Γ ⊢[PRAAx] app f (fun j => Syn.subst ![i,data F G m a c]
      ((![fstT (var 1),fstT (sndT (var 1)),fstT (sndT (sndT (var 1))),
        fstT (sndT (sndT (sndT (var 1)))),sndT (sndT (sndT (sndT (var 1)))),var 0] : Fin 6 → PTm 2) j)) ≐ _
  rw [vector]
  have e := snd_pair (Γ := Γ) F (pairT G (pairT m (pairT a c)))
  have f' := (congrSnd e).eqTrans (snd_pair G (pairT m (pairT a c)))
  have g := (congrSnd f').eqTrans (snd_pair m (pairT a c))
  apply congrApp f
  intro j
  fin_cases j
  · exact fst_pair _ _
  · exact e.fstE
  · exact f'.fstE
  · exact g.fstE
  · exact g.sndE
  · exact .eqRefl _

theorem column_program_at (F G m a c j : PTm n) : Γ ⊢[PRAAx]
    app columnProgram ![F,G,m,a,c,j] ≐ stage F G m a c j := by
  simpa [columnProgram] using toPR_eq (Γ := Γ)
    (stage (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) ![F,G,m,a,c,j]
theorem columns_length (F G m a c : PTm n) : Γ ⊢[PRAAx] length (columns F G m a c) ≐ m := sequence_length _ _ _
theorem columns_lookup (F G m a c j : PTm n) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    entry (columns F G m a c) j ≐ stage F G m a c j :=
  (sequence_decode (packedBody columnProgram) hj).eqTrans
    ((packed_body_at _ _ _ _ _ _ _).eqTrans (column_program_at _ _ _ _ _ _))

theorem entry_program_at (F G m a c r j : PTm n) : Γ ⊢[PRAAx]
    app entryProgram ![F,G,m,a,c,r,j] ≐ matrixEntry F G m a c r j := by
  simpa [entryProgram] using toPR_eq (Γ := Γ)
    (matrixEntry (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) : PTm 7) ![F,G,m,a,c,r,j]

theorem entry_body_at (F G m a c r j : PTm n) : Γ ⊢[PRAAx]
    inst2 entryBody j (pairT r (data F G m a c)) ≐ matrixEntry F G m a c r j := by
  have vector : (fun t => Syn.subst ![j,pairT r (data F G m a c)]
      ((![fstT (sndT (var 1)),fstT (sndT (sndT (var 1))),fstT (sndT (sndT (sndT (var 1)))),
        fstT (sndT (sndT (sndT (sndT (var 1))))),sndT (sndT (sndT (sndT (sndT (var 1))))),fstT (var 1),var 0] : Fin 7 → PTm 2) t)) =
      ![fstT (sndT (pairT r (data F G m a c))),fstT (sndT (sndT (pairT r (data F G m a c)))),
        fstT (sndT (sndT (sndT (pairT r (data F G m a c))))),fstT (sndT (sndT (sndT (sndT (pairT r (data F G m a c)))))),
        sndT (sndT (sndT (sndT (sndT (pairT r (data F G m a c)))))),fstT (pairT r (data F G m a c)),j] := by
    funext t
    fin_cases t <;> simp
  change Γ ⊢[PRAAx] app entryProgram (fun t => Syn.subst ![j,pairT r (data F G m a c)]
      ((![fstT (sndT (var 1)),fstT (sndT (sndT (var 1))),fstT (sndT (sndT (sndT (var 1)))),
        fstT (sndT (sndT (sndT (sndT (var 1))))),sndT (sndT (sndT (sndT (sndT (var 1))))),fstT (var 1),var 0] : Fin 7 → PTm 2) t)) ≐ _
  rw [vector]
  have e := snd_pair (Γ := Γ) r (data F G m a c)
  have d := (congrSnd e).eqTrans (snd_pair F (pairT G (pairT m (pairT a c))))
  have f := (congrSnd d).eqTrans (snd_pair G (pairT m (pairT a c)))
  have g := (congrSnd f).eqTrans (snd_pair m (pairT a c))
  have fields : Γ ⊢[PRAAx] app entryProgram
      ![fstT (sndT (pairT r (data F G m a c))),fstT (sndT (sndT (pairT r (data F G m a c)))),
        fstT (sndT (sndT (sndT (pairT r (data F G m a c))))),fstT (sndT (sndT (sndT (sndT (pairT r (data F G m a c)))))),
        sndT (sndT (sndT (sndT (sndT (pairT r (data F G m a c)))))),fstT (pairT r (data F G m a c)),j] ≐
      app entryProgram ![F,G,m,a,c,r,j] := by
    apply congrApp entryProgram
    intro t
    fin_cases t
    · exact e.fstE
    · exact d.fstE
    · exact f.fstE
    · exact g.fstE
    · exact g.sndE
    · exact fst_pair _ _
    · exact .eqRefl _
  exact fields.eqTrans (entry_program_at _ _ _ _ _ _ _)

theorem matrix_row_length (F G m a c r : PTm n) : Γ ⊢[PRAAx] length (matrixRow F G m a c r) ≐ m := sequence_length _ _ _
theorem matrix_row_lookup (F G m a c r j : PTm n) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    entry (matrixRow F G m a c r) j ≐ matrixEntry F G m a c r j :=
  (sequence_decode entryBody hj).eqTrans (entry_body_at _ _ _ _ _ _ _)
theorem row_program_at (F G m a c r : PTm n) : Γ ⊢[PRAAx]
    app rowProgram ![F,G,m,a,c,r] ≐ matrixRow F G m a c r := by
  simpa [rowProgram] using toPR_eq (Γ := Γ)
    (matrixRow (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) ![F,G,m,a,c,r]
theorem matrix_length (F G m a c : PTm n) : Γ ⊢[PRAAx] length (matrix F G m a c) ≐ m := sequence_length _ _ _
theorem matrix_lookup (F G m a c r : PTm n) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    entry (matrix F G m a c) r ≐ matrixRow F G m a c r :=
  (sequence_decode (packedBody rowProgram) hr).eqTrans
    ((packed_body_at _ _ _ _ _ _ _).eqTrans (row_program_at _ _ _ _ _ _))
theorem matrix_scalar_row_length (F G m a c r : PTm n) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    length (entry (matrix F G m a c) r) ≐ m :=
  (congrFst (matrix_lookup _ _ _ _ _ _ hr)).eqTrans (matrix_row_length _ _ _ _ _ _)
theorem matrix_coefficient_polynomial (F G m a c r j : PTm n)
    (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    entry (entry (matrix F G m a c) r) j ≐ matrixEntry F G m a c r j :=
  (entry_congr (matrix_lookup _ _ _ _ _ _ hr) (.eqRefl _)).eqTrans (matrix_row_lookup _ _ _ _ _ _ _ hj)
theorem matrix_polynomial_length (F G m a c r j : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hG : Γ ⊢[PRAAx] rowShape G m a) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    length (entry (entry (matrix F G m a c) r) j) ≐ succ (width m a c) :=
  (congrFst (matrix_coefficient_polynomial _ _ _ _ _ _ _ hr hj)).eqTrans (matrix_entry_length _ _ _ _ _ _ _ hm hG hr hj)
theorem matrix_polynomial_canonical (F G m a c r j : PTm n)
    (hG : Γ ⊢[PRAAx] rowShape G m a) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    canonicalCoefficients (entry (entry (matrix F G m a c) r) j) :=
  GaussianRationalMonicReduction.canonical_coefficients_congr (matrix_coefficient_polynomial _ _ _ _ _ _ _ hr hj)
    (matrix_entry_canonical _ _ _ _ _ _ _ hG hr)

/-! A literal finite scalar sum is the component of the source row e(y)M.
Its body reads the actual stored matrix polynomial and then specializes X. -/
def pairingData (M j x y : PTm n) : PTm n := pairT M (pairT j (pairT x y))
def pairingTerm (M j x y r : PTm n) : PTm n :=
  qmul (power y r) (evaluate (entry (entry M r) j) x)
def pairingBody : PTm 2 := pairingTerm (fstT (var 1)) (fstT (sndT (var 1)))
  (fstT (sndT (sndT (var 1)))) (sndT (sndT (sndT (var 1)))) (var 0)
def pairingTerms (M m j x y : PTm n) : PTm n := sequence pairingBody m (pairingData M j x y)
def pairing (M m j x y : PTm n) : PTm n := evaluate (pairingTerms M m j x y) qone
def matrixPairing (F G m a c j x y : PTm n) : PTm n := pairing (matrix F G m a c) m j x y

ipra_subst pairingData
ipra_subst pairingTerm
ipra_subst pairingTerms
ipra_subst pairing
ipra_subst matrixPairing

theorem pairing_body_at (M j x y r : PTm n) : Γ ⊢[PRAAx]
    inst2 pairingBody r (pairingData M j x y) ≐ pairingTerm M j x y r := by
  simp only [pairingBody,inst2,subst_pairingTerm,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  have e := snd_pair (Γ := Γ) M (pairT j (pairT x y))
  have f := (congrSnd e).eqTrans (snd_pair j (pairT x y))
  exact qmul_congr
    (congrAp2 GaussianRationalReciprocal.powerF (.eqRefl _) f.sndE)
    (evaluation_congr (entry_congr (entry_congr (fst_pair _ _) (.eqRefl _)) e.fstE)
      f.fstE)
theorem pairing_length (M m j x y : PTm n) : Γ ⊢[PRAAx] length (pairingTerms M m j x y) ≐ m := sequence_length _ _ _
theorem pairing_lookup (M m j x y r : PTm n) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    entry (pairingTerms M m j x y) r ≐ pairingTerm M j x y r :=
  (sequence_decode pairingBody hr).eqTrans (pairing_body_at _ _ _ _ _)

theorem pairing_power_term (F G m a c j x y r : PTm n)
    (hm : Γ ⊢[PRAAx] le one m) (hj : Γ ⊢[PRAAx] lt j m) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    entry (pairingTerms (matrix F G m a c) m j x y) r ≐
      GaussianOffDominantTerms.term (values (stage F G m a c j) m x) (pred m) y r := by
  have coefficient : Γ ⊢[PRAAx] evaluate (entry (entry (matrix F G m a c) r) j) x ≐
      entry (values (stage F G m a c j) m x) (monus (pred m) r) :=
    (evaluation_congr (matrix_coefficient_polynomial _ _ _ _ _ _ _ hr hj) (.eqRefl _)).eqTrans
      ((matrix_entry_evaluation _ _ _ _ _ _ _ _).eqTrans
        ((values_lookup _ _ _ _ (slot_range m r hr)).eqSymm.eqTrans
          (entry_congr (.eqRefl _) (slot_pred m r hm))))
  exact (pairing_lookup _ _ _ _ _ _ hr).eqTrans
    ((qmul_congr (.eqRefl _) coefficient).eqTrans (GaussianRationalPowerAlgebra.qmul_commutative _ _))

theorem pairing_stage_evaluation (F G m a c j x y : PTm n)
    (hm : Γ ⊢[PRAAx] le one m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    matrixPairing F G m a c j x y ≐ evaluate (values (stage F G m a c j) m x) y := by
  have ms : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift m) := by
    simpa only [Fm.shift,subst_le,Syn.shift,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using hm.shift
  have js : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift j) (Syn.shift m) := by
    simpa only [Fm.shift,subst_lt,Syn.shift] using hj.shift
  have entries : Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift m) ⟶
      entry (Syn.shift (pairingTerms (matrix F G m a c) m j x y)) (var 0) ≐
        entry (Syn.shift (GaussianRationalPowerExpansion.terms (values (stage F G m a c j) m x) (pred m) y)) (var 0)) := by
    refine .allI (.impI ?_)
    have e := (pairing_power_term (Syn.shift F) (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift c)
      (Syn.shift j) (Syn.shift x) (Syn.shift y) (var 0) ms.wk js.wk Prf.hyp0).eqTrans
        (GaussianRationalPowerExpansion.terms_lookup _ _ _ _ (index_le_pred _ _ ms.wk Prf.hyp0)).eqSymm
    simpa only [Syn.shift,subst_pairingTerms,subst_matrix,GaussianRationalPowerExpansion.subst_terms,
      GaussianPolynomialMonicCompanion.subst_values,subst_stage,LeanProofs.IPRA.PTm.subst_pred] using e
  have shape : Γ ⊢[PRAAx] length (values (stage F G m a c j) m x) ≐ succ (pred m) :=
    (values_length _ _ _).eqTrans (RationalIntegerNormalization.positive_form hm)
  have termsShape : Γ ⊢[PRAAx] length (GaussianRationalPowerExpansion.terms (values (stage F G m a c j) m x) (pred m) y) ≐ m :=
    (GaussianRationalPowerExpansion.terms_length _ _ _).eqTrans (RationalIntegerNormalization.positive_form hm).eqSymm
  exact (congrAp3 hornerF (pairing_length _ _ _ _ _) (.eqRefl _) (.eqRefl _)).eqTrans
    ((GaussianRationalLinearProduct.horner_ext _ _ _ _ _ entries (le_refl _)).eqTrans
      ((congrAp3 hornerF termsShape.eqSymm (.eqRefl _) (.eqRefl _)).eqTrans
        (GaussianRationalPowerExpansion.power_expansion _ _ _ shape).eqSymm))

/-- The actual j-th component of e(y)M_G(x)=G(x,y)e(y), derived from the
real polynomial-valued companion program and the original curve equation. -/
theorem evaluation_row (F G m a c j x y : PTm n)
    (hm : Γ ⊢[PRAAx] le one m) (hF : Γ ⊢[PRAAx] rowShape F m c)
    (hG : Γ ⊢[PRAAx] rowShape G m a) (hj : Γ ⊢[PRAAx] lt j m)
    (hCurve : Γ ⊢[PRAAx] evaluate (monicValues F m x) y ≐ qzero) : Γ ⊢[PRAAx]
    matrixPairing F G m a c j x y ≐ qmul (evaluate (values G m x) y) (power y j) :=
  (pairing_stage_evaluation _ _ _ _ _ _ _ _ hm hj).eqTrans
    (stage_evaluation _ _ _ _ _ _ _ _ hm hF hG hCurve)
theorem zero_evaluation_row (F G m a c j x y : PTm n)
    (hm : Γ ⊢[PRAAx] le one m) (hF : Γ ⊢[PRAAx] rowShape F m c)
    (hG : Γ ⊢[PRAAx] rowShape G m a) (hj : Γ ⊢[PRAAx] lt j m)
    (hCurve : Γ ⊢[PRAAx] evaluate (monicValues F m x) y ≐ qzero)
    (hZero : Γ ⊢[PRAAx] evaluate (values G m x) y ≐ qzero) : Γ ⊢[PRAAx]
    matrixPairing F G m a c j x y ≐ qzero :=
  (evaluation_row _ _ _ _ _ _ _ _ hm hF hG hj hCurve).eqTrans
    ((qmul_congr hZero (.eqRefl _)).eqTrans (GaussianRationalSyntheticDivision.qmul_zero_left _))

/-! Actual PR5 programs retain both the individual columns and the complete
polynomial-valued matrix. The query point is not an input of the constructor. -/
def columnsF : PR 5 := PTm.toPR (columns (var 0) (var 1) (var 2) (var 3) (var 4))
def matrixF : PR 5 := PTm.toPR (matrix (var 0) (var 1) (var 2) (var 3) (var 4))
def output (F G m a c : PTm n) : PTm n := pairT (columns F G m a c) (matrix F G m a c)
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (F G m a c : PTm n) : PTm n := app outputF ![F,G,m,a,c]
ipra_subst output
ipra_subst run
theorem columns_program (F G m a c : PTm n) : Γ ⊢[PRAAx]
    app columnsF ![F,G,m,a,c] ≐ columns F G m a c := by
  simpa [columnsF] using toPR_eq (Γ := Γ) (columns (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![F,G,m,a,c]
theorem matrix_program (F G m a c : PTm n) : Γ ⊢[PRAAx]
    app matrixF ![F,G,m,a,c] ≐ matrix F G m a c := by
  simpa [matrixF] using toPR_eq (Γ := Γ) (matrix (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![F,G,m,a,c]
theorem program_at (F G m a c : PTm n) : Γ ⊢[PRAAx] run F G m a c ≐ output F G m a c := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![F,G,m,a,c]
theorem returned_columns (F G m a c : PTm n) : Γ ⊢[PRAAx] fstT (run F G m a c) ≐ columns F G m a c :=
  (program_at _ _ _ _ _).fstE
theorem returned_matrix (F G m a c : PTm n) : Γ ⊢[PRAAx] sndT (run F G m a c) ≐ matrix F G m a c :=
  (program_at _ _ _ _ _).sndE
theorem returned_columns_length (F G m a c : PTm n) : Γ ⊢[PRAAx] length (fstT (run F G m a c)) ≐ m :=
  (congrFst (returned_columns _ _ _ _ _)).eqTrans (columns_length _ _ _ _ _)
theorem returned_matrix_length (F G m a c : PTm n) : Γ ⊢[PRAAx] length (sndT (run F G m a c)) ≐ m :=
  (congrFst (returned_matrix _ _ _ _ _)).eqTrans (matrix_length _ _ _ _ _)
theorem returned_column (F G m a c j : PTm n) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    entry (fstT (run F G m a c)) j ≐ stage F G m a c j :=
  (entry_congr (returned_columns _ _ _ _ _) (.eqRefl _)).eqTrans (columns_lookup _ _ _ _ _ _ hj)
theorem returned_polynomial (F G m a c r j : PTm n)
    (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    entry (entry (sndT (run F G m a c)) r) j ≐ matrixEntry F G m a c r j :=
  (entry_congr (entry_congr (returned_matrix _ _ _ _ _) (.eqRefl _)) (.eqRefl _)).eqTrans
    (matrix_coefficient_polynomial _ _ _ _ _ _ _ hr hj)
theorem returned_polynomial_length (F G m a c r j : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hG : Γ ⊢[PRAAx] rowShape G m a) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    length (entry (entry (sndT (run F G m a c)) r) j) ≐ succ (width m a c) :=
  (congrFst (returned_polynomial _ _ _ _ _ _ _ hr hj)).eqTrans (matrix_entry_length _ _ _ _ _ _ _ hm hG hr hj)
theorem returned_polynomial_canonical (F G m a c r j : PTm n)
    (hG : Γ ⊢[PRAAx] rowShape G m a) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    canonicalCoefficients (entry (entry (sndT (run F G m a c)) r) j) :=
  GaussianRationalMonicReduction.canonical_coefficients_congr (returned_polynomial _ _ _ _ _ _ _ hr hj)
    (matrix_entry_canonical _ _ _ _ _ _ _ hG hr)
theorem returned_coefficient (F G m a c r j s : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hG : Γ ⊢[PRAAx] rowShape G m a) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m)
    (hs : Γ ⊢[PRAAx] le s (width m a c)) : Γ ⊢[PRAAx]
    entry (entry (entry (sndT (run F G m a c)) r) j) s ≐
      GaussianRationalPolynomialBuffers.padCoefficient (entry (stage F G m a c j) (slot m r)) (padding m a c j) s :=
  (entry_congr (returned_polynomial _ _ _ _ _ _ _ hr hj) (.eqRefl _)).eqTrans
    (matrix_entry_coefficient _ _ _ _ _ _ _ _ hm hG hr hj hs)

theorem pairing_congr {M M' : PTm n} (m j x y : PTm n) (hM : Γ ⊢[PRAAx] M ≐ M') : Γ ⊢[PRAAx]
    pairing M m j x y ≐ pairing M' m j x y := by
  ipra_congr (pairing (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) with
    [hM, .eqRefl m, .eqRefl j, .eqRefl x, .eqRefl y]
theorem returned_evaluation_row (F G m a c j x y : PTm n)
    (hm : Γ ⊢[PRAAx] le one m) (hF : Γ ⊢[PRAAx] rowShape F m c)
    (hG : Γ ⊢[PRAAx] rowShape G m a) (hj : Γ ⊢[PRAAx] lt j m)
    (hCurve : Γ ⊢[PRAAx] evaluate (monicValues F m x) y ≐ qzero) : Γ ⊢[PRAAx]
    pairing (sndT (run F G m a c)) m j x y ≐ qmul (evaluate (values G m x) y) (power y j) :=
  (pairing_congr _ _ _ _ (returned_matrix _ _ _ _ _)).eqTrans (evaluation_row _ _ _ _ _ _ _ _ hm hF hG hj hCurve)

/-! Closed endpoints keep every size, polynomial list and query numerical. -/
theorem actual_polynomial_stage_stored_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (rowShape (var 1) (var 2) (var 3) ⟶ stored (stage (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
      (var 2) (bound (var 3) (var 4) (var 5))) :=
  closeUniv 6 (.impI (stage_stored _ _ _ _ _ _ Prf.hyp0))
theorem actual_polynomial_column_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (le one (var 2) ⟶ rowShape (var 0) (var 2) (var 4) ⟶ rowShape (var 1) (var 2) (var 3) ⟶
      evaluate (monicValues (var 0) (var 2) (var 6)) (var 7) ≐ qzero ⟶
        evaluationLaw (var 0) (var 1) (var 2) (var 3) (var 4) (var 6) (var 7) (var 5)) :=
  closeUniv 8 (.impI (.impI (.impI (.impI (stage_evaluation _ _ _ _ _ _ _ _ hyp2.wk hyp2 Prf.hyp1 Prf.hyp0)))))
theorem actual_polynomial_matrix_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4)) ⋏
      ((fstT (run (var 0) (var 1) (var 2) (var 3) (var 4)) ≐ columns (var 0) (var 1) (var 2) (var 3) (var 4)) ⋏
        (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4)) ≐ matrix (var 0) (var 1) (var 2) (var 3) (var 4)))) :=
  closeUniv 5 (.andI (program_at _ _ _ _ _) (.andI (returned_columns _ _ _ _ _) (returned_matrix _ _ _ _ _)))
theorem actual_polynomial_matrix_dimensions_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((length (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4))) ≐ var 2) ⋏
      length (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))) ≐ var 2) :=
  closeUniv 5 (.andI (returned_columns_length _ _ _ _ _) (returned_matrix_length _ _ _ _ _))
theorem actual_polynomial_matrix_entry_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (le one (var 2) ⟶ rowShape (var 1) (var 2) (var 3) ⟶ lt (var 5) (var 2) ⟶ lt (var 6) (var 2) ⟶
      ((length (entry (entry (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))) (var 5)) (var 6)) ≐
          succ (width (var 2) (var 3) (var 4))) ⋏
        canonicalCoefficients (entry (entry (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))) (var 5)) (var 6)))) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (.andI
    (returned_polynomial_length _ _ _ _ _ _ _ hyp2.wk hyp2 Prf.hyp1 Prf.hyp0)
    (returned_polynomial_canonical _ _ _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))))
theorem actual_polynomial_matrix_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (le one (var 2) ⟶ rowShape (var 1) (var 2) (var 3) ⟶ lt (var 5) (var 2) ⟶ lt (var 6) (var 2) ⟶
      le (var 7) (width (var 2) (var 3) (var 4)) ⟶
        entry (entry (entry (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))) (var 5)) (var 6)) (var 7) ≐
          GaussianRationalPolynomialBuffers.padCoefficient
            (entry (stage (var 0) (var 1) (var 2) (var 3) (var 4) (var 6)) (slot (var 2) (var 5)))
            (padding (var 2) (var 3) (var 4) (var 6)) (var 7)) :=
  closeUniv 8 (.impI (.impI (.impI (.impI (.impI
    (returned_coefficient _ _ _ _ _ _ _ _ hyp2.wk.wk hyp2.wk hyp2 Prf.hyp1 Prf.hyp0))))))
theorem source_polynomial_matrix_evaluation_row_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (le one (var 2) ⟶ rowShape (var 0) (var 2) (var 4) ⟶ rowShape (var 1) (var 2) (var 3) ⟶
      lt (var 5) (var 2) ⟶ evaluate (monicValues (var 0) (var 2) (var 6)) (var 7) ≐ qzero ⟶
        pairing (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))) (var 2) (var 5) (var 6) (var 7) ≐
          qmul (evaluate (values (var 1) (var 2) (var 6)) (var 7)) (power (var 7) (var 5))) :=
  closeUniv 8 (.impI (.impI (.impI (.impI (.impI
    (returned_evaluation_row _ _ _ _ _ _ _ _ hyp2.wk.wk hyp2.wk hyp2 Prf.hyp1 Prf.hyp0))))))
theorem source_polynomial_matrix_common_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (le one (var 2) ⟶ rowShape (var 0) (var 2) (var 4) ⟶ rowShape (var 1) (var 2) (var 3) ⟶
      lt (var 5) (var 2) ⟶ evaluate (monicValues (var 0) (var 2) (var 6)) (var 7) ≐ qzero ⟶
        evaluate (values (var 1) (var 2) (var 6)) (var 7) ≐ qzero ⟶
          matrixPairing (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ≐ qzero) :=
  closeUniv 8 (.impI (.impI (.impI (.impI (.impI (.impI
    (zero_evaluation_row _ _ _ _ _ _ _ _ hyp2.wk.wk.wk hyp2.wk.wk hyp2.wk hyp2 Prf.hyp1 Prf.hyp0)))))))

end LeanProofs.IPRA.Analysis.GaussianPolynomialMultiplicationMatrix

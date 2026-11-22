import IPRADerivations.Analysis.GaussianPolynomialYShift

/-!
# Rectangular bivariate padding and addition

The outer list stores descending Y coefficients, each an actual polynomial
in X. Leading outer padding uses polynomial-zero rows. No Gaussian scalar
operation is applied to an outer polynomial-row code.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBivariatePolynomialBuffers

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianPolynomialMonicCompanion (values values_length values_lookup rowShape row_shape_at normalizedRow
  normalized_length normalized_canonical normalized_evaluation pad_canonical evaluation_congr)
open GaussianPolynomialMultiplicationMatrix (stored)
open GaussianRationalHorner (evaluate hornerF qzero qadd)
open GaussianRationalPolynomialBuffers (zeros zeros_length zeros_evaluation leftPad pad_length pad_evaluation
  added added_length added_lookup added_evaluation)
open GaussianRationalSyntheticDivision (canonicalCoefficients qadd_congr)
open LeanProofs.IPRA.Foundations.GuardedTotalization (sel sel_one sel_zero)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open LeanProofs.IPRA.PTm (monus)
open ConciseIPRA.PTm (zero succ app)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def padRow (G a dx dy r : PTm n) : PTm n :=
  sel (Signum.sg (monus dy r)) (zeros (succ (a+dx)))
    (leftPad (normalizedRow (entry G (monus r dy))) dx)
def padData (G a dx dy : PTm n) : PTm n := pairT G (pairT a (pairT dx dy))
def padBody : PTm 2 := padRow (fstT (var 1)) (fstT (sndT (var 1)))
  (fstT (sndT (sndT (var 1)))) (sndT (sndT (sndT (var 1)))) (var 0)
def pad (G m a dx dy : PTm n) : PTm n := sequence padBody (dy+m) (padData G a dx dy)
def addRow (A B a r : PTm n) : PTm n := added (entry A r) (entry B r) (succ a)
def addData (A B a : PTm n) : PTm n := pairT A (pairT B a)
def addBody : PTm 2 := addRow (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0)
def add (A B m a : PTm n) : PTm n := sequence addBody m (addData A B a)

@[simp] theorem subst_padRow {k : ℕ} (σ : Fin n → PTm k) (G a dx dy r : PTm n) :
    Syn.subst σ (padRow G a dx dy r) = padRow (Syn.subst σ G) (Syn.subst σ a) (Syn.subst σ dx)
      (Syn.subst σ dy) (Syn.subst σ r) := by simp [padRow,sel,Signum.sg]
@[simp] theorem subst_padData {k : ℕ} (σ : Fin n → PTm k) (G a dx dy : PTm n) :
    Syn.subst σ (padData G a dx dy) = padData (Syn.subst σ G) (Syn.subst σ a) (Syn.subst σ dx) (Syn.subst σ dy) := by simp [padData]
@[simp] theorem subst_pad {k : ℕ} (σ : Fin n → PTm k) (G m a dx dy : PTm n) :
    Syn.subst σ (pad G m a dx dy) = pad (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ dx) (Syn.subst σ dy) := by simp [pad]
@[simp] theorem subst_addRow {k : ℕ} (σ : Fin n → PTm k) (A B a r : PTm n) :
    Syn.subst σ (addRow A B a r) = addRow (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ r) := by simp [addRow]
@[simp] theorem subst_addData {k : ℕ} (σ : Fin n → PTm k) (A B a : PTm n) :
    Syn.subst σ (addData A B a) = addData (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ a) := by simp [addData]
@[simp] theorem subst_add {k : ℕ} (σ : Fin n → PTm k) (A B m a : PTm n) :
    Syn.subst σ (add A B m a) = add (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ m) (Syn.subst σ a) := by simp [add]

theorem pad_row_before (G a dx dy r : PTm n) (hr : Γ ⊢[PRAAx] lt r dy) : Γ ⊢[PRAAx]
    padRow G a dx dy r ≐ zeros (succ (a+dx)) := sel_one (AnalyticNumberTheory.Totatives.sg_lt hr)
theorem pad_row_after (G a dx dy r : PTm n) (hr : Γ ⊢[PRAAx] le dy r) : Γ ⊢[PRAAx]
    padRow G a dx dy r ≐ leftPad (normalizedRow (entry G (monus r dy))) dx := sel_zero (AnalyticNumberTheory.Totatives.sg_le hr)
theorem pad_body_at (G a dx dy r : PTm n) : Γ ⊢[PRAAx] inst2 padBody r (padData G a dx dy) ≐ padRow G a dx dy r := by
  have tail := snd_pair (Γ := Γ) G (pairT a (pairT dx dy))
  have rest := (congrSnd tail).eqTrans (snd_pair a (pairT dx dy))
  simp only [padBody,inst2,subst_padRow,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  simpa using Prf.eqCongr (Γ := Γ) (padRow (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
    (σ := ![fstT (padData G a dx dy),fstT (sndT (padData G a dx dy)),fstT (sndT (sndT (padData G a dx dy))),
      sndT (sndT (sndT (padData G a dx dy))),r]) (σ' := ![G,a,dx,dy,r]) (fun j => by
      fin_cases j
      · exact fst_pair _ _
      · exact (congrFst tail).eqTrans (fst_pair _ _)
      · exact (congrFst rest).eqTrans (fst_pair _ _)
      · exact (congrSnd rest).eqTrans (snd_pair _ _)
      · exact .eqRefl _)
theorem pad_length (G m a dx dy : PTm n) : Γ ⊢[PRAAx] length (pad G m a dx dy) ≐ dy+m := sequence_length _ _ _
theorem pad_lookup (G m a dx dy r : PTm n) (hr : Γ ⊢[PRAAx] lt r (dy+m)) : Γ ⊢[PRAAx]
    entry (pad G m a dx dy) r ≐ padRow G a dx dy r := (sequence_decode padBody hr).eqTrans (pad_body_at _ _ _ _ _)
theorem pad_tail_index (m dy r : PTm n) (hr : Γ ⊢[PRAAx] lt r (dy+m)) (hdy : Γ ⊢[PRAAx] le dy r) :
    Γ ⊢[PRAAx] lt (monus r dy) m := by
  have enough : Γ ⊢[PRAAx] le (succ r) (dy+m) := hr
  have equality := eq_add_of_le hdy
  have shifted : Γ ⊢[PRAAx] le (dy+succ (monus r dy)) (dy+m) :=
    le_congr ((congrSucc equality).eqTrans (by ipra_ring)) (.eqRefl _) enough
  exact le_of_add_le_add_right (le_congr (add_comm _ _) (add_comm _ _) shifted)

theorem pad_row_length (G m a dx dy r : PTm n) (hG : Γ ⊢[PRAAx] rowShape G m a)
    (hr : Γ ⊢[PRAAx] lt r (dy+m)) : Γ ⊢[PRAAx] length (entry (pad G m a dx dy) r) ≐ succ (a+dx) := by
  have e := pad_lookup G m a dx dy r hr
  refine .orE (lt_or_le r dy) ?_ ?_
  · exact (congrFst (e.wk.eqTrans (pad_row_before _ _ _ _ _ Prf.hyp0))).eqTrans (zeros_length _)
  · exact (congrFst (e.wk.eqTrans (pad_row_after _ _ _ _ _ Prf.hyp0))).eqTrans
      ((GaussianRationalPolynomialBuffers.pad_length _ _).eqTrans
        ((congrAdd (.eqRefl _) ((normalized_length _).eqTrans (row_shape_at _ _ _ _ hG.wk (pad_tail_index _ _ _ hr.wk Prf.hyp0)))).eqTrans (by ipra_ring)))
theorem pad_row_canonical (G m a dx dy r : PTm n) (hr : Γ ⊢[PRAAx] lt r (dy+m)) : Γ ⊢[PRAAx]
    canonicalCoefficients (entry (pad G m a dx dy) r) := by
  have e := pad_lookup G m a dx dy r hr
  refine .orE (lt_or_le r dy) ?_ ?_
  · exact GaussianRationalMonicReduction.canonical_coefficients_congr (e.wk.eqTrans (pad_row_before _ _ _ _ _ Prf.hyp0))
      (GaussianRationalMonicReduction.zeros_canonical _)
  · exact GaussianRationalMonicReduction.canonical_coefficients_congr (e.wk.eqTrans (pad_row_after _ _ _ _ _ Prf.hyp0))
      (pad_canonical _ _ (normalized_canonical _))
theorem pad_stored (G m a dx dy : PTm n) (hG : Γ ⊢[PRAAx] rowShape G m a) : Γ ⊢[PRAAx]
    stored (pad G m a dx dy) (dy+m) (a+dx) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift G) (Syn.shift m) (Syn.shift a) := by simpa [Fm.shift,Syn.shift] using hG.shift
  refine .andI (pad_length _ _ _ _ _) (.andI (.allI (.impI ?_)) (.allI (.impI ?_)))
  · simpa [Syn.shift] using pad_row_length (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift dx) (Syn.shift dy) (var 0) hs.wk Prf.hyp0
  · simpa [Syn.shift] using pad_row_canonical (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift dx) (Syn.shift dy) (var 0) Prf.hyp0

theorem pad_specialization (G m a dx dy x r : PTm n) (hr : Γ ⊢[PRAAx] lt r (dy+m)) : Γ ⊢[PRAAx]
    entry (values (pad G m a dx dy) (dy+m) x) r ≐ entry (leftPad (values G m x) dy) r := by
  have out := (values_lookup _ _ _ _ hr).eqTrans (evaluation_congr (pad_lookup G m a dx dy r hr) (.eqRefl x))
  have inside : Γ ⊢[PRAAx] lt r (dy+length (values G m x)) := lt_congr (.eqRefl _) (congrAdd (.eqRefl _) (values_length _ _ _).eqSymm) hr
  have old := GaussianRationalPolynomialBuffers.pad_lookup (values G m x) dy r inside
  refine .orE (lt_or_le r dy) ?_ ?_
  · exact out.wk.eqTrans ((evaluation_congr (pad_row_before G a dx dy r Prf.hyp0) (.eqRefl x)).eqTrans
      ((zeros_evaluation _ _).eqTrans (old.wk.eqTrans (GaussianRationalPolynomialBuffers.pad_coefficient_before _ _ _ Prf.hyp0)).eqSymm))
  · exact out.wk.eqTrans ((evaluation_congr (pad_row_after G a dx dy r Prf.hyp0) (.eqRefl x)).eqTrans
      ((pad_evaluation _ _ _).eqTrans ((normalized_evaluation _ _).eqTrans
        ((values_lookup G m x (monus r dy) (pad_tail_index _ _ _ hr.wk Prf.hyp0)).eqSymm.eqTrans
          (old.wk.eqTrans (GaussianRationalPolynomialBuffers.pad_coefficient_after _ _ _ Prf.hyp0)).eqSymm))))
theorem pad_evaluation (G m a dx dy x y : PTm n) : Γ ⊢[PRAAx]
    evaluate (values (pad G m a dx dy) (dy+m) x) y ≐ evaluate (values G m x) y := by
  let C := values (pad G m a dx dy) (dy+m) x
  let D := leftPad (values G m x) dy
  have entries : Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift (dy+m)) ⟶ entry (Syn.shift C) (var 0) ≐ entry (Syn.shift D) (var 0)) := by
    refine .allI (.impI ?_)
    simpa [C,D,Syn.shift] using pad_specialization (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift dx) (Syn.shift dy) (Syn.shift x) (var 0) Prf.hyp0
  have len := (GaussianRationalPolynomialBuffers.pad_length (Γ := Γ) (values G m x) dy).eqTrans (congrAdd (.eqRefl _) (values_length _ _ _))
  exact (congrAp3 hornerF (values_length _ _ _) (.eqRefl _) (.eqRefl _)).eqTrans
    ((GaussianRationalLinearProduct.horner_ext C D y (dy+m) (dy+m) entries (le_refl _)).eqTrans
      ((congrAp3 hornerF len.eqSymm (.eqRefl _) (.eqRefl _)).eqTrans (GaussianRationalPolynomialBuffers.pad_evaluation _ _ _)))

theorem add_body_at (A B a r : PTm n) : Γ ⊢[PRAAx] inst2 addBody r (addData A B a) ≐ addRow A B a r := by
  simp only [addBody,inst2,subst_addRow,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  have tail := snd_pair (Γ := Γ) A (pairT B a)
  simpa using Prf.eqCongr (Γ := Γ) (addRow (var 0) (var 1) (var 2) (var 3) : PTm 4)
    (σ := ![fstT (addData A B a),fstT (sndT (addData A B a)),sndT (sndT (addData A B a)),r]) (σ' := ![A,B,a,r])
    (fun i => by fin_cases i; exact fst_pair _ _; exact (congrFst tail).eqTrans (fst_pair _ _); exact (congrSnd tail).eqTrans (snd_pair _ _); exact .eqRefl _)
theorem add_length (A B m a : PTm n) : Γ ⊢[PRAAx] length (add A B m a) ≐ m := sequence_length _ _ _
theorem add_lookup (A B m a r : PTm n) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    entry (add A B m a) r ≐ added (entry A r) (entry B r) (succ a) := (sequence_decode addBody hr).eqTrans (add_body_at _ _ _ _)
theorem add_coefficient (A B m a r s : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hs : Γ ⊢[PRAAx] le s a) : Γ ⊢[PRAAx]
    entry (entry (add A B m a) r) s ≐ qadd (entry (entry A r) s) (entry (entry B r) s) :=
  (entry_congr (add_lookup _ _ _ _ _ hr) (.eqRefl _)).eqTrans (added_lookup _ _ _ _ ((succ_monus_succ _ _).eqTrans hs))
theorem add_stored (A B m a : PTm n) : Γ ⊢[PRAAx] stored (add A B m a) m a := by
  refine .andI (add_length _ _ _ _) (.andI (.allI (.impI ?_)) (.allI (.impI ?_)))
  · simpa only [Syn.shift,subst_add,length] using (congrFst (add_lookup (Syn.shift A) (Syn.shift B) (Syn.shift m) (Syn.shift a) (var 0) Prf.hyp0)).eqTrans (added_length _ _ _)
  · simpa only [Syn.shift,subst_add] using GaussianRationalMonicReduction.canonical_coefficients_congr
      (add_lookup (Syn.shift A) (Syn.shift B) (Syn.shift m) (Syn.shift a) (var 0) Prf.hyp0)
      (GaussianRationalMonicReduction.added_canonical _ _ _)
theorem add_specialization (A B m a x r : PTm n) (hA : Γ ⊢[PRAAx] rowShape A m a) (hB : Γ ⊢[PRAAx] rowShape B m a)
    (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    entry (values (add A B m a) m x) r ≐ entry (added (values A m x) (values B m x) m) r :=
  (values_lookup _ _ _ _ hr).eqTrans ((evaluation_congr (add_lookup _ _ _ _ _ hr) (.eqRefl x)).eqTrans
    ((added_evaluation _ _ _ x (row_shape_at _ _ _ _ hA hr) (row_shape_at _ _ _ _ hB hr)).eqTrans
      ((qadd_congr (values_lookup A m x r hr).eqSymm (values_lookup B m x r hr).eqSymm).eqTrans (added_lookup _ _ _ _ hr).eqSymm)))
theorem add_evaluation (A B m a x y : PTm n) (hA : Γ ⊢[PRAAx] rowShape A m a) (hB : Γ ⊢[PRAAx] rowShape B m a) : Γ ⊢[PRAAx]
    evaluate (values (add A B m a) m x) y ≐ qadd (evaluate (values A m x) y) (evaluate (values B m x) y) := by
  let C := values (add A B m a) m x
  let D := added (values A m x) (values B m x) m
  have hAs : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift A) (Syn.shift m) (Syn.shift a) := by simpa [Fm.shift,Syn.shift] using hA.shift
  have hBs : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift B) (Syn.shift m) (Syn.shift a) := by simpa [Fm.shift,Syn.shift] using hB.shift
  have entries : Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift m) ⟶ entry (Syn.shift C) (var 0) ≐ entry (Syn.shift D) (var 0)) := by
    refine .allI (.impI ?_)
    simpa [C,D,Syn.shift] using add_specialization (Syn.shift A) (Syn.shift B) (Syn.shift m) (Syn.shift a) (Syn.shift x) (var 0) hAs.wk hBs.wk Prf.hyp0
  exact (congrAp3 hornerF (values_length _ _ _) (.eqRefl _) (.eqRefl _)).eqTrans
    ((GaussianRationalLinearProduct.horner_ext C D y m m entries (le_refl _)).eqTrans
      ((congrAp3 hornerF (added_length _ _ _).eqSymm (.eqRefl _) (.eqRefl _)).eqTrans
        (added_evaluation _ _ _ y (values_length _ _ _) (values_length _ _ _))))

theorem pad_leading_coefficient (G m a dx dy r s : PTm n) (hr : Γ ⊢[PRAAx] lt r dy)
    (hs : Γ ⊢[PRAAx] le s (a+dx)) : Γ ⊢[PRAAx] entry (entry (pad G m a dx dy) r) s ≐ qzero :=
  (entry_congr ((pad_lookup _ _ _ _ _ _ (le_trans hr (le_add_right _ _))).eqTrans (pad_row_before _ _ _ _ _ hr)) (.eqRefl _)).eqTrans
    (GaussianRationalPolynomialBuffers.zeros_lookup _ _ ((succ_monus_succ _ _).eqTrans hs))
theorem pad_tail_coefficient (G m a dx dy r s : PTm n) (hG : Γ ⊢[PRAAx] rowShape G m a)
    (hr : Γ ⊢[PRAAx] lt r m) (hs : Γ ⊢[PRAAx] le s a) : Γ ⊢[PRAAx]
    entry (entry (pad G m a dx dy) (dy+r)) (dx+s) ≐ entry (normalizedRow (entry G r)) s := by
  have range : Γ ⊢[PRAAx] lt (dy+r) (dy+m) :=
    le_congr (by ipra_ring : Γ ⊢[PRAAx] succ r+dy ≐ succ (dy+r)) (add_comm m dy) (add_le_add_right dy hr)
  have index : Γ ⊢[PRAAx] monus (dy+r) dy ≐ r := (congrMonus (add_comm dy r) (.eqRefl dy)).eqTrans (add_monus r dy)
  have padded : Γ ⊢[PRAAx] leftPad (normalizedRow (entry G (monus (dy+r) dy))) dx ≐ leftPad (normalizedRow (entry G r)) dx := by
    simpa using Prf.eqCongr (Γ := Γ) (leftPad (normalizedRow (entry (var 0) (var 1))) (var 2) : PTm 3)
      (σ := ![G,monus (dy+r) dy,dx]) (σ' := ![G,r,dx])
      (fun i => by fin_cases i; exact .eqRefl _; exact index; exact .eqRefl _)
  have old := (pad_lookup G m a dx dy (dy+r) range).eqTrans
    ((pad_row_after G a dx dy (dy+r) (le_add_right _ _)).eqTrans padded)
  exact (entry_congr old (.eqRefl _)).eqTrans (GaussianRationalPolynomialBuffers.pad_tail _ _ _
    (lt_congr (.eqRefl _) ((normalized_length _).eqTrans (row_shape_at _ _ _ _ hG hr)).eqSymm ((succ_monus_succ _ _).eqTrans hs)))

def padF : PR 5 := PTm.toPR (pad (var 0) (var 1) (var 2) (var 3) (var 4))
def padRun (G m a dx dy : PTm n) : PTm n := app padF ![G,m,a,dx,dy]
def addF : PR 4 := PTm.toPR (add (var 0) (var 1) (var 2) (var 3))
def addRun (A B m a : PTm n) : PTm n := app addF ![A,B,m,a]
theorem pad_program (G m a dx dy : PTm n) : Γ ⊢[PRAAx] padRun G m a dx dy ≐ pad G m a dx dy := by
  simpa [padRun,padF] using toPR_eq (Γ := Γ) (pad (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![G,m,a,dx,dy]
theorem add_program (A B m a : PTm n) : Γ ⊢[PRAAx] addRun A B m a ≐ add A B m a := by
  simpa [addRun,addF] using toPR_eq (Γ := Γ) (add (var 0) (var 1) (var 2) (var 3) : PTm 4) ![A,B,m,a]
theorem returned_pad_stored (G m a dx dy : PTm n) (hG : Γ ⊢[PRAAx] rowShape G m a) : Γ ⊢[PRAAx]
    stored (padRun G m a dx dy) (dy+m) (a+dx) :=
  GaussianPolynomialMultiplicationMatrix.stored_congr (pad_program _ _ _ _ _).eqSymm (.eqRefl _) (.eqRefl _) (pad_stored _ _ _ _ _ hG)
theorem returned_add_stored (A B m a : PTm n) : Γ ⊢[PRAAx] stored (addRun A B m a) m a :=
  GaussianPolynomialMultiplicationMatrix.stored_congr (add_program _ _ _ _).eqSymm (.eqRefl _) (.eqRefl _) (add_stored _ _ _ _)

theorem actual_rectangular_pad_stored_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (rowShape (var 0) (var 1) (var 2) ⟶ stored (pad (var 0) (var 1) (var 2) (var 3) (var 4)) (var 4+var 1) (var 2+var 3)) :=
  closeUniv 5 (.impI (pad_stored _ _ _ _ _ Prf.hyp0))
theorem actual_rectangular_pad_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (evaluate (values (pad (var 0) (var 1) (var 2) (var 3) (var 4)) (var 4+var 1) (var 5)) (var 6) ≐
      evaluate (values (var 0) (var 1) (var 5)) (var 6)) := closeUniv 7 (pad_evaluation _ _ _ _ _ _ _)
theorem actual_rectangular_add_stored_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (stored (add (var 0) (var 1) (var 2) (var 3)) (var 2) (var 3)) := closeUniv 4 (add_stored _ _ _ _)
theorem actual_rectangular_add_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (lt (var 4) (var 2) ⟶ le (var 5) (var 3) ⟶ entry (entry (add (var 0) (var 1) (var 2) (var 3)) (var 4)) (var 5) ≐
      qadd (entry (entry (var 0) (var 4)) (var 5)) (entry (entry (var 1) (var 4)) (var 5))) :=
  closeUniv 6 (.impI (.impI (add_coefficient _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_rectangular_add_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (rowShape (var 0) (var 2) (var 3) ⟶ rowShape (var 1) (var 2) (var 3) ⟶
      evaluate (values (add (var 0) (var 1) (var 2) (var 3)) (var 2) (var 4)) (var 5) ≐
        qadd (evaluate (values (var 0) (var 2) (var 4)) (var 5)) (evaluate (values (var 1) (var 2) (var 4)) (var 5))) :=
  closeUniv 6 (.impI (.impI (add_evaluation _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_rectangular_pad_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (padRun (var 0) (var 1) (var 2) (var 3) (var 4) ≐ pad (var 0) (var 1) (var 2) (var 3) (var 4)) := closeUniv 5 (pad_program _ _ _ _ _)
theorem actual_rectangular_add_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (addRun (var 0) (var 1) (var 2) (var 3) ≐ add (var 0) (var 1) (var 2) (var 3)) := closeUniv 4 (add_program _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianBivariatePolynomialBuffers

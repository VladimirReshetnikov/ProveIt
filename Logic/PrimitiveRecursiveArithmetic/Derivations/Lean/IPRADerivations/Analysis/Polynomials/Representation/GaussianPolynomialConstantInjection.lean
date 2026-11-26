import IPRADerivations.Analysis.Polynomials.CompanionMatrices.GaussianPolynomialMultiplicationMatrix
import IPRADerivations.Foundations.GuardedTotalization

/-!
# Adding an original X-polynomial to the constant Y coefficient

The actual row constructor adds the canonically padded original polynomial
only in the final descending Y row. All output coefficients are actual
buffers. Its coefficient observations, storage shape and every-query
bivariate evaluation law are derived without a supplied output law.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialConstantInjection

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (evaluate horner hornerF qzero qadd)
open GaussianRationalSyntheticDivision (qadd_congr canonicalCoefficients)
open GaussianPolynomialMonicCompanion (normalizedRow normalized_length normalized_canonical normalized_evaluation
  rowShape row_shape_at values values_length values_lookup evaluation_congr)
open GaussianRationalPolynomialBuffers (zeros zeros_length zeros_evaluation leftPad pad_length pad_evaluation added added_length added_lookup added_evaluation)
open LeanProofs.IPRA.Foundations.GuardedTotalization (sel sel_one sel_zero)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ app)
open LeanProofs.IPRA.PTm (pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def constantRow (C m a d r : PTm n) : PTm n := sel (eqb (succ r) m)
  (leftPad (normalizedRow C) d) (zeros (succ (a+d)))
def injectedRow (G C m a d r : PTm n) : PTm n := added (entry G r) (constantRow C m a d r) (succ (a+d))
def data (G C m a d : PTm n) : PTm n := pairT G (pairT C (pairT m (pairT a d)))
def fields (p : PTm n) : Fin 5 → PTm n :=
  ![fstT p,fstT (sndT p),fstT (sndT (sndT p)),fstT (sndT (sndT (sndT p))),sndT (sndT (sndT (sndT p)))]
def rowBody : PTm 2 := injectedRow (fields (var 1) 0) (fields (var 1) 1) (fields (var 1) 2) (fields (var 1) 3) (fields (var 1) 4) (var 0)
def inject (G C m a d : PTm n) : PTm n := sequence rowBody m (data G C m a d)

@[simp] theorem subst_constantRow {k : ℕ} (σ : Fin n → PTm k) (C m a d r : PTm n) :
    Syn.subst σ (constantRow C m a d r) = constantRow (Syn.subst σ C) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ d) (Syn.subst σ r) := by simp [constantRow,sel]
@[simp] theorem subst_injectedRow {k : ℕ} (σ : Fin n → PTm k) (G C m a d r : PTm n) :
    Syn.subst σ (injectedRow G C m a d r) = injectedRow (Syn.subst σ G) (Syn.subst σ C) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ d) (Syn.subst σ r) := by simp [injectedRow]
@[simp] theorem subst_data {k : ℕ} (σ : Fin n → PTm k) (G C m a d : PTm n) :
    Syn.subst σ (data G C m a d) = data (Syn.subst σ G) (Syn.subst σ C) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ d) := by simp [data]
@[simp] theorem subst_fields {k : ℕ} (σ : Fin n → PTm k) (p : PTm n) (i : Fin 5) :
    Syn.subst σ (fields p i) = fields (Syn.subst σ p) i := by fin_cases i <;> simp [fields]
@[simp] theorem subst_inject {k : ℕ} (σ : Fin n → PTm k) (G C m a d : PTm n) :
    Syn.subst σ (inject G C m a d) = inject (Syn.subst σ G) (Syn.subst σ C) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ d) := by simp [inject]

theorem constant_last (C m a d r : PTm n) (h : Γ ⊢[PRAAx] succ r ≐ m) : Γ ⊢[PRAAx]
    constantRow C m a d r ≐ leftPad (normalizedRow C) d := sel_one (eqb_of_eq h)
theorem constant_other (C m a d r : PTm n) (h : Γ ⊢[PRAAx] neg (succ r ≐ m)) : Γ ⊢[PRAAx]
    constantRow C m a d r ≐ zeros (succ (a+d)) := sel_zero (eqb_of_ne h)
theorem constant_length (C m a d r : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ a) : Γ ⊢[PRAAx]
    length (constantRow C m a d r) ≐ succ (a+d) := by
  refine .orE (eq_or_ne (succ r) m) ?_ ?_
  · exact (congrFst (constant_last _ _ _ _ _ Prf.hyp0)).eqTrans
      ((pad_length _ _).eqTrans ((congrAdd (.eqRefl _) ((normalized_length C).eqTrans hC.wk)).eqTrans (by ipra_ring)))
  · exact (congrFst (constant_other _ _ _ _ _ Prf.hyp0)).eqTrans (zeros_length _)
theorem row_length (G C m a d r : PTm n) : Γ ⊢[PRAAx] length (injectedRow G C m a d r) ≐ succ (a+d) := added_length _ _ _
theorem row_canonical (G C m a d r : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (injectedRow G C m a d r) := GaussianRationalMonicReduction.added_canonical _ _ _

theorem fields_at (G C m a d : PTm n) (i : Fin 5) : Γ ⊢[PRAAx] fields (data G C m a d) i ≐ ![G,C,m,a,d] i := by
  have e0 := snd_pair (Γ := Γ) G (pairT C (pairT m (pairT a d)))
  have e1 := (congrSnd e0).eqTrans (snd_pair C (pairT m (pairT a d)))
  have e2 := (congrSnd e1).eqTrans (snd_pair m (pairT a d))
  fin_cases i
  · exact fst_pair _ _
  · exact (congrFst e0).eqTrans (fst_pair _ _)
  · exact (congrFst e1).eqTrans (fst_pair _ _)
  · exact (congrFst e2).eqTrans (fst_pair _ _)
  · exact (congrSnd e2).eqTrans (snd_pair _ _)
theorem tuple_six_last {α : Type} (a b c d e f : α) : ![a,b,c,d,e,f] (5 : Fin 6) = f := rfl

theorem row_congr {G G' C C' m m' a a' d d' r r' : PTm n} (hG : Γ ⊢[PRAAx] G ≐ G') (hC : Γ ⊢[PRAAx] C ≐ C')
    (hm : Γ ⊢[PRAAx] m ≐ m') (ha : Γ ⊢[PRAAx] a ≐ a') (hd : Γ ⊢[PRAAx] d ≐ d') (hr : Γ ⊢[PRAAx] r ≐ r') : Γ ⊢[PRAAx]
    injectedRow G C m a d r ≐ injectedRow G' C' m' a' d' r' := by
  simpa only [subst_injectedRow,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,tuple_six_last,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (injectedRow (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6)
      (σ := ![G,C,m,a,d,r]) (σ' := ![G',C',m',a',d',r'])
      (fun i => by fin_cases i <;> simp only [Matrix.cons_val_succ',Matrix.cons_val_zero']; exact hG; exact hC; exact hm; exact ha; exact hd; exact hr)
theorem row_body_at (G C m a d r : PTm n) : Γ ⊢[PRAAx] inst2 rowBody r (data G C m a d) ≐ injectedRow G C m a d r := by
  simp only [rowBody,inst2,subst_injectedRow,subst_fields,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact row_congr (fields_at _ _ _ _ _ 0) (fields_at _ _ _ _ _ 1) (fields_at _ _ _ _ _ 2)
    (fields_at _ _ _ _ _ 3) (fields_at _ _ _ _ _ 4) (.eqRefl _)
theorem inject_length (G C m a d : PTm n) : Γ ⊢[PRAAx] length (inject G C m a d) ≐ m := sequence_length _ _ _
theorem inject_lookup (G C m a d r : PTm n) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    entry (inject G C m a d) r ≐ injectedRow G C m a d r := (sequence_decode rowBody hr).eqTrans (row_body_at _ _ _ _ _ _)
theorem coefficient_lookup (G C m a d r s : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hs : Γ ⊢[PRAAx] le s (a+d)) : Γ ⊢[PRAAx]
    entry (entry (inject G C m a d) r) s ≐ qadd (entry (entry G r) s) (entry (constantRow C m a d r) s) :=
  (entry_congr (inject_lookup _ _ _ _ _ _ hr) (.eqRefl _)).eqTrans
    (added_lookup _ _ _ _ ((succ_monus_succ _ _).eqTrans hs))

theorem inject_stored (G C m a d : PTm n) : Γ ⊢[PRAAx] GaussianPolynomialMultiplicationMatrix.stored (inject G C m a d) m (a+d) := by
  refine .andI (inject_length _ _ _ _ _) (.andI ?_ ?_)
  · refine .allI (.impI ?_)
    simpa only [Syn.shift,subst_inject,PTm.subst_add,length] using
      (congrFst (inject_lookup (Syn.shift G) (Syn.shift C) (Syn.shift m) (Syn.shift a) (Syn.shift d) (var 0) Prf.hyp0)).eqTrans (row_length _ _ _ _ _ _)
  · refine .allI (.impI ?_)
    simpa only [Syn.shift,subst_inject] using GaussianRationalMonicReduction.canonical_coefficients_congr
      (inject_lookup (Syn.shift G) (Syn.shift C) (Syn.shift m) (Syn.shift a) (Syn.shift d) (var 0) Prf.hyp0) (row_canonical _ _ _ _ _ _)

theorem row_evaluation (G C m a d r x : PTm n) (hG : Γ ⊢[PRAAx] rowShape G m (a+d))
    (hC : Γ ⊢[PRAAx] length C ≐ succ a) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    evaluate (injectedRow G C m a d r) x ≐ qadd (evaluate (entry G r) x) (evaluate (constantRow C m a d r) x) :=
  added_evaluation _ _ _ _ (row_shape_at _ _ _ _ hG hr) (constant_length _ _ _ _ _ hC)
theorem evaluation_before_last (G C m a d r x : PTm n) (hG : Γ ⊢[PRAAx] rowShape G m (a+d))
    (hC : Γ ⊢[PRAAx] length C ≐ succ a) (hr : Γ ⊢[PRAAx] lt (succ r) m) : Γ ⊢[PRAAx]
    entry (values (inject G C m a d) m x) r ≐ entry (values G m x) r := by
  have range := lt_of_le_of_lt (le_succ_self r) hr
  have ne : Γ ⊢[PRAAx] neg (succ r ≐ m) := .impI (lt_irrefl _ _ (lt_congr Prf.hyp0 (.eqRefl _) hr.wk))
  exact (values_lookup _ _ _ _ range).eqTrans ((evaluation_congr (inject_lookup _ _ _ _ _ _ range) (.eqRefl _)).eqTrans
    ((row_evaluation _ _ _ _ _ _ _ hG hC range).eqTrans
      ((qadd_congr (.eqRefl _) ((evaluation_congr (constant_other _ _ _ _ _ ne) (.eqRefl _)).eqTrans (zeros_evaluation _ _))).eqTrans
        ((GaussianReciprocalHorner.qadd_zero_right _ (GaussianRationalHorner.horner_canonical _ _ _)).eqTrans (values_lookup _ _ _ _ range).eqSymm))))

theorem evaluation_last_at (G C m a d r x : PTm n) (hG : Γ ⊢[PRAAx] rowShape G m (a+d))
    (hC : Γ ⊢[PRAAx] length C ≐ succ a) (hLast : Γ ⊢[PRAAx] succ r ≐ m) : Γ ⊢[PRAAx]
    entry (values (inject G C m a d) m x) r ≐ qadd (entry (values G m x) r) (evaluate C x) := by
  have hr := lt_congr (.eqRefl r) hLast (le_refl (succ r))
  exact (values_lookup _ _ _ _ hr).eqTrans ((evaluation_congr (inject_lookup _ _ _ _ _ _ hr) (.eqRefl _)).eqTrans
    ((row_evaluation _ _ _ _ _ _ _ hG hC hr).eqTrans
      (qadd_congr (values_lookup _ _ _ _ hr).eqSymm
        ((evaluation_congr (constant_last _ _ _ _ _ hLast) (.eqRefl _)).eqTrans
          ((pad_evaluation _ _ _).eqTrans (normalized_evaluation _ _))))))

theorem prefix_before_last (G C m a d r x y : PTm n) (hG : Γ ⊢[PRAAx] rowShape G m (a+d))
    (hC : Γ ⊢[PRAAx] length C ≐ succ a) (hLast : Γ ⊢[PRAAx] succ r ≐ m) : Γ ⊢[PRAAx]
    horner (values (inject G C m a d) m x) y r ≐ horner (values G m x) y r := by
  have hGs : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift G) (Syn.shift m) (Syn.shift a+Syn.shift d) := by
    simpa [Fm.shift,Syn.shift] using hG.shift
  have hCs : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C) ≐ succ (Syn.shift a) := by
    simpa [Fm.shift,Syn.shift] using hC.shift
  have last : Γ.map Fm.shift ⊢[PRAAx] succ (Syn.shift r) ≐ Syn.shift m := by simpa [Fm.shift,Syn.shift] using hLast.shift
  apply GaussianRationalLinearProduct.horner_ext _ _ _ r r ?_ (le_refl _)
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift r) :: Γ.map Fm.shift
  have more : Δ ⊢[PRAAx] lt (succ (var 0)) (succ (Syn.shift r)) := (succ_monus_succ (succ (var 0)) (Syn.shift r)).eqTrans Prf.hyp0
  have range : Δ ⊢[PRAAx] lt (succ (var 0)) (Syn.shift m) := lt_congr (.eqRefl _) last.wk more
  simpa only [Δ,Syn.shift,GaussianPolynomialMonicCompanion.subst_values,subst_inject] using
    evaluation_before_last (Syn.shift G) (Syn.shift C) (Syn.shift m) (Syn.shift a) (Syn.shift d) (var 0) (Syn.shift x)
      hGs.wk hCs.wk range

theorem inject_evaluation (G C m a d x y : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hG : Γ ⊢[PRAAx] rowShape G m (a+d)) (hC : Γ ⊢[PRAAx] length C ≐ succ a) : Γ ⊢[PRAAx]
    evaluate (values (inject G C m a d) m x) y ≐ qadd (evaluate (values G m x) y) (evaluate C x) := by
  have positive := RationalIntegerNormalization.positive_form hm
  have original := (congrAp3 hornerF ((values_length G m x).eqTrans positive) (.eqRefl _) (.eqRefl y)).eqTrans
    (GaussianRationalHorner.horner_succ (values G m x) y (pred m))
  exact (congrAp3 hornerF ((values_length (inject G C m a d) m x).eqTrans positive) (.eqRefl _) (.eqRefl y)).eqTrans
    ((GaussianRationalHorner.horner_succ _ _ _).eqTrans
      ((qadd_congr (GaussianRationalSyntheticDivision.qmul_congr
          (prefix_before_last _ _ _ _ _ _ _ _ hG hC positive.eqSymm) (.eqRefl _))
        (evaluation_last_at _ _ _ _ _ _ _ hG hC positive.eqSymm)).eqTrans
        ((GaussianRationalSumAlgebra.qadd_associative _ _ _).eqSymm.eqTrans
          (qadd_congr original.eqSymm (.eqRefl _)))))

def injectF : PR 5 := PTm.toPR (inject (var 0) (var 1) (var 2) (var 3) (var 4))
def run (G C m a d : PTm n) : PTm n := app injectF ![G,C,m,a,d]
@[simp] theorem subst_run {k : ℕ} (σ : Fin n → PTm k) (G C m a d : PTm n) :
    Syn.subst σ (run G C m a d) = run (Syn.subst σ G) (Syn.subst σ C) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ d) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl
theorem program_at (G C m a d : PTm n) : Γ ⊢[PRAAx] run G C m a d ≐ inject G C m a d := by
  simpa [run,injectF] using toPR_eq (Γ := Γ) (inject (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![G,C,m,a,d]
theorem returned_stored (G C m a d : PTm n) : Γ ⊢[PRAAx]
    GaussianPolynomialMultiplicationMatrix.stored (run G C m a d) m (a+d) :=
  GaussianPolynomialMultiplicationMatrix.stored_congr (program_at _ _ _ _ _).eqSymm (.eqRefl _) (.eqRefl _) (inject_stored _ _ _ _ _)
theorem returned_evaluation (G C m a d x y : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hG : Γ ⊢[PRAAx] rowShape G m (a+d)) (hC : Γ ⊢[PRAAx] length C ≐ succ a) : Γ ⊢[PRAAx]
    evaluate (values (run G C m a d) m x) y ≐ qadd (evaluate (values G m x) y) (evaluate C x) :=
  (evaluation_congr (GaussianPolynomialMonicCompanion.values_congr (program_at _ _ _ _ _) (.eqRefl _) (.eqRefl _)) (.eqRefl _)).eqTrans
    (inject_evaluation _ _ _ _ _ _ _ hm hG hC)

theorem actual_constant_injection_stored_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (GaussianPolynomialMultiplicationMatrix.stored (inject (var 0) (var 1) (var 2) (var 3) (var 4)) (var 2) (var 3+var 4)) :=
  closeUniv 5 (inject_stored _ _ _ _ _)
theorem actual_constant_injection_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (lt (var 5) (var 2) ⟶ le (var 6) (var 3+var 4) ⟶ entry (entry (inject (var 0) (var 1) (var 2) (var 3) (var 4)) (var 5)) (var 6) ≐
      qadd (entry (entry (var 0) (var 5)) (var 6)) (entry (constantRow (var 1) (var 2) (var 3) (var 4) (var 5)) (var 6))) :=
  closeUniv 7 (.impI (.impI (coefficient_lookup _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_constant_injection_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (le one (var 2) ⟶ rowShape (var 0) (var 2) (var 3+var 4) ⟶ length (var 1) ≐ succ (var 3) ⟶
      evaluate (values (inject (var 0) (var 1) (var 2) (var 3) (var 4)) (var 2) (var 5)) (var 6) ≐
        qadd (evaluate (values (var 0) (var 2) (var 5)) (var 6)) (evaluate (var 1) (var 5))) :=
  closeUniv 7 (.impI (.impI (.impI (inject_evaluation _ _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_constant_injection_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ inject (var 0) (var 1) (var 2) (var 3) (var 4)) := closeUniv 5 (program_at _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianPolynomialConstantInjection

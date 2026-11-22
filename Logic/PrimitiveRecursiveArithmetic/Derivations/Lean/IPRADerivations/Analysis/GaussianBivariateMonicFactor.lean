import IPRADerivations.Analysis.GaussianPolynomialMonicCompanion

/-!
# The full stored monic factor

The coefficient table stores the constant-one X polynomial as the
leading Y row and keeps the original tail rows. Specialization recovers
the existing scalar monic polynomial at each numerical X query.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBivariateMonicFactor

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianPolynomialMonicCompanion
  (rowShape row_shape_at monicRow monic_row_length values values_length values_lookup
    monicValues monic_length monic_head monic_tail evaluation_congr)
open GaussianRationalHorner (evaluate hornerF)
open GaussianRationalMonicReduction (constant_evaluation)
open GaussianRationalSyntheticDivision (qone qone_canonical)
open GaussianTranslatedNonconstant (recode_eq)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open LeanProofs.IPRA.PTm (pred)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def row (F c i : PTm n) : PTm n :=
  RationalArithmetic.select (Signum.sg i) (monicRow c) (entry F (pred i))

def rowBody : PTm 2 := row (fstT (var 1)) (sndT (var 1)) (var 0)

def table (F m c : PTm n) : PTm n := sequence rowBody (succ m) (pairT F c)

@[simp] theorem subst_row {k : ℕ} (σ : Fin n → PTm k) (F c i : PTm n) :
    Syn.subst σ (row F c i) = row (Syn.subst σ F) (Syn.subst σ c) (Syn.subst σ i) := by
  simp [row, Signum.sg]

@[simp] theorem subst_table {k : ℕ} (σ : Fin n → PTm k) (F m c : PTm n) :
    Syn.subst σ (table F m c) = table (Syn.subst σ F) (Syn.subst σ m) (Syn.subst σ c) := by
  simp [table]

theorem row_body_at (F c i : PTm n) : Γ ⊢[PRAAx] inst2 rowBody i (pairT F c) ≐ row F c i := by
  simp only [rowBody, inst2, subst_row, subst_fstT, subst_sndT, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  simpa only [subst_row, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] using Prf.eqCongr (Γ := Γ) (row (var 0) (var 1) (var 2) : PTm 3)
      (σ := ![fstT (pairT F c), sndT (pairT F c), i]) (σ' := ![F, c, i])
      (fun k => by fin_cases k; exact fst_pair _ _; exact snd_pair _ _; exact .eqRefl _)

theorem table_length (F m c : PTm n) : Γ ⊢[PRAAx] length (table F m c) ≐ succ m := sequence_length _ _ _

theorem table_lookup (F m c i : PTm n) (hi : Γ ⊢[PRAAx] lt i (succ m)) :
    Γ ⊢[PRAAx] entry (table F m c) i ≐ row F c i :=
  (sequence_decode rowBody (x := pairT F c) hi).eqTrans (row_body_at F c i)

theorem table_head (F m c : PTm n) :
    Γ ⊢[PRAAx] entry (table F m c) zero ≐ monicRow c :=
  (table_lookup F m c zero (zero_lt_succ m)).eqTrans (RationalArithmetic.select_zero _ _ _ Signum.sg_zero)

theorem table_tail (F m c i : PTm n) (hi : Γ ⊢[PRAAx] lt i m) :
    Γ ⊢[PRAAx] entry (table F m c) (succ i) ≐ entry F i :=
  (table_lookup F m c (succ i) ((succ_monus_succ _ _).eqTrans hi)).eqTrans
    ((RationalArithmetic.select_one _ _ _ (Signum.sg_succ i)).eqTrans (entry_congr (.eqRefl F) (pred_succ i)))

theorem table_row_length (F m c i : PTm n) (hF : Γ ⊢[PRAAx] rowShape F m c)
    (hi : Γ ⊢[PRAAx] lt i (succ m)) : Γ ⊢[PRAAx] length (entry (table F m c) i) ≐ succ c := by
  refine .orE (zero_or_succ i) ?_ ?_
  · exact (congrFst ((entry_congr (.eqRefl (table F m c)) Prf.hyp0).eqTrans (table_head _ _ _))).eqTrans
      (monic_row_length c)
  · let Δ := (i ≐ succ (pred i)) :: Γ
    have below : Δ ⊢[PRAAx] lt (succ (pred i)) (succ m) :=
      lt_congr (Prf.hyp0 : Δ ⊢[PRAAx] i ≐ succ (pred i)) (.eqRefl _) hi.wk
    have bound : Δ ⊢[PRAAx] lt (pred i) m :=
      (succ_monus_succ (succ (pred i)) m).eqSymm.eqTrans below
    exact (congrFst ((entry_congr (.eqRefl (table F m c)) Prf.hyp0).eqTrans (table_tail F m c (pred i) bound))).eqTrans
      (row_shape_at F m c (pred i) hF.wk bound)

theorem table_shape (F m c : PTm n) (hF : Γ ⊢[PRAAx] rowShape F m c) :
    Γ ⊢[PRAAx] rowShape (table F m c) (succ m) c := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift F) (Syn.shift m) (Syn.shift c) := by
    simpa [Fm.shift, Syn.shift] using hF.shift
  refine .allI (.impI ?_)
  simpa only [Syn.shift, subst_table, ConciseIPRA.PTm.subst_succ] using
    table_row_length (Syn.shift F) (Syn.shift m) (Syn.shift c) (var 0) hs.wk Prf.hyp0

theorem specialization (F m c x i : PTm n) (hi : Γ ⊢[PRAAx] lt i (succ m)) :
    Γ ⊢[PRAAx] entry (values (table F m c) (succ m) x) i ≐ entry (monicValues F m x) i := by
  let C := values (table F m c) (succ m) x
  let D := monicValues F m x
  refine .orE (zero_or_succ i) ?_ ?_
  · have lhs := (values_lookup (Γ := (i ≐ zero) :: Γ) (table F m c) (succ m) x zero
      (zero_lt_succ m)).eqTrans
        ((evaluation_congr (table_head F m c) (.eqRefl x)).eqTrans
          ((constant_evaluation qone (succ c) x).eqTrans (recode_eq _ qone_canonical)))
    exact (entry_congr (.eqRefl C) Prf.hyp0).eqTrans
      (lhs.eqTrans ((monic_head F m x).eqSymm.eqTrans (entry_congr (.eqRefl D) Prf.hyp0).eqSymm))
  · let Δ := (i ≐ succ (pred i)) :: Γ
    have below : Δ ⊢[PRAAx] lt (succ (pred i)) (succ m) :=
      lt_congr (Prf.hyp0 : Δ ⊢[PRAAx] i ≐ succ (pred i)) (.eqRefl _) hi.wk
    have bound : Δ ⊢[PRAAx] lt (pred i) m :=
      (succ_monus_succ (succ (pred i)) m).eqSymm.eqTrans below
    have lhs := (values_lookup (table F m c) (succ m) x (succ (pred i))
      ((succ_monus_succ _ _).eqTrans bound)).eqTrans
        (evaluation_congr (table_tail F m c (pred i) bound) (.eqRefl x))
    exact (entry_congr (.eqRefl C) Prf.hyp0).eqTrans
      (lhs.eqTrans ((monic_tail F m x (pred i) bound).eqSymm.eqTrans (entry_congr (.eqRefl D) Prf.hyp0).eqSymm))

theorem table_evaluation (F m c x y : PTm n) :
    Γ ⊢[PRAAx] evaluate (values (table F m c) (succ m) x) y ≐ evaluate (monicValues F m x) y := by
  let C := values (table F m c) (succ m) x
  let D := monicValues F m x
  have entries : Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift (succ m)) ⟶ entry (Syn.shift C) (var 0) ≐ entry (Syn.shift D) (var 0)) := by
    refine .allI (.impI ?_)
    simpa only [C, D, Syn.shift, subst_table, GaussianPolynomialMonicCompanion.subst_values,
      GaussianPolynomialMonicCompanion.subst_monicValues, ConciseIPRA.PTm.subst_succ] using
      specialization (Syn.shift F) (Syn.shift m) (Syn.shift c) (Syn.shift x) (var 0) Prf.hyp0
  exact (congrAp3 hornerF (values_length _ _ _) (.eqRefl C) (.eqRefl y)).eqTrans
    ((GaussianRationalLinearProduct.horner_ext C D y (succ m) (succ m) entries (le_refl _)).eqTrans
      (congrAp3 hornerF (monic_length _ _ _).eqSymm (.eqRefl D) (.eqRefl y)))

theorem actual_monic_factor_shape_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (rowShape (var 0) (var 1) (var 2) ⟶
      rowShape (table (var 0) (var 1) (var 2)) (succ (var 1)) (var 2)) :=
  closeUniv 3 (.impI (table_shape _ _ _ Prf.hyp0))

theorem actual_monic_factor_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (evaluate (values (table (var 0) (var 1) (var 2)) (succ (var 1)) (var 3)) (var 4) ≐
      evaluate (monicValues (var 0) (var 1) (var 3)) (var 4)) :=
  closeUniv 5 (table_evaluation _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianBivariateMonicFactor

import IPRADerivations.Analysis.Polynomials.GaussianPolynomialMultiplicationMatrix
import IPRADerivations.Foundations.GuardedTotalization

/-!
# Multiplication by the second indeterminate in rectangular storage

The output pads and canonicalizes each original coefficient row, then
appends a polynomial-zero row. Specialization of the second variable
agrees with the actual scalar append-zero operation.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialYShift

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianPolynomialMonicCompanion (values values_length values_lookup rowShape row_shape_at normalizedRow
  normalized_length normalized_evaluation normalized_canonical pad_canonical)
open GaussianPolynomialMultiplicationMatrix (stored)
open GaussianRationalHorner (evaluate hornerF qmul)
open GaussianRationalPolynomialBuffers (zeros zeros_length zeros_evaluation leftPad pad_length pad_evaluation
  appendZero append_length append_lookup append_evaluation)
open GaussianRationalLinearProduct (horner_ext padded_inside padded_outside)
open GaussianRationalSyntheticDivision (canonicalCoefficients)
open LeanProofs.IPRA.Foundations.GuardedTotalization (sel sel_one sel_zero)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open ConciseIPRA.PTm (succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def row (G m a d r : PTm n) : PTm n :=
  sel (eqb r m) (zeros (succ (a+d))) (leftPad (normalizedRow (entry G r)) d)

def data (G m a d : PTm n) : PTm n := pairT G (pairT m (pairT a d))
def rowBody : PTm 2 := row (fstT (var 1)) (fstT (sndT (var 1)))
  (fstT (sndT (sndT (var 1)))) (sndT (sndT (sndT (var 1)))) (var 0)
def shiftY (G m a d : PTm n) : PTm n := sequence rowBody (succ m) (data G m a d)

@[simp] theorem subst_row {k : ℕ} (σ : Fin n → PTm k) (G m a d r : PTm n) :
    Syn.subst σ (row G m a d r) = row (Syn.subst σ G) (Syn.subst σ m)
      (Syn.subst σ a) (Syn.subst σ d) (Syn.subst σ r) := by simp [row,sel]
@[simp] theorem subst_data {k : ℕ} (σ : Fin n → PTm k) (G m a d : PTm n) :
    Syn.subst σ (data G m a d) = data (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ d) := by
  simp [data]
@[simp] theorem subst_shiftY {k : ℕ} (σ : Fin n → PTm k) (G m a d : PTm n) :
    Syn.subst σ (shiftY G m a d) = shiftY (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ d) := by
  simp [shiftY]

theorem row_body_at (G m a d r : PTm n) : Γ ⊢[PRAAx] inst2 rowBody r (data G m a d) ≐ row G m a d r := by
  have tail := snd_pair (Γ := Γ) G (pairT m (pairT a d))
  have rest := (congrSnd tail).eqTrans (snd_pair m (pairT a d))
  simp only [rowBody,inst2,subst_row,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  simpa using Prf.eqCongr (Γ := Γ) (row (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
    (σ := ![fstT (data G m a d),fstT (sndT (data G m a d)),fstT (sndT (sndT (data G m a d))),
      sndT (sndT (sndT (data G m a d))),r])
    (σ' := ![G,m,a,d,r]) (fun j => by
      fin_cases j
      · exact fst_pair _ _
      · exact (congrFst tail).eqTrans (fst_pair _ _)
      · exact (congrFst rest).eqTrans (fst_pair _ _)
      · exact (congrSnd rest).eqTrans (snd_pair _ _)
      · exact .eqRefl _)
theorem shift_length (G m a d : PTm n) : Γ ⊢[PRAAx] length (shiftY G m a d) ≐ succ m := sequence_length _ _ _
theorem shift_lookup (G m a d r : PTm n) (hr : Γ ⊢[PRAAx] lt r (succ m)) : Γ ⊢[PRAAx]
    entry (shiftY G m a d) r ≐ row G m a d r :=
  (sequence_decode rowBody hr).eqTrans (row_body_at _ _ _ _ _)
theorem last_row (G m a d r : PTm n) (hr : Γ ⊢[PRAAx] r ≐ m) : Γ ⊢[PRAAx] row G m a d r ≐ zeros (succ (a+d)) :=
  sel_one (eqb_of_eq hr)
theorem earlier_row (G m a d r : PTm n) (hr : Γ ⊢[PRAAx] lt r m) :
    Γ ⊢[PRAAx] row G m a d r ≐ leftPad (normalizedRow (entry G r)) d :=
  sel_zero (eqb_of_ne (.impI (lt_irrefl _ _ (lt_congr (.eqRefl _) Prf.hyp0.eqSymm hr.wk))))
theorem padded_length (G m a d r : PTm n) (hG : Γ ⊢[PRAAx] rowShape G m a) (hr : Γ ⊢[PRAAx] lt r m) :
    Γ ⊢[PRAAx] length (leftPad (normalizedRow (entry G r)) d) ≐ succ (a+d) :=
  (pad_length _ _).eqTrans
    ((congrAdd (.eqRefl _) ((normalized_length _).eqTrans (row_shape_at _ _ _ _ hG hr))).eqTrans (by ipra_ring))

theorem shifted_row_length (G m a d r : PTm n) (hG : Γ ⊢[PRAAx] rowShape G m a)
    (hr : Γ ⊢[PRAAx] lt r (succ m)) : Γ ⊢[PRAAx] length (entry (shiftY G m a d) r) ≐ succ (a+d) := by
  have eq := shift_lookup G m a d r hr
  refine .orE (lt_or_eq_of_le ((succ_monus_succ _ _).eqSymm.eqTrans hr)) ?_ ?_
  · exact (congrFst (eq.wk.eqTrans (earlier_row _ _ _ _ _ Prf.hyp0))).eqTrans (padded_length _ _ _ _ _ hG.wk Prf.hyp0)
  · exact (congrFst (eq.wk.eqTrans (last_row _ _ _ _ _ Prf.hyp0))).eqTrans (zeros_length _)

theorem shifted_row_canonical (G m a d r : PTm n) (hr : Γ ⊢[PRAAx] lt r (succ m)) :
    Γ ⊢[PRAAx] canonicalCoefficients (entry (shiftY G m a d) r) := by
  have eq := shift_lookup G m a d r hr
  refine .orE (lt_or_eq_of_le ((succ_monus_succ _ _).eqSymm.eqTrans hr)) ?_ ?_
  · exact GaussianRationalMonicReduction.canonical_coefficients_congr (eq.wk.eqTrans (earlier_row _ _ _ _ _ Prf.hyp0))
      (pad_canonical _ _ (normalized_canonical _))
  · exact GaussianRationalMonicReduction.canonical_coefficients_congr (eq.wk.eqTrans (last_row _ _ _ _ _ Prf.hyp0))
      (GaussianRationalMonicReduction.zeros_canonical _)

theorem shift_stored (G m a d : PTm n) (hG : Γ ⊢[PRAAx] rowShape G m a) :
    Γ ⊢[PRAAx] stored (shiftY G m a d) (succ m) (a+d) := by
  have hGs : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift G) (Syn.shift m) (Syn.shift a) := by
    simpa [Fm.shift,Syn.shift] using hG.shift
  refine .andI (shift_length _ _ _ _) (.andI (.allI (.impI ?_)) (.allI (.impI ?_)))
  · simpa [Syn.shift] using shifted_row_length (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift d) (var 0) hGs.wk Prf.hyp0
  · simpa [Syn.shift] using shifted_row_canonical (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift d) (var 0) Prf.hyp0

theorem specialized_entry (G m a d x r : PTm n) (hr : Γ ⊢[PRAAx] lt r (succ m)) :
    Γ ⊢[PRAAx] entry (values (shiftY G m a d) (succ m) x) r ≐ entry (appendZero (values G m x)) r := by
  let C := values G m x
  have len := values_length (Γ := Γ) G m x
  have hle := (succ_monus_succ _ _).eqSymm.eqTrans hr
  have new := (values_lookup _ _ _ _ hr).eqTrans
    (GaussianPolynomialMonicCompanion.evaluation_congr (shift_lookup G m a d r hr) (.eqRefl x))
  have old := append_lookup C r (le_congr (.eqRefl r) len.eqSymm hle)
  refine .orE (lt_or_eq_of_le hle) ?_ ?_
  · have ev := (GaussianPolynomialMonicCompanion.evaluation_congr (Γ := lt r m :: Γ)
      (earlier_row G m a d r Prf.hyp0) (.eqRefl x)).eqTrans
      ((pad_evaluation _ _ _).eqTrans (normalized_evaluation _ _))
    have read := (old.wk.eqTrans (padded_inside C (length C) r (lt_congr (.eqRefl r) len.wk.eqSymm Prf.hyp0))).eqTrans
      (values_lookup G m x r Prf.hyp0)
    exact new.wk.eqTrans (ev.eqTrans read.eqSymm)
  · have ev := (GaussianPolynomialMonicCompanion.evaluation_congr (Γ := (r ≐ m) :: Γ)
      (last_row G m a d r Prf.hyp0) (.eqRefl x)).eqTrans
      (zeros_evaluation _ _)
    have read := old.wk.eqTrans (padded_outside C (length C) r (le_congr len.wk.eqSymm Prf.hyp0.eqSymm (le_refl m)))
    exact new.wk.eqTrans (ev.eqTrans read.eqSymm)

theorem shift_evaluation (G m a d x y : PTm n) : Γ ⊢[PRAAx]
    evaluate (values (shiftY G m a d) (succ m) x) y ≐ qmul y (evaluate (values G m x) y) := by
  let C := values (shiftY G m a d) (succ m) x
  let D := appendZero (values G m x)
  have entries : Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift (succ m)) ⟶ entry (Syn.shift C) (var 0) ≐ entry (Syn.shift D) (var 0)) := by
    refine .allI (.impI ?_)
    simpa [C,D,Syn.shift] using specialized_entry (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift d) (Syn.shift x) (var 0) Prf.hyp0
  have dLength := (append_length (Γ := Γ) (values G m x)).eqTrans (congrSucc (values_length G m x))
  exact (congrAp3 hornerF (values_length _ _ _) (.eqRefl _) (.eqRefl _)).eqTrans
    ((horner_ext C D y (succ m) (succ m) entries (le_refl _)).eqTrans
      ((congrAp3 hornerF dLength.eqSymm (.eqRefl _) (.eqRefl _)).eqTrans ((append_evaluation _ _).eqTrans
        (GaussianRationalPowerAlgebra.qmul_commutative _ _))))

theorem actual_y_shift_stored_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (rowShape (var 0) (var 1) (var 2) ⟶ stored (shiftY (var 0) (var 1) (var 2) (var 3))
      (succ (var 1)) (var 2 + var 3)) :=
  closeUniv 4 (.impI (shift_stored _ _ _ _ Prf.hyp0))

theorem actual_y_shift_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (evaluate (values (shiftY (var 0) (var 1) (var 2) (var 3)) (succ (var 1)) (var 4)) (var 5) ≐
      qmul (var 5) (evaluate (values (var 0) (var 1) (var 4)) (var 5))) :=
  closeUniv 6 (shift_evaluation _ _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianPolynomialYShift

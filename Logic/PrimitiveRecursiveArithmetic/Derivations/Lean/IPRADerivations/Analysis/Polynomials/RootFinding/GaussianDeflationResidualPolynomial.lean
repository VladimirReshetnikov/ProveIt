import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianDeflationTelescoping
import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianApproximateFactorization
import IPRADerivations.Analysis.Polynomials.GaussianRationalGridCoefficientEquality
import IPRADerivations.Core.CongruenceTactic

/-!
# The stored telescoping residual polynomial

Each actual residual scales the polynomial of the preceding roots. The
scaled terms are padded to the original degree and added coefficientwise.
Evaluation of this stored sum agrees with the residual telescope, and exact
grid reflection identifies its coefficients with the original difference.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianDeflationResidualPolynomial

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianDeflationTelescoping (residuals residualSum residual_sum_zero residual_sum_succ telescoping_evaluation)
open GaussianRationalDeflation (roots)
open GaussianVandermondeNewtonPolynomials (polynomial polynomial_length evaluation_product)
open GaussianRationalHorner (evaluate qzero qmul qadd canonical qadd_canonical)
open GaussianRationalSyntheticDivision (qone qzero_canonical qadd_congr qmul_congr)
open GaussianRationalMetric (qsub_canonical)
open GaussianRationalCoefficientScaling (scaled scaled_length scaled_lookup evaluation_linearity)
open GaussianRationalPolynomialBuffers
  (leftPad pad_length pad_leading pad_tail pad_evaluation zeros zeros_length zeros_lookup zeros_evaluation
    added added_length added_lookup added_evaluation)
open GaussianRationalGridCoefficientEquality (gridEqual coefficient_recode_equal)
open GaussianRationalFiniteGridIdentity (gridPoint)
open GaussianCoefficientL1 (subCoefficients sub_lookup)
open GaussianRationalMonicCompanion (difference_evaluation sub_length)
open GaussianTranslatedNonconstant (recode_eq)
open GaussianRationalReconstruction (evaluate_congr)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open LeanProofs.IPRA.PTm (monus)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def contribution (S R N j : PTm n) : PTm n :=
  leftPad (scaled (polynomial S j) (entry R j)) (monus N j)

@[simp] theorem subst_contribution {k : ℕ} (σ : Fin n → PTm k) (S R N j : PTm n) :
    Syn.subst σ (contribution S R N j) = contribution (Syn.subst σ S) (Syn.subst σ R)
      (Syn.subst σ N) (Syn.subst σ j) := by simp [contribution]

theorem contribution_length (S R N j : PTm n) (hj : Γ ⊢[PRAAx] le j N) :
    Γ ⊢[PRAAx] length (contribution S R N j) ≐ succ N := by
  have len := (scaled_length (Γ := Γ) (polynomial S j) (entry R j)).eqTrans (polynomial_length S j)
  exact (pad_length _ _).eqTrans ((congrAdd (.eqRefl _) len).eqTrans
    ((by ipra_ring : Γ ⊢[PRAAx] monus N j + succ j ≐ succ (j + monus N j)).eqTrans
      (congrSucc (eq_add_of_le hj).eqSymm)))

theorem contribution_padding (S R N j i : PTm n) (hi : Γ ⊢[PRAAx] lt i (monus N j)) :
    Γ ⊢[PRAAx] entry (contribution S R N j) i ≐ qzero := pad_leading _ _ _ hi

theorem contribution_coefficient (S R N j i : PTm n) (hi : Γ ⊢[PRAAx] le i j) :
    Γ ⊢[PRAAx] entry (contribution S R N j) (monus N j + i) ≐
      qmul (entry R j) (entry (polynomial S j) i) := by
  have bound : Γ ⊢[PRAAx] lt i (length (polynomial S j)) :=
    lt_congr (.eqRefl _) (polynomial_length S j).eqSymm ((succ_monus_succ _ _).eqTrans hi)
  exact (pad_tail _ _ _ (lt_congr (.eqRefl _) (scaled_length _ _).eqSymm bound)).eqTrans
    (scaled_lookup _ _ _ bound)

theorem contribution_evaluation (S R N j y : PTm n) :
    Γ ⊢[PRAAx] evaluate (contribution S R N j) y ≐ qmul (entry R j)
      (GaussianVandermondeNewtonPolynomials.differenceProduct S y j) :=
  (pad_evaluation _ _ _).eqTrans ((evaluation_linearity _ _ _).eqTrans
    (qmul_congr (.eqRefl _) (evaluation_product S j y)))

def data (S R N : PTm n) : PTm n := pairT S (pairT R N)
def baseBody : PTm 1 := zeros (succ (sndT (sndT (var 0))))
def update (S R N j old : PTm n) : PTm n := added old (contribution S R N j) (succ N)
def stepBody : PTm 3 := update (fstT (var 2)) (fstT (sndT (var 2)))
  (sndT (sndT (var 2))) (var 0) (var 1)
def foldF : PR 2 := rec2 baseBody stepBody
def fold (S R N j : PTm n) : PTm n := ap2 foldF j (data S R N)

@[simp] theorem subst_data {k : ℕ} (σ : Fin n → PTm k) (S R N : PTm n) :
    Syn.subst σ (data S R N) = data (Syn.subst σ S) (Syn.subst σ R) (Syn.subst σ N) := by simp [data]
@[simp] theorem subst_update {k : ℕ} (σ : Fin n → PTm k) (S R N j old : PTm n) :
    Syn.subst σ (update S R N j old) = update (Syn.subst σ S) (Syn.subst σ R) (Syn.subst σ N)
      (Syn.subst σ j) (Syn.subst σ old) := by simp [update]
@[simp] theorem subst_fold {k : ℕ} (σ : Fin n → PTm k) (S R N j : PTm n) :
    Syn.subst σ (fold S R N j) = fold (Syn.subst σ S) (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ j) := by
  simp [fold]

theorem fold_zero (S R N : PTm n) : Γ ⊢[PRAAx] fold S R N zero ≐ zeros (succ N) := by
  have inner := (congrSnd (snd_pair (Γ := Γ) S (pairT R N))).eqTrans (snd_pair R N)
  have base := rec2_zero (Γ := Γ) baseBody stepBody (data S R N)
  simp only [baseBody, GaussianRationalPolynomialBuffers.subst_zeros, ConciseIPRA.PTm.subst_succ,
    subst_sndT, Syn.subst_var, Matrix.cons_val_zero] at base
  have eq : Γ ⊢[PRAAx] zeros (succ (sndT (sndT (data S R N)))) ≐ zeros (succ N) := by
    ipra_congr (zeros (succ (var 0)) : PTm 1) with [(show _ ⊢[PRAAx] sndT (sndT (data S R N)) ≐ N from inner)]
  exact base.eqTrans eq

theorem fold_succ (S R N j : PTm n) :
    Γ ⊢[PRAAx] fold S R N (succ j) ≐ update S R N j (fold S R N j) := by
  have step := rec2_succ (Γ := Γ) baseBody stepBody j (data S R N)
  simp only [stepBody, subst_update, subst_fstT, subst_sndT, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at step
  have tail := snd_pair (Γ := Γ) S (pairT R N)
  have args : Γ ⊢[PRAAx] update (fstT (data S R N)) (fstT (sndT (data S R N))) (sndT (sndT (data S R N))) j
      (fold S R N j) ≐ update S R N j (fold S R N j) := by
    simpa only [subst_update, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons] using
      Prf.eqCongr (Γ := Γ) (update (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
        (σ := ![fstT (data S R N), fstT (sndT (data S R N)), sndT (sndT (data S R N)), j, fold S R N j])
        (σ' := ![S, R, N, j, fold S R N j]) (fun i => by
          fin_cases i
          · exact fst_pair _ _
          · exact (congrFst tail).eqTrans (fst_pair _ _)
          · exact (congrSnd tail).eqTrans (snd_pair _ _)
          · exact .eqRefl _
          · exact .eqRefl _)
  exact step.eqTrans args

theorem fold_length (S R N j : PTm n) : Γ ⊢[PRAAx] length (fold S R N j) ≐ succ N := by
  refine .orE (zero_or_succ j) ?_ ?_
  · exact (congrFst ((congrAp2 foldF Prf.hyp0 (.eqRefl _)).eqTrans (fold_zero S R N))).eqTrans (zeros_length _)
  · exact (congrFst ((congrAp2 foldF Prf.hyp0 (.eqRefl _)).eqTrans
      (fold_succ S R N (PTm.pred j)))).eqTrans (added_length _ _ _)

theorem fold_coefficient_succ (S R N j i : PTm n) (hi : Γ ⊢[PRAAx] lt i (succ N)) :
    Γ ⊢[PRAAx] entry (fold S R N (succ j)) i ≐
      qadd (entry (fold S R N j) i) (entry (contribution S R N j) i) :=
  (Foundations.SequenceComposition.entry_congr (fold_succ S R N j) (.eqRefl i)).eqTrans
    (added_lookup _ _ _ _ hi)

theorem fold_coefficient_canonical (S R N j i : PTm n) (hi : Γ ⊢[PRAAx] lt i (succ N)) :
    Γ ⊢[PRAAx] canonical (entry (fold S R N j) i) := by
  refine .orE (zero_or_succ j) ?_ ?_
  · have e : (j ≐ zero) :: Γ ⊢[PRAAx] entry (fold S R N j) i ≐ qzero :=
      (Foundations.SequenceComposition.entry_congr
        ((congrAp2 foldF Prf.hyp0 (.eqRefl (data S R N))).eqTrans (fold_zero S R N)) (.eqRefl i)).eqTrans
          (zeros_lookup _ _ hi.wk)
    exact GaussianRationalHorner.canonical_congr e qzero_canonical
  · have e : (j ≐ succ (PTm.pred j)) :: Γ ⊢[PRAAx] entry (fold S R N j) i ≐
        qadd (entry (fold S R N (PTm.pred j)) i) (entry (contribution S R N (PTm.pred j)) i) :=
      (Foundations.SequenceComposition.entry_congr (congrAp2 foldF Prf.hyp0 (.eqRefl (data S R N)))
        (.eqRefl i)).eqTrans (fold_coefficient_succ S R N (PTm.pred j) i hi.wk)
    exact GaussianRationalHorner.canonical_congr e (qadd_canonical _ _)

theorem fold_evaluation_step (S R N j y : PTm n) (hj : Γ ⊢[PRAAx] le j N)
    (ih : Γ ⊢[PRAAx] evaluate (fold S R N j) y ≐ residualSum S R j y) :
    Γ ⊢[PRAAx] evaluate (fold S R N (succ j)) y ≐ residualSum S R (succ j) y :=
  (evaluate_congr (fold_succ S R N j) (.eqRefl y)).eqTrans
    ((added_evaluation _ _ _ _ (fold_length S R N j) (contribution_length S R N j hj)).eqTrans
      ((qadd_congr ih (contribution_evaluation S R N j y)).eqTrans (residual_sum_succ S R j y).eqSymm))

theorem fold_evaluation (S R N j y : PTm n) (hj : Γ ⊢[PRAAx] le j N) :
    Γ ⊢[PRAAx] evaluate (fold S R N j) y ≐ residualSum S R j y := by
  have all : Γ ⊢[PRAAx] .all (le (var 0) (Syn.shift N) ⟶
      evaluate (fold (Syn.shift S) (Syn.shift R) (Syn.shift N) (var 0)) (Syn.shift y) ≐
        residualSum (Syn.shift S) (Syn.shift R) (var 0) (Syn.shift y)) := by
    refine PRA.qfInd _ ⟨le_QF _ _, trivial⟩ ?_ ?_
    · simp only [Fm.subst_imp, subst_le, Fm.subst_eq, GaussianRationalHorner.subst_evaluate, subst_fold,
        GaussianDeflationTelescoping.subst_residualSum, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      exact .impI ((evaluate_congr (fold_zero S R N) (.eqRefl y)).eqTrans
        ((zeros_evaluation _ _).eqTrans (residual_sum_zero S R y).eqSymm))
    · simp only [Fm.subst_imp, subst_le, Fm.subst_eq, GaussianRationalHorner.subst_evaluate, subst_fold,
        GaussianDeflationTelescoping.subst_residualSum, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      exact .impI (fold_evaluation_step _ _ _ _ _ (le_trans (le_succ_self _) Prf.hyp0)
        (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)))
  have rule : Γ ⊢[PRAAx] le j N ⟶ evaluate (fold S R N j) y ≐ residualSum S R j y := by
    simpa only [Fm.subst_imp, subst_le, Fm.subst_eq, GaussianRationalHorner.subst_evaluate, subst_fold,
      GaussianDeflationTelescoping.subst_residualSum, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using all.allE j
  exact .impE rule hj

def difference (step : PR 3) (C N e f : PTm n) : PTm n :=
  subCoefficients C (polynomial (roots step C N e f N) N) (succ N)
def result (step : PR 3) (C N e f : PTm n) : PTm n :=
  fold (roots step C N e f N) (residuals step C N e f) N N

@[simp] theorem subst_difference {k : ℕ} (σ : Fin n → PTm k) (step : PR 3) (C N e f : PTm n) :
    Syn.subst σ (difference step C N e f) =
      difference step (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ e) (Syn.subst σ f) := by simp [difference]
@[simp] theorem subst_result {k : ℕ} (σ : Fin n → PTm k) (step : PR 3) (C N e f : PTm n) :
    Syn.subst σ (result step C N e f) =
      result step (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ e) (Syn.subst σ f) := by simp [result]

theorem exact_evaluation (step : PR 3) (C N e f y : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hM : Γ ⊢[PRAAx] entry C zero ≐ qone) :
    Γ ⊢[PRAAx] evaluate (difference step C N e f) y ≐ evaluate (result step C N e f) y :=
  (difference_evaluation _ _ _ _ hC (polynomial_length _ _)).eqTrans
    ((telescoping_evaluation step C N e f y hC hM).eqTrans (fold_evaluation _ _ _ _ _ (le_refl N)).eqSymm)

theorem coefficient_identity (step : PR 3) (C N e f i : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hM : Γ ⊢[PRAAx] entry C zero ≐ qone) (hi : Γ ⊢[PRAAx] le i N) :
    Γ ⊢[PRAAx] entry (difference step C N e f) i ≐ entry (result step C N e f) i := by
  have cs : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C) ≐ succ (Syn.shift N) := by
    simpa [Fm.shift, Syn.shift] using hC.shift
  have ms : Γ.map Fm.shift ⊢[PRAAx] entry (Syn.shift C) zero ≐ qone := by
    simpa [Fm.shift, Syn.shift] using hM.shift
  have grid : Γ ⊢[PRAAx] gridEqual (difference step C N e f) (result step C N e f) N := by
    refine .allI (.impI ?_)
    simpa only [Syn.shift, subst_difference, subst_result] using
      exact_evaluation step (Syn.shift C) (Syn.shift N) (Syn.shift e) (Syn.shift f) (gridPoint (var 0)) cs.wk ms.wk
  have bound : Γ ⊢[PRAAx] lt i (succ N) := (succ_monus_succ _ _).eqTrans hi
  have left : Γ ⊢[PRAAx] canonical (entry (difference step C N e f) i) :=
    GaussianRationalHorner.canonical_congr (sub_lookup _ _ _ _ bound) (qsub_canonical _ _)
  have same := coefficient_recode_equal _ _ _ _ (sub_length _ _ _) (fold_length _ _ _ _) grid hi
  exact (recode_eq _ left).eqSymm.eqTrans (same.eqTrans
    (recode_eq _ (fold_coefficient_canonical _ _ _ _ _ bound)))

theorem actual_residual_polynomial_identity_closed (step : PR 3) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (length (var 0) ≐ succ (var 1) ⟶ entry (var 0) zero ≐ qone ⟶ le (var 4) (var 1) ⟶
        entry (difference step (var 0) (var 1) (var 2) (var 3)) (var 4) ≐
        entry (result step (var 0) (var 1) (var 2) (var 3)) (var 4)) :=
  closeUniv 5 (.impI (.impI (.impI (coefficient_identity step _ _ _ _ _
    Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

theorem actual_factorization_telescoping_closed (step : PR 3) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (length (var 0) ≐ succ (var 1) ⟶ entry (var 0) zero ≐ qone ⟶ le (var 4) (var 1) ⟶
        entry (subCoefficients (var 0)
          (GaussianApproximateFactorization.productPolynomial step (var 0) (var 1) (var 2) (var 3))
          (succ (var 1))) (var 4) ≐
        entry (result step (var 0) (var 1) (var 2)
          (GaussianFactorParameters.toleranceDenominator (var 0) (var 1) (var 3))) (var 4)) :=
  closeUniv 5 (.impI (.impI (.impI (coefficient_identity step _ _ _ _ _
    Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianDeflationResidualPolynomial

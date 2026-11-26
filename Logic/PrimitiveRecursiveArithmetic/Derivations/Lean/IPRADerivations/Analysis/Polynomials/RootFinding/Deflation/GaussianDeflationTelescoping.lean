import IPRADerivations.Analysis.Polynomials.RootFinding.Deflation.GaussianRationalDeflation
import IPRADerivations.Analysis.Polynomials.Elimination.Vandermonde.GaussianVandermondeNewtonPolynomials

/-!
# The exact residual sum of the computed deflation loop

The original deflation stages supply the residual values. The actual root
list supplies the prefix products. A quantifier-free invariant adds one
residual term at a time, leaving the next quotient times its prefix product.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianDeflationTelescoping

open_ipra
open GaussianRationalDeflation (data polynomial polynomial_zero polynomial_invariant roots roots_lookup rootAt stage_division)
open GaussianVandermondeNewtonPolynomials (differenceProduct difference_zero difference_succ evaluation_product)
open GaussianRationalFiniteSum (sum)
open GaussianRationalHorner (evaluate hornerF horner_zero horner_succ horner_canonical qzero qadd qmul)
open GaussianRationalMetric (qsub)
open GaussianRationalSyntheticDivision
  (qone qone_canonical qzero_canonical qadd_congr qmul_congr qsub_congr qzero_add qmul_zero_left)
open GaussianRationalCoefficientScaling (qmul_add)
open GaussianRationalSumAlgebra (qadd_associative)
open GaussianReciprocalHorner (qadd_commutative qmul_associative qmul_one_right qsub_add_cancel)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReconstruction (evaluate_congr)
open GaussianTranslatedNonconstant (recode_eq)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def residual (step : PR 3) (C N e f i : PTm n) : PTm n :=
  evaluate (polynomial step C N e f i) (rootAt step C N e f i)

def residualBody (step : PR 3) : PTm 2 :=
  residual step (fstT (sndT (var 1))) (fstT (var 1))
    (fstT (sndT (sndT (var 1)))) (sndT (sndT (sndT (var 1)))) (var 0)

def residuals (step : PR 3) (C N e f : PTm n) : PTm n :=
  sequence (residualBody step) N (data C N e f)

ipra_subst residual
ipra_subst residuals

theorem residual_body_at (step : PR 3) (C N e f i : PTm n) :
    Γ ⊢[PRAAx] inst2 (residualBody step) i (data C N e f) ≐ residual step C N e f i := by
  have tail := snd_pair (Γ := Γ) N (pairT C (pairT e f))
  have rest := (congrSnd tail).eqTrans (snd_pair C (pairT e f))
  simp only [residualBody, inst2, subst_residual, subst_fstT, subst_sndT, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  simpa only [subst_residual, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (residual step (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
      (σ := ![fstT (sndT (data C N e f)), fstT (data C N e f), fstT (sndT (sndT (data C N e f))),
        sndT (sndT (sndT (data C N e f))), i]) (σ' := ![C, N, e, f, i]) (fun r => by
          fin_cases r
          · exact tail.fstE
          · exact fst_pair _ _
          · exact rest.fstE
          · exact rest.sndE
          · exact .eqRefl _)

theorem residuals_length (step : PR 3) (C N e f : PTm n) :
    Γ ⊢[PRAAx] length (residuals step C N e f) ≐ N := sequence_length _ _ _

theorem residuals_lookup (step : PR 3) (C N e f i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] entry (residuals step C N e f) i ≐ residual step C N e f i :=
  (sequence_decode (residualBody step) (x := data C N e f) hi).eqTrans (residual_body_at step C N e f i)

def sumData (S R y : PTm n) : PTm n := pairT S (pairT R y)
def sumBody : PTm 2 := qmul (entry (fstT (sndT (var 1))) (var 0))
  (differenceProduct (fstT (var 1)) (sndT (sndT (var 1))) (var 0))
def residualSum (S R j y : PTm n) : PTm n := sum sumBody j (sumData S R y)

ipra_subst sumData
ipra_subst residualSum

theorem sum_body_at (S R y i : PTm n) :
    Γ ⊢[PRAAx] inst2 sumBody i (sumData S R y) ≐ qmul (entry R i) (differenceProduct S y i) := by
  have tail := snd_pair (Γ := Γ) S (pairT R y)
  have productEq : Γ ⊢[PRAAx] differenceProduct (fstT (sumData S R y)) (sndT (sndT (sumData S R y))) i ≐
      differenceProduct S y i := by
    ipra_congr (differenceProduct (var 0) (var 1) (var 2) : PTm 3) with
      [(show _ ⊢[PRAAx] fstT (sumData S R y) ≐ S from fst_pair _ _),
        (show _ ⊢[PRAAx] sndT (sndT (sumData S R y)) ≐ y from tail.sndE), .eqRefl i]
  simp only [sumBody, inst2, GaussianRationalHorner.subst_qmul, GaussianVandermondeNewtonPolynomials.subst_differenceProduct,
    Foundations.MasterCertificate.subst_entry, subst_fstT, subst_sndT, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact qmul_congr (Foundations.SequenceComposition.entry_congr tail.fstE (.eqRefl i)) productEq

theorem residual_sum_zero (S R y : PTm n) : Γ ⊢[PRAAx] residualSum S R zero y ≐ qzero := GaussianRationalFiniteSum.sum_zero _ _
theorem residual_sum_succ (S R j y : PTm n) :
    Γ ⊢[PRAAx] residualSum S R (succ j) y ≐
      qadd (residualSum S R j y) (qmul (entry R j) (differenceProduct S y j)) :=
  (GaussianRationalFiniteSum.sum_succ sumBody j (sumData S R y)).eqTrans (qadd_congr (.eqRefl _) (sum_body_at S R y j))

def invariant (step : PR 3) (C N e f j y : PTm n) : Fm PTm n :=
  le j N ⟶ evaluate C y ≐
    qadd (residualSum (roots step C N e f N) (residuals step C N e f) j y)
      (qmul (differenceProduct (roots step C N e f N) y j) (evaluate (polynomial step C N e f j) y))

ipra_subst invariant

theorem invariant_base (step : PR 3) (C N e f y : PTm n) :
    Γ ⊢[PRAAx] invariant step C N e f zero y := by
  refine .impI ?_
  let Δ := le zero N :: Γ
  have p := evaluate_congr (Γ := Δ) (polynomial_zero step C N e f) (.eqRefl y)
  have unit := GaussianRationalFiniteProduct.raw_one_left (Γ := Δ) (evaluate C y)
  exact ((qadd_congr (residual_sum_zero _ _ _)
    ((qmul_congr (difference_zero _ _) p).eqTrans (unit.eqTrans (recode_eq _ (horner_canonical _ _ _))))).eqTrans
      (qzero_add (evaluate C y) (horner_canonical _ _ _))).eqSymm

theorem invariant_step (step : PR 3) (C N e f j y : PTm n)
    (hC : Γ ⊢[PRAAx] length C ≐ succ N) (hM : Γ ⊢[PRAAx] entry C zero ≐ qone)
    (ih : Γ ⊢[PRAAx] invariant step C N e f j y) :
    Γ ⊢[PRAAx] invariant step C N e f (succ j) y := by
  let S := roots step C N e f N
  let R := residuals step C N e f
  let B := differenceProduct S y j
  let L := residualSum S R j y
  let Z := qsub y (rootAt step C N e f j)
  let V := evaluate (polynomial step C N e f (succ j)) y
  let E := residual step C N e f j
  refine .impI ?_
  have hj : lt j N :: Γ ⊢[PRAAx] lt j N := Prf.hyp0
  have split := stage_division step C N e f j y hC.wk hM.wk hj
  have fac : lt j N :: Γ ⊢[PRAAx] differenceProduct S y (succ j) ≐ qmul B Z :=
    (difference_succ S y j).eqTrans (qmul_congr (.eqRefl _) (qsub_congr (.eqRefl _) (roots_lookup step C N e f N j hj)))
  have term : lt j N :: Γ ⊢[PRAAx] residualSum S R (succ j) y ≐ qadd L (qmul E B) :=
    (residual_sum_succ S R j y).eqTrans (qadd_congr (.eqRefl _) (qmul_congr (residuals_lookup step C N e f j hj) (.eqRefl _)))
  have expansion : lt j N :: Γ ⊢[PRAAx] qadd L (qmul B (qadd (qmul Z V) E)) ≐
      qadd (qadd L (qmul E B)) (qmul (qmul B Z) V) :=
    (qadd_congr (.eqRefl _) ((qmul_add B (qmul Z V) E).eqTrans
      ((qadd_congr (qmul_associative _ _ _).eqSymm (qmul_commutative _ _)).eqTrans
        (qadd_commutative _ _)))).eqTrans (qadd_associative _ _ _).eqSymm
  exact (.impE ih.wk (le_of_lt hj) : _ ⊢[PRAAx] _).eqTrans
    ((qadd_congr (.eqRefl _) (qmul_congr (.eqRefl _) split)).eqTrans
      (expansion.eqTrans (qadd_congr term.eqSymm (qmul_congr fac.eqSymm (.eqRefl _)))))

theorem prefix_identity (step : PR 3) (C N e f j y : PTm n)
    (hC : Γ ⊢[PRAAx] length C ≐ succ N) (hM : Γ ⊢[PRAAx] entry C zero ≐ qone) :
    Γ ⊢[PRAAx] invariant step C N e f j y := by
  have cs : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C) ≐ succ (Syn.shift N) := by
    simpa [Fm.shift, Syn.shift] using hC.shift
  have ms : Γ.map Fm.shift ⊢[PRAAx] entry (Syn.shift C) zero ≐ qone := by
    simpa [Fm.shift, Syn.shift] using hM.shift
  have all : Γ ⊢[PRAAx] .all (invariant step (Syn.shift C) (Syn.shift N) (Syn.shift e)
      (Syn.shift f) (var 0) (Syn.shift y)) := by
    ipra_qfind (⟨le_QF _ _, trivial⟩) [subst_invariant]
    · exact invariant_base _ _ _ _ _ _
    · exact invariant_step _ _ _ _ _ _ _ cs.wk ms.wk Prf.hyp0
  simpa only [subst_invariant, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using all.allE j

theorem final_evaluation (step : PR 3) (C N e f y : PTm n)
    (hC : Γ ⊢[PRAAx] length C ≐ succ N) (hM : Γ ⊢[PRAAx] entry C zero ≐ qone) :
    Γ ⊢[PRAAx] evaluate (polynomial step C N e f N) y ≐ qone := by
  let P := polynomial step C N e f N
  have h := polynomial_invariant step C N e f N hC hM (le_refl N)
  have len : Γ ⊢[PRAAx] length P ≐ one := (.andE₁ h : Γ ⊢[PRAAx] _).eqTrans (congrSucc (monus_self N))
  exact (congrAp3 hornerF len (.eqRefl P) (.eqRefl y)).eqTrans
    ((horner_succ P y zero).eqTrans
      ((qadd_congr ((qmul_congr (horner_zero P y) (.eqRefl _)).eqTrans (qmul_zero_left _)) (.andE₂ h)).eqTrans
        (qzero_add _ qone_canonical)))

theorem telescoping_evaluation (step : PR 3) (C N e f y : PTm n)
    (hC : Γ ⊢[PRAAx] length C ≐ succ N) (hM : Γ ⊢[PRAAx] entry C zero ≐ qone) :
    Γ ⊢[PRAAx] qsub (evaluate C y)
      (evaluate (GaussianVandermondeNewtonPolynomials.polynomial (roots step C N e f N) N) y) ≐
      residualSum (roots step C N e f N) (residuals step C N e f) N y := by
  let S := roots step C N e f N
  let L := residualSum S (residuals step C N e f) N y
  have eq := Prf.impE (prefix_identity step C N e f N y hC hM) (le_refl N)
  let prod := differenceProduct S y N
  have last := (qmul_congr (.eqRefl prod) (final_evaluation step C N e f y hC hM)).eqTrans
    (qmul_one_right _ (GaussianRationalFiniteProduct.product_canonical GaussianVandermondeNewtonPolynomials.differenceBody N
      (GaussianVandermondeNewtonPolynomials.differenceData S y)))
  exact (qsub_congr (eq.eqTrans (qadd_congr (.eqRefl L) last)) (evaluation_product S N y)).eqTrans
    (qsub_add_cancel L prod (GaussianRationalFiniteSum.sum_canonical _ _ _))

theorem actual_deflation_residual_sum_evaluation_closed (step : PR 3) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (length (var 0) ≐ succ (var 1) ⟶ entry (var 0) zero ≐ qone ⟶
        qsub (evaluate (var 0) (var 4))
          (evaluate (GaussianVandermondeNewtonPolynomials.polynomial
            (roots step (var 0) (var 1) (var 2) (var 3) (var 1)) (var 1)) (var 4)) ≐
        residualSum (roots step (var 0) (var 1) (var 2) (var 3) (var 1))
          (residuals step (var 0) (var 1) (var 2) (var 3)) (var 1) (var 4)) :=
  closeUniv 5 (.impI (.impI (telescoping_evaluation step _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianDeflationTelescoping

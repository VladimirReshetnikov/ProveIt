import IPRADerivations.Analysis.Polynomials.Representation.GaussianRationalPolynomialBuffers
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianRationalRoundedPower

/-!
# The geometric polynomial for cyclic root reconstruction

The monic coefficient list of length `m` consists of literal ones.
Its Horner value at one is `m`, and multiplying its value by `z-1`
gives the actual rational power `z^m-1`.
-/

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianCyclicGeometricPolynomial

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (zeroCode oneCode scale)
open GaussianRationalHorner (horner hornerF horner_zero horner_succ horner_canonical evaluate qzero qadd qmul
  canonical_unique ofGaussian_canonical qadd_canonical represents_congr qadd_represents)
open GaussianRationalMetric (qsub qnegative)
open GaussianRationalReciprocal (qone power power_zero power_succ power_canonical)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalNaturalScale (naturalPoint natural_point_represents)
open GaussianRationalPolynomialBuffers (distribute_right)
open GaussianRationalSumAlgebra (qadd_associative)
open GaussianRationalSyntheticDivision (qadd_congr qsub_congr qmul_congr qmul_zero_left
  qzero_add qone_canonical qzero_canonical)
open GaussianReciprocalHorner (qmul_one_right qadd_commutative qadd_zero_right qsub_add_cancel)
open GaussianRootAlgebra (equal_of_values re_scale im_scale re_one im_one re_zero im_zero re_add im_add)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_decode sequence_length)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def coefficients (m : PTm n) : PTm n := sequence (qone : PTm 2) m zero

@[simp] theorem subst_coefficients {L : ℕ} (σ : Fin n → PTm L) (m : PTm n) :
    Syn.subst σ (coefficients m) = coefficients (Syn.subst σ m) := by simp [coefficients]

theorem coefficients_length (m : PTm n) : Γ ⊢[PRAAx] length (coefficients m) ≐ m :=
  sequence_length _ _ _

theorem coefficient_at (m j : PTm n) (hj : Γ ⊢[PRAAx] lt j m) :
    Γ ⊢[PRAAx] entry (coefficients m) j ≐ qone := by
  simpa [coefficients,LeanProofs.IPRA.inst2] using sequence_decode (qone : PTm 2) hj (x := (zero : PTm n))

theorem coefficients_monic (m : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] entry (coefficients m) zero ≐ qone :=
  coefficient_at m zero hm

private theorem prefix_succ (m z j : PTm n) (hj : Γ ⊢[PRAAx] lt j m) :
    Γ ⊢[PRAAx] horner (coefficients m) z (succ j) ≐ qadd (qmul (horner (coefficients m) z j) z) qone :=
  (horner_succ _ _ _).eqTrans (qadd_congr (.eqRefl _) (coefficient_at _ _ hj))

private theorem evaluate_at_length (m z : PTm n) :
    Γ ⊢[PRAAx] evaluate (coefficients m) z ≐ horner (coefficients m) z m :=
  congrAp3 hornerF (coefficients_length m) (.eqRefl _) (.eqRefl _)

private def prefixLaw (m z j : PTm n) : Fm PTm n :=
  le j m ⟶ qadd (qmul (horner (coefficients m) z j) z) qone ≐
    qadd (power z j) (horner (coefficients m) z j)

@[simp] private theorem subst_prefixLaw {L : ℕ} (σ : Fin n → PTm L) (m z j : PTm n) :
    (prefixLaw m z j).subst σ = prefixLaw (Syn.subst σ m) (Syn.subst σ z) (Syn.subst σ j) := by
  simp [prefixLaw]

private theorem prefix_law_zero (m z : PTm n) : Γ ⊢[PRAAx] prefixLaw m z zero := by
  let a := horner (coefficients m) z zero
  have ha : Γ ⊢[PRAAx] a ≐ qzero := horner_zero _ _
  have left : Γ ⊢[PRAAx] qadd (qmul a z) qone ≐ qone :=
    (qadd_congr ((qmul_congr ha (.eqRefl _)).eqTrans (qmul_zero_left _)) (.eqRefl _)).eqTrans
      (qzero_add qone qone_canonical)
  have right : Γ ⊢[PRAAx] qadd (power z zero) a ≐ qone :=
    (qadd_congr (power_zero z) ha).eqTrans (qadd_zero_right qone qone_canonical)
  exact .impI (left.eqTrans right.eqSymm).wk

private theorem prefix_law_step (m z j : PTm n) (ih : Γ ⊢[PRAAx] prefixLaw m z j) :
    Γ ⊢[PRAAx] prefixLaw m z (succ j) := by
  let Δ := le (succ j) m :: Γ
  let S := horner (coefficients m) z j
  let T := horner (coefficients m) z (succ j)
  let P := power z j
  have hj : Δ ⊢[PRAAx] lt j m := Prf.hyp0
  have step : Δ ⊢[PRAAx] T ≐ qadd (qmul S z) qone := prefix_succ m z j hj
  have alt : Δ ⊢[PRAAx] T ≐ qadd P S := step.eqTrans (.impE ih.wk (le_of_lt hj))
  have next : Δ ⊢[PRAAx] qadd (qmul T z) qone ≐ qadd (power z (succ j)) T :=
    (qadd_congr ((qmul_congr alt (.eqRefl _)).eqTrans (distribute_right _ _ _)) (.eqRefl _)).eqTrans
      ((qadd_associative _ _ _).eqTrans (qadd_congr (power_succ z j).eqSymm step.eqSymm))
  exact .impI next

private theorem prefix_identity (m z j : PTm n) (hj : Γ ⊢[PRAAx] le j m) :
    Γ ⊢[PRAAx] qadd (qmul (horner (coefficients m) z j) z) qone ≐
      qadd (power z j) (horner (coefficients m) z j) := by
  have h : Γ ⊢[PRAAx] .all (prefixLaw (Syn.shift m) (Syn.shift z) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,trivial⟩ ?_ ?_
    · simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
        prefix_law_zero (Γ := Γ) m z
    · simpa only [subst_prefixLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
        prefix_law_step (Γ := prefixLaw (Syn.shift m) (Syn.shift z) (var 0) :: Γ.map Fm.shift)
          (Syn.shift m) (Syn.shift z) (var 0) Prf.hyp0
  have rule : Γ ⊢[PRAAx] prefixLaw m z j := by
    simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE j
  exact .impE rule hj

private theorem subtract_exchange (a b c : PTm n) :
    Γ ⊢[PRAAx] qsub (qsub a b) c ≐ qsub (qsub a c) b :=
  (qadd_associative a (qnegative b) (qnegative c)).eqTrans
    ((qadd_congr (.eqRefl _) (qadd_commutative _ _)).eqTrans (qadd_associative _ _ _).eqSymm)

theorem geometric_factorization (m z : PTm n) :
    Γ ⊢[PRAAx] qmul (qsub z qone) (evaluate (coefficients m) z) ≐ qsub (power z m) qone := by
  let S := horner (coefficients m) z m
  let P := power z m
  have hS := evaluate_at_length (Γ := Γ) m z
  have h := prefix_identity (Γ := Γ) m z m (le_refl _)
  have diff : Γ ⊢[PRAAx] qmul (qsub z qone) S ≐ qsub (qmul S z) S :=
    (qmul_commutative _ _).eqTrans
      ((GaussianRationalRoundedPower.multiplication_difference S z qone).eqSymm.eqTrans
        (qsub_congr (.eqRefl _) (qmul_one_right _ (horner_canonical _ _ _))))
  have cancel : Γ ⊢[PRAAx] qsub (qmul S z) S ≐ qsub (qsub (qadd (qmul S z) qone) qone) S :=
    qsub_congr (qsub_add_cancel (qmul S z) qone (GaussianRationalHorner.qmul_canonical _ _)).eqSymm (.eqRefl _)
  exact (qmul_congr (.eqRefl _) hS).eqTrans (diff.eqTrans
    (cancel.eqTrans ((qsub_congr (qsub_congr h (.eqRefl _)) (.eqRefl _)).eqTrans
      ((subtract_exchange _ _ _).eqTrans (qsub_congr (qsub_add_cancel P S (power_canonical z m)) (.eqRefl _))))))

private theorem natural_point_zero : Γ ⊢[PRAAx] naturalPoint (zero : PTm n) ≐ qzero := by
  apply canonical_unique _ _ zeroCode one (ofGaussian_canonical _ _ (le_refl _)) qzero_canonical
    (le_refl _) _ (GaussianRationalHorner.zero_represents one)
  apply represents_congr (.eqRefl _) _ (.eqRefl _) (natural_point_represents _)
  apply equal_of_values <;> simp only [re_scale,im_scale,re_one,im_one,re_zero,im_zero] <;> ipra_simps <;> ring

private theorem natural_point_step (j : PTm n) :
    Γ ⊢[PRAAx] qadd (naturalPoint j) qone ≐ naturalPoint (succ j) := by
  apply canonical_unique _ _ (scale (succ j) oneCode) one (qadd_canonical _ _)
    (ofGaussian_canonical _ _ (le_refl _)) (le_refl _) _ (natural_point_represents _)
  apply represents_congr (.eqRefl _) _ (.eqRefl _)
    (qadd_represents _ _ _ _ _ (le_refl _) (natural_point_represents j)
      (GaussianRationalHorner.ofGaussian_represents oneCode one (le_refl _)))
  apply equal_of_values <;> simp only [re_add,im_add,re_scale,im_scale,re_one,im_one] <;> ipra_simps <;> ring

private def countingLaw (m j : PTm n) : Fm PTm n :=
  le j m ⟶ horner (coefficients m) qone j ≐ naturalPoint j

@[simp] private theorem subst_countingLaw {L : ℕ} (σ : Fin n → PTm L) (m j : PTm n) :
    (countingLaw m j).subst σ = countingLaw (Syn.subst σ m) (Syn.subst σ j) := by simp [countingLaw]

private theorem counting_step (m j : PTm n) (ih : Γ ⊢[PRAAx] countingLaw m j) :
    Γ ⊢[PRAAx] countingLaw m (succ j) := by
  let Δ := le (succ j) m :: Γ
  have hj : Δ ⊢[PRAAx] lt j m := Prf.hyp0
  have h : Δ ⊢[PRAAx] horner (coefficients m) qone j ≐ naturalPoint j := .impE ih.wk (le_of_lt hj)
  exact .impI ((prefix_succ m qone j hj).eqTrans
    ((qadd_congr ((qmul_one_right _ (horner_canonical _ _ _)).eqTrans h) (.eqRefl _)).eqTrans
      (natural_point_step j)))

theorem evaluation_at_one (m : PTm n) :
    Γ ⊢[PRAAx] evaluate (coefficients m) qone ≐ naturalPoint m := by
  have h : Γ ⊢[PRAAx] .all (countingLaw (Syn.shift m) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,trivial⟩ ?_ ?_
    · simp only [subst_countingLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI ((horner_zero _ _).eqTrans natural_point_zero.eqSymm).wk
    · simpa only [subst_countingLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
        counting_step (Γ := countingLaw (Syn.shift m) (var 0) :: Γ.map Fm.shift)
          (Syn.shift m) (var 0) Prf.hyp0
  have rule : Γ ⊢[PRAAx] countingLaw m m := by
    simpa only [subst_countingLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE m
  exact (evaluate_at_length m qone).eqTrans (.impE rule (le_refl _))

theorem actual_cyclic_geometric_polynomial_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      ((qmul (qsub (var 0) qone) (evaluate (coefficients (var 1)) (var 0)) ≐
        qsub (power (var 0) (var 1)) qone) ⋏
      (evaluate (coefficients (var 1)) qone ≐ naturalPoint (var 1))) :=
  closeUniv 2 (.andI (geometric_factorization _ _) (evaluation_at_one _))

end LeanProofs.IPRA.Analysis.GaussianCyclicGeometricPolynomial

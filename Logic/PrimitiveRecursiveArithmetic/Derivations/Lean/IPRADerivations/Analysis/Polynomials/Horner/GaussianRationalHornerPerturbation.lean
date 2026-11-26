import IPRADerivations.Analysis.Polynomials.RootFinding.Deflation.GaussianRationalDeflationError
import IPRADerivations.Analysis.Polynomials.RootFinding.Descent.GaussianMonicResidualRadius
import IPRADerivations.Analysis.Polynomials.Coefficients.GaussianCoefficientNormOrder

/-!
# Uniform original-coefficient perturbation of actual rational Horner programs

The actual Horner prefixes are compared using the original independently
normalized Gaussian-rational coefficients and query. A local affine
subtraction identity is proved from computed operand representations, then
quantifier-free induction derives the exact n R^(n-1) delta bound. No
Horner difference, evaluation identity or cleared coefficient error is an
input. Numerical degrees, counters, radii and fraction data are internal.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalHornerPerturbation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner
  (qzero qadd qmul horner evaluate represents canonical_unique represents_congr represents_rescale
    qadd_represents qmul_represents positive_product)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qsub bounded distanceBounded qsub_represents)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision
  (qadd_congr qmul_congr qsub_congr rescale_to remainingDen remaining_den_positive)
open LeanProofs.IPRA.Analysis.GaussianRationalL1 (rawDen rawGaussian raw_den_positive raw_represents)
open LeanProofs.IPRA.Analysis.GaussianRootAlgebra (equal_of_values re_add im_add re_sub im_sub re_mul im_mul re_scale im_scale)
open LeanProofs.IPRA.Analysis.RationalSupMetric (numeratorOf denominatorOf)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The single exact affine difference law needed by the actual recurrence. -/
theorem affine_difference_from_representations (c d a b z C D A B Z E : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (hc : Γ ⊢[PRAAx] represents c C E)
    (hd : Γ ⊢[PRAAx] represents d D E) (ha : Γ ⊢[PRAAx] represents a A E)
    (hb : Γ ⊢[PRAAx] represents b B E) (hz : Γ ⊢[PRAAx] represents z Z E) : Γ ⊢[PRAAx]
    qsub (qadd (qmul c z) a) (qadd (qmul d z) b) ≐
      qadd (qmul (qsub c d) z) (qsub a b) := by
  have E2 := positive_product E E hE hE
  have a2 := represents_rescale a A E E ha
  have b2 := represents_rescale b B E E hb
  have left := qsub_represents _ _ _ _ _ E2
    (qadd_represents _ _ _ _ _ E2 (qmul_represents _ _ _ _ _ _ hE hE hc hz) a2)
    (qadd_represents _ _ _ _ _ E2 (qmul_represents _ _ _ _ _ _ hE hE hd hz) b2)
  have right := qadd_represents _ _ _ _ _ E2
    (qmul_represents _ _ _ _ _ _ hE hE (qsub_represents _ _ _ _ _ hE hc hd) hz)
    (represents_rescale _ _ E E (qsub_represents _ _ _ _ _ hE ha hb))
  apply canonical_unique _ _ _ _ (GaussianRationalMetric.qsub_canonical _ _)
    (GaussianRationalHorner.qadd_canonical _ _) E2 (hrv := right)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := left)
  apply equal_of_values <;> simp only [re_sub,im_sub,re_add,im_add,re_mul,im_mul,re_scale,im_scale] <;> ring

theorem affine_difference (c d a b z : PTm n) : Γ ⊢[PRAAx]
    qsub (qadd (qmul c z) a) (qadd (qmul d z) b) ≐
      qadd (qmul (qsub c d) z) (qsub a b) := by
  let E := rawDen c*remainingDen d a b z
  have hE : Γ ⊢[PRAAx] le one E := positive_product _ _ (raw_den_positive c) (remaining_den_positive _ _ _ _)
  have hc := rescale_to c (rawGaussian c) (rawDen c) (remainingDen d a b z) E (raw_represents (Γ := Γ) c) (.eqRefl _)
  have hd := rescale_to d (rawGaussian d) (rawDen d) (remainingDen c a b z) E (raw_represents (Γ := Γ) d)
    (by unfold E remainingDen; ipra_ring)
  have ha := rescale_to a (rawGaussian a) (rawDen a) (remainingDen c d b z) E (raw_represents (Γ := Γ) a)
    (by unfold E remainingDen; ipra_ring)
  have hb := rescale_to b (rawGaussian b) (rawDen b) (remainingDen c d a z) E (raw_represents (Γ := Γ) b)
    (by unfold E remainingDen; ipra_ring)
  have hz := rescale_to z (rawGaussian z) (rawDen z) (remainingDen c d a b) E (raw_represents (Γ := Γ) z)
    (by unfold E remainingDen; ipra_ring)
  exact affine_difference_from_representations _ _ _ _ _ _ _ _ _ _ E hE hc hd ha hb hz

/-- This is the actual difference of two runtime Horner prefixes. -/
theorem horner_difference_succ (C D z k : PTm n) : Γ ⊢[PRAAx]
    qsub (horner C z (succ k)) (horner D z (succ k)) ≐
      qadd (qmul (qsub (horner C z k) (horner D z k)) z) (qsub (entry C k) (entry D k)) :=
  (qsub_congr (GaussianRationalHorner.horner_succ _ _ _) (GaussianRationalHorner.horner_succ _ _ _)).eqTrans
    (affine_difference _ _ _ _ _)

def coefficientErrors (C D N A B : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift N) ⟶ distanceBounded (entry (Syn.shift C) (succ (var 0)))
    (entry (Syn.shift D) (succ (var 0))) (Syn.shift A) (Syn.shift B))
def budget (R A k : PTm n) : PTm n := k*pw R (PTm.pred k)*A

@[simp] theorem subst_coefficientErrors {m : ℕ} (σ : Fin n → PTm m) (C D N A B : PTm n) :
    (coefficientErrors C D N A B).subst σ = coefficientErrors (Syn.subst σ C) (Syn.subst σ D)
      (Syn.subst σ N) (Syn.subst σ A) (Syn.subst σ B) := by
  simp only [coefficientErrors,Fm.subst_all,Fm.subst_imp,subst_lt,subst_entry,GaussianRationalMetric.subst_distanceBounded,
    ConciseIPRA.PTm.subst_succ,Syn.subst_var,Syn.up_zero,Syn.up_succ,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_budget {m : ℕ} (σ : Fin n → PTm m) (R A k : PTm n) :
    Syn.subst σ (budget R A k) = budget (Syn.subst σ R) (Syn.subst σ A) (Syn.subst σ k) := by simp [budget]

theorem coefficient_error_at (C D N A B j : PTm n) (h : Γ ⊢[PRAAx] coefficientErrors C D N A B)
    (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx] distanceBounded (entry C (succ j)) (entry D (succ j)) A B := by
  have rule : Γ ⊢[PRAAx] lt j N ⟶ distanceBounded (entry C (succ j)) (entry D (succ j)) A B := by
    simpa only [coefficientErrors,Fm.subst_imp,subst_lt,GaussianRationalMetric.subst_distanceBounded,
      subst_entry,ConciseIPRA.PTm.subst_succ,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE j
  exact .impE rule hj

theorem budget_zero (R A : PTm n) : Γ ⊢[PRAAx] budget R A zero ≐ zero := by unfold budget; ipra_ring

theorem budget_succ (R A k : PTm n) : Γ ⊢[PRAAx] budget R A (succ k) ≐ succ k*pw R k*A :=
  congrMul (congrMul (.eqRefl _) (congrAp2 powF (pred_succ k) (.eqRefl _))) (.eqRefl _)

theorem weighted_power (R k : PTm n) : Γ ⊢[PRAAx] k*pw R (PTm.pred k)*R ≐ k*pw R k := by
  refine .orE (zero_or_succ k) ?_ ?_
  · have e := natEq (Prf.hyp0 : ((k ≐ zero) :: Γ) ⊢[PRAAx] k ≐ zero)
    apply deriveNat
    ipra_simps
    rw [e]
    ring
  · have e := natEq (((congrAp2 powF (Prf.hyp0 : ((k ≐ succ (PTm.pred k)) :: Γ) ⊢[PRAAx] k ≐ succ (PTm.pred k))
      (.eqRefl _)).eqTrans (pw_succ R (PTm.pred k))))
    apply deriveNat
    ipra_simps
    rw [e]
    ring

/-- The geometric growth budget retains precisely k R^(k-1) delta,
including the zero prefix and the first lower coefficient. -/
theorem budget_step (R A k : PTm n) (hR : Γ ⊢[PRAAx] le one R) : Γ ⊢[PRAAx]
    le (budget R A k*R+A) (budget R A (succ k)) := by
  have power := GaussianPolynomialPerturbation.power_positive (Γ := Γ) R k hR
  have last : Γ ⊢[PRAAx] le A (pw R k*A) := le_congr (one_mul A) (.eqRefl _)
    (le_mul_mono power (le_refl A))
  have old : Γ ⊢[PRAAx] budget R A k*R+A ≐ k*pw R k*A+A := by
    have e := natEq (weighted_power (Γ := Γ) R k)
    apply deriveNat
    unfold budget
    ipra_simps
    linear_combination Groth.ι (IPRA.Q.mk Γ A)*e
  have next : Γ ⊢[PRAAx] k*pw R k*A+pw R k*A ≐ budget R A (succ k) :=
    (by ipra_ring : Γ ⊢[PRAAx] k*pw R k*A+pw R k*A ≐ succ k*pw R k*A).eqTrans (budget_succ R A k).eqSymm
  exact le_congr old.eqSymm next (add_le_add₂ (le_refl _) last)

/-- The two summands keep their actual common radius denominator. -/
theorem bounded_sum_same_den (u v a b B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hu : Γ ⊢[PRAAx] bounded u a B) (hv : Γ ⊢[PRAAx] bounded v b B) : Γ ⊢[PRAAx]
    bounded (qadd u v) (a+b) B :=
  GaussianMonicResidualRadius.bounded_cancel _ _ _ _ hB hB
    (GaussianRationalReciprocal.bound_congr (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (GaussianRationalReciprocal.bounded_sum _ _ _ _ _ _ hB hB hu hv))

theorem bounded_weaken (u a b B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hab : Γ ⊢[PRAAx] le a b) (hu : Γ ⊢[PRAAx] bounded u a B) : Γ ⊢[PRAAx] bounded u b B := by
  have raw := GaussianRationalMetric.bounded_to_cleared u (rawGaussian u) (rawDen u) a B
    (raw_den_positive u) hB (raw_represents u) hu
  have square := le_mul_mono (le_mul_mono hab hab) (le_refl (rawDen u*rawDen u))
  exact GaussianRationalMetric.bounded_of_cleared u (rawGaussian u) (rawDen u) b B
    (raw_den_positive u) hB (raw_represents u) (le_trans raw square)


def prefixLaw (C D z N R A B k : PTm n) : Fm PTm n := le k N ⟶
  distanceBounded (horner C z (succ k)) (horner D z (succ k)) (budget R A k) B
@[simp] theorem subst_prefixLaw {m : ℕ} (σ : Fin n → PTm m) (C D z N R A B k : PTm n) :
    (prefixLaw C D z N R A B k).subst σ = prefixLaw (Syn.subst σ C) (Syn.subst σ D)
      (Syn.subst σ z) (Syn.subst σ N) (Syn.subst σ R) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ k) := by
  simp only [prefixLaw,Fm.subst_imp,subst_le,GaussianRationalMetric.subst_distanceBounded,
    GaussianRationalHorner.subst_horner,ConciseIPRA.PTm.subst_succ,subst_budget]

theorem prefix_zero (C D z R A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hLead : Γ ⊢[PRAAx] entry C zero ≐ entry D zero) : Γ ⊢[PRAAx]
    distanceBounded (horner C z (succ zero)) (horner D z (succ zero)) (budget R A zero) B := by
  have same : Γ ⊢[PRAAx] horner C z (succ zero) ≐ horner D z (succ zero) :=
    (GaussianRationalHorner.horner_succ _ _ _).eqTrans
      ((qadd_congr (qmul_congr ((GaussianRationalHorner.horner_zero _ _).eqTrans
        (GaussianRationalHorner.horner_zero _ _).eqSymm) (.eqRefl _)) hLead).eqTrans
          (GaussianRationalHorner.horner_succ _ _ _).eqSymm)
  have zeroDiff := (qsub_congr same (.eqRefl _)).eqTrans (GaussianCoefficientNormOrder.qsub_self _)
  exact GaussianRationalReciprocal.bound_congr zeroDiff.eqSymm (budget_zero R A).eqSymm (.eqRefl _)
    (GaussianMonicResidualRadius.zero_bounded zero B hB)

theorem prefix_step (C D z N R A B k : PTm n)
    (hR : Γ ⊢[PRAAx] le one R) (hB : Γ ⊢[PRAAx] le one B)
    (hErrors : Γ ⊢[PRAAx] coefficientErrors C D N A B) (hz : Γ ⊢[PRAAx] bounded z R one)
    (hk : Γ ⊢[PRAAx] lt k N)
    (ih : Γ ⊢[PRAAx] distanceBounded (horner C z (succ k)) (horner D z (succ k)) (budget R A k) B) :
    Γ ⊢[PRAAx] distanceBounded (horner C z (succ (succ k))) (horner D z (succ (succ k)))
      (budget R A (succ k)) B := by
  have product := GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ hB (le_refl one) ih hz
  have product' := GaussianRationalReciprocal.bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring : Γ ⊢[PRAAx] B*one ≐ B) product
  have sum := bounded_sum_same_den _ _ _ _ B hB product' (coefficient_error_at C D N A B k hErrors hk)
  have exactStep := GaussianRationalReciprocal.bound_congr (horner_difference_succ C D z (succ k)).eqSymm
    (.eqRefl _) (.eqRefl _) sum
  exact bounded_weaken _ _ _ B hB (budget_step R A k hR) exactStep

/-- QF induction proves the actual runtime prefix bound; the lower
coefficient condition is instantiated at exactly the stage used. -/
theorem prefix_bound (C D z N R A B k : PTm n)
    (hLead : Γ ⊢[PRAAx] entry C zero ≐ entry D zero)
    (hR : Γ ⊢[PRAAx] le one R) (hB : Γ ⊢[PRAAx] le one B)
    (hErrors : Γ ⊢[PRAAx] coefficientErrors C D N A B) (hz : Γ ⊢[PRAAx] bounded z R one)
    (hk : Γ ⊢[PRAAx] le k N) : Γ ⊢[PRAAx]
    distanceBounded (horner C z (succ k)) (horner D z (succ k)) (budget R A k) B := by
  have hLead' : Γ.map Fm.shift ⊢[PRAAx] entry (Syn.shift C) zero ≐ entry (Syn.shift D) zero := by
    simpa only [Fm.shift,Fm.subst_eq,subst_entry,ConciseIPRA.PTm.subst_zero,Syn.shift] using hLead.shift
  have hR' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift R) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,Syn.shift] using hR.shift
  have hB' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,Syn.shift] using hB.shift
  have hErrors' : Γ.map Fm.shift ⊢[PRAAx] coefficientErrors (Syn.shift C) (Syn.shift D) (Syn.shift N) (Syn.shift A) (Syn.shift B) := by
    simpa only [Fm.shift,subst_coefficientErrors,Syn.shift] using hErrors.shift
  have hz' : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift z) (Syn.shift R) one := by
    simpa only [Fm.shift,GaussianRationalMetric.subst_bounded,ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ,Syn.shift] using hz.shift
  have all : Γ ⊢[PRAAx] .all (prefixLaw (Syn.shift C) (Syn.shift D) (Syn.shift z) (Syn.shift N)
      (Syn.shift R) (Syn.shift A) (Syn.shift B) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,le_QF _ _⟩ ?_ ?_
    · simp only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI (prefix_zero C D z R A B hB hLead).wk
    · simp only [subst_prefixLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      let I := prefixLaw (Syn.shift C) (Syn.shift D) (Syn.shift z) (Syn.shift N)
        (Syn.shift R) (Syn.shift A) (Syn.shift B) (var 0)
      exact prefix_step _ _ _ _ _ _ _ _ hR'.wk.wk hB'.wk.wk hErrors'.wk.wk hz'.wk.wk Prf.hyp0
        (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0))
  have rule : Γ ⊢[PRAAx] prefixLaw C D z N R A B k := by
    simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k
  exact .impE rule hk

/-- The exact source n R^(n-1) delta estimate, on the original rational
coefficient lists and actual Horner evaluation. The stronger N=0 case is
also included, where equal leading coefficients give zero difference. -/
theorem evaluation_bound (C D z N R A B : PTm n)
    (hC : Γ ⊢[PRAAx] length C ≐ succ N) (hD : Γ ⊢[PRAAx] length D ≐ succ N)
    (hLead : Γ ⊢[PRAAx] entry C zero ≐ entry D zero)
    (hR : Γ ⊢[PRAAx] le one R) (hB : Γ ⊢[PRAAx] le one B)
    (hErrors : Γ ⊢[PRAAx] coefficientErrors C D N A B) (hz : Γ ⊢[PRAAx] bounded z R one) : Γ ⊢[PRAAx]
    distanceBounded (evaluate C z) (evaluate D z) (N*pw R (PTm.pred N)*A) B := by
  have actual := prefix_bound C D z N R A B N hLead hR hB hErrors hz (le_refl _)
  exact GaussianRationalReciprocal.bound_congr
    (qsub_congr (congrAp3 GaussianRationalHorner.hornerF hC.eqSymm (.eqRefl _) (.eqRefl _))
      (congrAp3 GaussianRationalHorner.hornerF hD.eqSymm (.eqRefl _) (.eqRefl _))) (.eqRefl _) (.eqRefl _) actual


theorem monic_evaluation_bound (C D z N R A B : PTm n)
    (hC : Γ ⊢[PRAAx] length C ≐ succ N) (hD : Γ ⊢[PRAAx] length D ≐ succ N)
    (hmC : Γ ⊢[PRAAx] entry C zero ≐ GaussianRationalSyntheticDivision.qone)
    (hmD : Γ ⊢[PRAAx] entry D zero ≐ GaussianRationalSyntheticDivision.qone)
    (hR : Γ ⊢[PRAAx] le one R) (hB : Γ ⊢[PRAAx] le one B)
    (hErrors : Γ ⊢[PRAAx] coefficientErrors C D N A B) (hz : Γ ⊢[PRAAx] bounded z R one) : Γ ⊢[PRAAx]
    distanceBounded (evaluate C z) (evaluate D z) (N*pw R (PTm.pred N)*A) B :=
  evaluation_bound C D z N R A B hC hD (hmC.eqTrans hmD.eqSymm) hR hB hErrors hz

def difference (C D z : PTm n) : PTm n := qsub (evaluate C z) (evaluate D z)
def differenceF : PR 3 := PTm.toPR (difference (var 0) (var 1) (var 2))
def budgetF : PR 3 := PTm.toPR (budget (var 0) (var 1) (var 2))

@[simp] theorem subst_difference {m : ℕ} (σ : Fin n → PTm m) (C D z : PTm n) :
    Syn.subst σ (difference C D z) = difference (Syn.subst σ C) (Syn.subst σ D) (Syn.subst σ z) := by
  simp only [difference,GaussianRationalMetric.subst_qsub,GaussianRationalHorner.subst_evaluate]

theorem difference_program_at (C D z : PTm n) : Γ ⊢[PRAAx] ap3 differenceF C D z ≐ difference C D z := by
  simpa only [differenceF,ap3,subst_difference,Syn.subst_var,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
      toPR_eq (Γ := Γ) (difference (var 0) (var 1) (var 2) : PTm 3) ![C,D,z]

theorem budget_program_at (R A k : PTm n) : Γ ⊢[PRAAx] ap3 budgetF R A k ≐ budget R A k := by
  simpa only [budgetF,ap3,subst_budget,Syn.subst_var,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
      toPR_eq (Γ := Γ) (budget (var 0) (var 1) (var 2) : PTm 3) ![R,A,k]

theorem program_bound (C D z N R A B : PTm n)
    (hC : Γ ⊢[PRAAx] length C ≐ succ N) (hD : Γ ⊢[PRAAx] length D ≐ succ N)
    (hLead : Γ ⊢[PRAAx] entry C zero ≐ entry D zero)
    (hR : Γ ⊢[PRAAx] le one R) (hB : Γ ⊢[PRAAx] le one B)
    (hErrors : Γ ⊢[PRAAx] coefficientErrors C D N A B) (hz : Γ ⊢[PRAAx] bounded z R one) : Γ ⊢[PRAAx]
    bounded (ap3 differenceF C D z) (ap3 budgetF R A N) B :=
  GaussianRationalReciprocal.bound_congr (difference_program_at C D z).eqSymm
    (budget_program_at R A N).eqSymm (.eqRefl _)
    (evaluation_bound C D z N R A B hC hD hLead hR hB hErrors hz)

theorem affine_horner_difference_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (qsub (qadd (qmul (var 0) (var 4)) (var 2)) (qadd (qmul (var 1) (var 4)) (var 3)) ≐
      qadd (qmul (qsub (var 0) (var 1)) (var 4)) (qsub (var 2) (var 3))) :=
  closeUniv 5 (affine_difference _ _ _ _ _)

theorem rational_horner_perturbation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (length (var 0) ≐ succ (var 3) ⟶ length (var 1) ≐ succ (var 3) ⟶
      entry (var 0) zero ≐ entry (var 1) zero ⟶ le one (var 4) ⟶ le one (var 6) ⟶
      coefficientErrors (var 0) (var 1) (var 3) (var 5) (var 6) ⟶ bounded (var 2) (var 4) one ⟶
      distanceBounded (evaluate (var 0) (var 2)) (evaluate (var 1) (var 2))
        (var 3*pw (var 4) (PTm.pred (var 3))*var 5) (var 6)) := by
  apply closeUniv 7
  refine .impI (.impI (.impI (.impI (.impI (.impI (.impI ?_))))))
  exact evaluation_bound _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk.wk
    Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

theorem rational_horner_prefix_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (entry (var 0) zero ≐ entry (var 1) zero ⟶ le one (var 4) ⟶ le one (var 6) ⟶
      coefficientErrors (var 0) (var 1) (var 3) (var 5) (var 6) ⟶ bounded (var 2) (var 4) one ⟶ le (var 7) (var 3) ⟶
      distanceBounded (horner (var 0) (var 2) (succ (var 7))) (horner (var 1) (var 2) (succ (var 7)))
        (budget (var 4) (var 5) (var 7)) (var 6)) := by
  apply closeUniv 8
  refine .impI (.impI (.impI (.impI (.impI (.impI ?_)))))
  exact prefix_bound _ _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk
    Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

theorem rational_horner_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (length (var 0) ≐ succ (var 3) ⟶ length (var 1) ≐ succ (var 3) ⟶
      entry (var 0) zero ≐ entry (var 1) zero ⟶ le one (var 4) ⟶ le one (var 6) ⟶
      coefficientErrors (var 0) (var 1) (var 3) (var 5) (var 6) ⟶ bounded (var 2) (var 4) one ⟶
      bounded (ap3 differenceF (var 0) (var 1) (var 2)) (ap3 budgetF (var 4) (var 5) (var 3)) (var 6)) := by
  apply closeUniv 7
  refine .impI (.impI (.impI (.impI (.impI (.impI (.impI ?_))))))
  exact program_bound _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk.wk
    Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

end LeanProofs.IPRA.Analysis.GaussianRationalHornerPerturbation

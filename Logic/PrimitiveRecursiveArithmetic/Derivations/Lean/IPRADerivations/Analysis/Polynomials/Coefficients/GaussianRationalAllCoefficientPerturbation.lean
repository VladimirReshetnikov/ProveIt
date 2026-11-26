import IPRADerivations.Analysis.Polynomials.Horner.GaussianRationalHornerPerturbation

/-!
# Perturbation of every coefficient of the actual rational Horner program

The leading coefficient is allowed to change. Genuine quantifier-free
induction starts at the empty Horner prefix and uses the original error
bound for precisely the next coefficient, including index zero. The
resulting degree-N bound is (N+1) R^N p/q. All coefficients, denominators,
prefix lengths, degrees and radii are numerical inputs. No monicity,
equal-head, canonical-storage or evaluator invariant is assumed.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalAllCoefficientPerturbation

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero horner evaluate)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (bounded distanceBounded)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qsub_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalHornerPerturbation
  (budget subst_budget budget_zero budget_succ budget_step bounded_sum_same_den bounded_weaken horner_difference_succ)
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal (bound_congr)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The original inclusive coefficient range includes the leading term. -/
def coefficientErrors (C D N p q : PTm n) : Fm PTm n := .all
  (le (var 0) (Syn.shift N) ⟶ distanceBounded (entry (Syn.shift C) (var 0))
    (entry (Syn.shift D) (var 0)) (Syn.shift p) (Syn.shift q))

ipra_subst coefficientErrors [Fm.subst_all, Fm.subst_imp, subst_le, subst_entry,
    GaussianRationalMetric.subst_distanceBounded, Syn.subst_var, Syn.up_zero, Syn.up_succ, Syn.subst_shift,
    Syn.shift_subst]

theorem coefficient_error_at (C D N p q i : PTm n) (h : Γ ⊢[PRAAx] coefficientErrors C D N p q)
    (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx] distanceBounded (entry C i) (entry D i) p q := by
  have rule : Γ ⊢[PRAAx] le i N ⟶ distanceBounded (entry C i) (entry D i) p q := by
    simpa only [coefficientErrors,Fm.subst_imp,subst_le,GaussianRationalMetric.subst_distanceBounded,
      subst_entry,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE i
  exact .impE rule hi

def prefixLaw (C D z N R p q k : PTm n) : Fm PTm n := le k (succ N) ⟶
  distanceBounded (horner C z k) (horner D z k) (budget R p k) q

ipra_subst prefixLaw

theorem prefix_zero (C D z R p q : PTm n) (hq : Γ ⊢[PRAAx] le one q) : Γ ⊢[PRAAx]
    distanceBounded (horner C z zero) (horner D z zero) (budget R p zero) q := by
  have diff : Γ ⊢[PRAAx] GaussianRationalMetric.qsub (horner C z zero) (horner D z zero) ≐ qzero :=
    (qsub_congr (GaussianRationalHorner.horner_zero C z) (GaussianRationalHorner.horner_zero D z)).eqTrans
    (GaussianCoefficientNormOrder.qsub_self qzero)
  exact bound_congr diff.eqSymm (budget_zero R p).eqSymm (.eqRefl _)
    (GaussianMonicResidualRadius.zero_bounded zero q hq)

theorem prefix_step (C D z N R p q k : PTm n)
    (hR : Γ ⊢[PRAAx] le one R) (hq : Γ ⊢[PRAAx] le one q)
    (hErrors : Γ ⊢[PRAAx] coefficientErrors C D N p q) (hz : Γ ⊢[PRAAx] bounded z R one)
    (hk : Γ ⊢[PRAAx] le k N)
    (ih : Γ ⊢[PRAAx] distanceBounded (horner C z k) (horner D z k) (budget R p k) q) : Γ ⊢[PRAAx]
    distanceBounded (horner C z (succ k)) (horner D z (succ k)) (budget R p (succ k)) q := by
  have product := GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ hq (le_refl one) ih hz
  have product' := bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring : Γ ⊢[PRAAx] q*one ≐ q) product
  have sum := bounded_sum_same_den _ _ _ _ q hq product' (coefficient_error_at C D N p q k hErrors hk)
  have actual := bound_congr (horner_difference_succ C D z k).eqSymm (.eqRefl _) (.eqRefl _) sum
  exact bounded_weaken _ _ _ q hq (budget_step R p k hR) actual

/-- The only induction is on a QF guarded comparison of actual prefixes. -/
theorem prefix_bound (C D z N R p q k : PTm n)
    (hR : Γ ⊢[PRAAx] le one R) (hq : Γ ⊢[PRAAx] le one q)
    (hErrors : Γ ⊢[PRAAx] coefficientErrors C D N p q) (hz : Γ ⊢[PRAAx] bounded z R one)
    (hk : Γ ⊢[PRAAx] le k (succ N)) : Γ ⊢[PRAAx]
    distanceBounded (horner C z k) (horner D z k) (budget R p k) q := by
  have hR' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift R) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,Syn.shift] using hR.shift
  have hq' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift q) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,Syn.shift] using hq.shift
  have errors' : Γ.map Fm.shift ⊢[PRAAx]
      coefficientErrors (Syn.shift C) (Syn.shift D) (Syn.shift N) (Syn.shift p) (Syn.shift q) := by
    simpa only [Fm.shift,subst_coefficientErrors,Syn.shift] using hErrors.shift
  have hz' : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift z) (Syn.shift R) one := by
    simpa only [Fm.shift,GaussianRationalMetric.subst_bounded,ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ,Syn.shift] using hz.shift
  have all : Γ ⊢[PRAAx] .all (prefixLaw (Syn.shift C) (Syn.shift D) (Syn.shift z) (Syn.shift N)
      (Syn.shift R) (Syn.shift p) (Syn.shift q) (var 0)) := by
    ipra_qfind (⟨le_QF _ _,le_QF _ _⟩) [subst_prefixLaw]
    · exact .impI (prefix_zero C D z R p q hq).wk
    · refine .impI ?_
      have range : le (succ (var 0)) (succ (Syn.shift N)) ::
          prefixLaw (Syn.shift C) (Syn.shift D) (Syn.shift z) (Syn.shift N)
            (Syn.shift R) (Syn.shift p) (Syn.shift q) (var 0) :: Γ.map Fm.shift ⊢[PRAAx]
          le (var 0) (Syn.shift N) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
      exact prefix_step _ _ _ _ _ _ _ _ hR'.wk.wk hq'.wk.wk errors'.wk.wk hz'.wk.wk range
        (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0))
  have rule : Γ ⊢[PRAAx] prefixLaw C D z N R p q k := by
    simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k
  exact .impE rule hk

/-- Every original coefficient, including the leading one, may differ. -/
theorem evaluation_bound (C D z N R p q : PTm n)
    (hC : Γ ⊢[PRAAx] length C ≐ succ N) (hD : Γ ⊢[PRAAx] length D ≐ succ N)
    (hR : Γ ⊢[PRAAx] le one R) (hq : Γ ⊢[PRAAx] le one q)
    (hErrors : Γ ⊢[PRAAx] coefficientErrors C D N p q) (hz : Γ ⊢[PRAAx] bounded z R one) : Γ ⊢[PRAAx]
    distanceBounded (evaluate C z) (evaluate D z) (succ N*pw R N*p) q := by
  have actual := prefix_bound C D z N R p q (succ N) hR hq hErrors hz (le_refl _)
  exact bound_congr
    (qsub_congr (congrAp3 GaussianRationalHorner.hornerF hC.eqSymm (.eqRefl _) (.eqRefl _))
      (congrAp3 GaussianRationalHorner.hornerF hD.eqSymm (.eqRefl _) (.eqRefl _)))
    (budget_succ R p N) (.eqRefl _) actual

def difference (C D z : PTm n) : PTm n := GaussianRationalMetric.qsub (evaluate C z) (evaluate D z)
def differenceF : PR 3 := GaussianRationalHornerPerturbation.differenceF
def budgetF : PR 3 := GaussianRationalHornerPerturbation.budgetF

ipra_subst difference
theorem difference_program_at (C D z : PTm n) : Γ ⊢[PRAAx] ap3 differenceF C D z ≐ difference C D z :=
  GaussianRationalHornerPerturbation.difference_program_at C D z
theorem budget_program_at (R p k : PTm n) : Γ ⊢[PRAAx] ap3 budgetF R p k ≐ budget R p k :=
  GaussianRationalHornerPerturbation.budget_program_at R p k

theorem program_bound (C D z N R p q : PTm n)
    (hC : Γ ⊢[PRAAx] length C ≐ succ N) (hD : Γ ⊢[PRAAx] length D ≐ succ N)
    (hR : Γ ⊢[PRAAx] le one R) (hq : Γ ⊢[PRAAx] le one q)
    (hErrors : Γ ⊢[PRAAx] coefficientErrors C D N p q) (hz : Γ ⊢[PRAAx] bounded z R one) : Γ ⊢[PRAAx]
    bounded (ap3 differenceF C D z) (ap3 budgetF R p (succ N)) q :=
  bound_congr (difference_program_at C D z).eqSymm (budget_program_at R p (succ N)).eqSymm (.eqRefl _)
    (bound_congr (.eqRefl _) (budget_succ R p N).eqSymm (.eqRefl _)
      (evaluation_bound C D z N R p q hC hD hR hq hErrors hz))

theorem all_coefficient_evaluation_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (length (var 0) ≐ succ (var 3) ⟶ length (var 1) ≐ succ (var 3) ⟶
      le one (var 4) ⟶ le one (var 6) ⟶ coefficientErrors (var 0) (var 1) (var 3) (var 5) (var 6) ⟶
      bounded (var 2) (var 4) one ⟶ distanceBounded (evaluate (var 0) (var 2)) (evaluate (var 1) (var 2))
        (succ (var 3)*pw (var 4) (var 3)*var 5) (var 6)) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (.impI (.impI
    (evaluation_bound _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk
      Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))))

theorem all_coefficient_prefix_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (le one (var 4) ⟶ le one (var 6) ⟶ coefficientErrors (var 0) (var 1) (var 3) (var 5) (var 6) ⟶
      bounded (var 2) (var 4) one ⟶ le (var 7) (succ (var 3)) ⟶
      distanceBounded (horner (var 0) (var 2) (var 7)) (horner (var 1) (var 2) (var 7))
        (budget (var 4) (var 5) (var 7)) (var 6)) :=
  closeUniv 8 (.impI (.impI (.impI (.impI (.impI
    (prefix_bound _ _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))))

theorem all_coefficient_program_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (length (var 0) ≐ succ (var 3) ⟶ length (var 1) ≐ succ (var 3) ⟶
      le one (var 4) ⟶ le one (var 6) ⟶ coefficientErrors (var 0) (var 1) (var 3) (var 5) (var 6) ⟶
      bounded (var 2) (var 4) one ⟶ bounded (ap3 differenceF (var 0) (var 1) (var 2))
        (ap3 budgetF (var 4) (var 5) (succ (var 3))) (var 6)) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (.impI (.impI
    (program_bound _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk
      Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))))

theorem actual_all_coefficient_programs_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((ap3 differenceF (var 0) (var 1) (var 2) ≐ difference (var 0) (var 1) (var 2)) ⋏
      ap3 budgetF (var 3) (var 4) (var 5) ≐ budget (var 3) (var 4) (var 5)) :=
  closeUniv 6 (.andI (difference_program_at _ _ _) (budget_program_at _ _ _))

end LeanProofs.IPRA.Analysis.GaussianRationalAllCoefficientPerturbation

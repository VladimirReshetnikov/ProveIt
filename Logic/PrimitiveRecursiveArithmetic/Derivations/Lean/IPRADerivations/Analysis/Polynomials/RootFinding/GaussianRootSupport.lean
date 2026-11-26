import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianRootRadius
import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianRootCoefficientCoherence
import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianRootStability

/-!
# Collision-tolerant root-support names

Finite-demand source04, thm:root-support. The fixed PR coefficient-name
schema supplies the original CN condition. The actual finite factorizer
uses the genuine local monic RD contract. All degrees, data and stages are
object-theory numerical inputs. The exact computed source A, R, b and
E(t) produce the actual lists and product coefficients, their common
radius, and both original Euclidean covers at radius 2^(-t-2).

No temporary deflation radius, root separation, assignment of roots,
coefficient-coherence certificate or Hausdorff output is supplied.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRootSupport

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRootRadius (roots product roots_length root_radius A_positive)
open LeanProofs.IPRA.Analysis.GaussianCoefficientNameBounds (A R CN)
open LeanProofs.IPRA.Analysis.GaussianRootSchedule (four toleranceDenominator tolerance_positive)
open LeanProofs.IPRA.Analysis.GaussianFactorParameters (monicRD)
open LeanProofs.IPRA.Analysis.GaussianRationalStability (pointsBounded)
open LeanProofs.IPRA.Analysis.GaussianRationalCover (close)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def coverDenominator (t : PTm n) : PTm n := pw two (t+two)
@[simp] theorem subst_coverDenominator {m : ℕ} (σ : Fin n → PTm m) (t : PTm n) :
    Syn.subst σ (coverDenominator t) = coverDenominator (Syn.subst σ t) := by simp [coverDenominator]

theorem cover_denominator_positive (t : PTm n) : Γ ⊢[PRAAx] le one (coverDenominator t) :=
  GaussianFactorBudget.power_positive _ _ (le_succ_self one)

theorem radius_positive (a : PR 3) (N x : PTm n) : Γ ⊢[PRAAx] le one (R a N x) :=
  le_trans (A_positive a N x) (le_add_right _ two)

theorem all_roots_bounded (step a : PR 3) (N t x : PTm n)
    (hRD : Γ ⊢[PRAAx] monicRD step) (hCN : Γ ⊢[PRAAx] CN a N x)
    (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    pointsBounded (roots step a N t x) (R a N x) one := by
  refine .allI (.impI ?_)
  simp only [Syn.shift,GaussianRootRadius.subst_roots,GaussianCoefficientNameBounds.subst_R,
    ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ]
  have rd : Γ.map Fm.shift ⊢[PRAAx] monicRD step := by
    simpa only [Fm.shift,GaussianFactorParameters.subst_monicRD] using hRD.shift
  have cn : Γ.map Fm.shift ⊢[PRAAx] CN a (Syn.shift N) (Syn.shift x) := by
    simpa only [Fm.shift,GaussianCoefficientNameBounds.subst_CN,Syn.shift] using hCN.shift
  have hn : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift N) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using hN.shift
  let Δ := lt (var 0) (length (roots step a (Syn.shift N) (Syn.shift t) (Syn.shift x))) :: Γ.map Fm.shift
  have index : Δ ⊢[PRAAx] lt (var 0) (Syn.shift N) :=
    lt_congr (.eqRefl (var 0)) (roots_length step a (Syn.shift N) (Syn.shift t) (Syn.shift x))
      (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) (length (roots step a (Syn.shift N) (Syn.shift t) (Syn.shift x))))
  exact root_radius step a (Syn.shift N) (Syn.shift t) (Syn.shift x) (var 0) rd.wk cn.wk hn.wk index

theorem source_stability_budget (N radius t : PTm n) : Γ ⊢[PRAAx]
    GaussianRootStability.sourceBudget N radius four (toleranceDenominator N radius t) one (coverDenominator t) := by
  have onePow := GaussianPolynomialPerturbation.one_power (Γ := Γ) N
  have target : Γ ⊢[PRAAx] toleranceDenominator N radius t ≐ pw one N*toleranceDenominator N radius t :=
    ((congrMul onePow (.eqRefl _)).eqTrans (one_mul _)).eqSymm
  exact le_congr (by unfold GaussianRootSchedule.coefficientConstant coverDenominator; ipra_ring) target
    (GaussianRootSchedule.root_stability_budget N radius t)

theorem stability_input (step a : PR 3) (N t u x : PTm n)
    (hRD : Γ ⊢[PRAAx] monicRD step) (hCN : Γ ⊢[PRAAx] CN a N x)
    (hN : Γ ⊢[PRAAx] le one N) (htu : Γ ⊢[PRAAx] le t u) : Γ ⊢[PRAAx]
    GaussianRootStability.stabilityInput (roots step a N t x) (roots step a N u x) N (R a N x)
      four (toleranceDenominator N (R a N x) t) one (coverDenominator t) := by
  have basic : Γ ⊢[PRAAx] GaussianRootStability.basicInput (roots step a N t x) (roots step a N u x)
      N (R a N x) four (toleranceDenominator N (R a N x) t) one (coverDenominator t) :=
    .andI hN (.andI (radius_positive a N x) (.andI (tolerance_positive _ _ _)
      (.andI (cover_denominator_positive t) (.andI (roots_length _ _ _ _ _)
        (.andI (roots_length _ _ _ _ _) (source_stability_budget N (R a N x) t))))))
  have errors : Γ ⊢[PRAAx] GaussianRootStability.coefficientErrors (roots step a N t x) (roots step a N u x)
      N four (toleranceDenominator N (R a N x) t) :=
    GaussianRootCoefficientCoherence.product_coefficient_errors step a N (R a N x) t u x hRD hCN hN htu
  exact .andI basic (.andI (all_roots_bounded step a N t x hRD hCN hN)
    (.andI (all_roots_bounded step a N u x hRD hCN hN) errors))

/-- The exact source (RS), for the actual uniformly computed root lists. -/
theorem root_support (step a : PR 3) (N t u x : PTm n)
    (hRD : Γ ⊢[PRAAx] monicRD step) (hCN : Γ ⊢[PRAAx] CN a N x)
    (hN : Γ ⊢[PRAAx] le one N) (htu : Γ ⊢[PRAAx] le t u) : Γ ⊢[PRAAx]
    close (roots step a N t x) (roots step a N u x) one (coverDenominator t) :=
  GaussianRootStability.product_stability _ _ _ _ _ _ _ _ (stability_input _ _ _ _ _ _ hRD hCN hN htu)

theorem root_support_checker (step a : PR 3) (N t u x : PTm n)
    (hRD : Γ ⊢[PRAAx] monicRD step) (hCN : Γ ⊢[PRAAx] CN a N x)
    (hN : Γ ⊢[PRAAx] le one N) (htu : Γ ⊢[PRAAx] le t u) : Γ ⊢[PRAAx]
    GaussianRationalCover.check (roots step a N t x) (roots step a N u x) one (coverDenominator t) ≐ one :=
  GaussianRootStability.checker_accepted _ _ _ _ _ _ _ _ (stability_input _ _ _ _ _ _ hRD hCN hN htu)

def rootNameF (step a : PR 3) : PR 3 := PTm.toPR (roots step a (var 0) (var 1) (var 2))
theorem root_name_program (step a : PR 3) (N t x : PTm n) : Γ ⊢[PRAAx]
    ap3 (rootNameF step a) N t x ≐ roots step a N t x := by
  simpa [rootNameF,ap3] using toPR_eq (Γ := Γ) (roots step a (var 0) (var 1) (var 2) : PTm 3) ![N,t,x]

theorem collision_tolerant_root_support_closed (step a : PR 3) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (monicRD step ⟶ CN a (var 0) (var 3) ⟶ le one (var 0) ⟶
      (pointsBounded (roots step a (var 0) (var 1) (var 3)) (R a (var 0) (var 3)) one ⋏
        (le (var 1) (var 2) ⟶ close (roots step a (var 0) (var 1) (var 3))
          (roots step a (var 0) (var 2) (var 3)) one (coverDenominator (var 1))))) :=
  closeUniv 4 (.impI (.impI (.impI (.andI (all_roots_bounded _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0)
    (.impI (root_support _ _ _ _ _ _ (Prf.wk hyp2) hyp2 Prf.hyp1 Prf.hyp0))))))

theorem collision_tolerant_root_checker_closed (step a : PR 3) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (monicRD step ⟶ CN a (var 0) (var 3) ⟶ le one (var 0) ⟶ le (var 1) (var 2) ⟶
      GaussianRationalCover.check (roots step a (var 0) (var 1) (var 3))
        (roots step a (var 0) (var 2) (var 3)) one (coverDenominator (var 1)) ≐ one) :=
  closeUniv 4 (.impI (.impI (.impI (.impI
    (root_support_checker _ _ _ _ _ _ (Prf.wk hyp2) hyp2 Prf.hyp1 Prf.hyp0)))))

theorem root_name_program_closed (step a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((ap3 (rootNameF step a) (var 0) (var 1) (var 2) ≐ roots step a (var 0) (var 1) (var 2)) ⋏
      length (roots step a (var 0) (var 1) (var 2)) ≐ var 0) :=
  closeUniv 3 (.andI (root_name_program _ _ _ _ _) (roots_length _ _ _ _ _))

end LeanProofs.IPRA.Analysis.GaussianRootSupport

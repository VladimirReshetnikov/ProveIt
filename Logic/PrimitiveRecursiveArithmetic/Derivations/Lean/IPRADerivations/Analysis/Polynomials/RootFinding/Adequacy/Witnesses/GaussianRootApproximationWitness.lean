import IPRADerivations.Analysis.Polynomials.RootFinding.Reconstruction.GaussianRootSupport
import IPRADerivations.Analysis.Polynomials.RootFinding.Reconstruction.GaussianRootFiniteEvaluation
import IPRADerivations.Analysis.Polynomials.RootFinding.Adequacy.GaussianRootAdequacySchedule
import IPRADerivations.Analysis.Polynomials.Horner.Perturbation.GaussianRationalHornerLipschitz

/-!
# Actual finite root-to-support witnesses

Source04 adequacy's forward finite construction: the exact PR stage and
point precision make (FE) small enough for actual finite factor search.
The source normalized vanishing equation concerns actual sample Horner
evaluations. The program returns the actual stage, precision, original root
index and literal root-list entry at distance at most 2^(-k-1) from the
chosen rational point sample. All numerical inputs remain internal.

This is the finite production used by adequacy; the completed Euclidean
distance name and its quantified Member equivalence are separate claims.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRootApproximationWitness

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (bounded distanceBounded)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (evaluate positive_product)
open LeanProofs.IPRA.Analysis.GaussianCoefficientNameBounds (A R CN)
open LeanProofs.IPRA.Analysis.GaussianFactorParameters (monicRD)
open LeanProofs.IPRA.Analysis.GaussianRootRadius (roots)
open LeanProofs.IPRA.Analysis.GaussianRootAdequacySchedule (stage sample)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def C (N U : PTm n) : PTm n := GaussianRootSchedule.coefficientConstant N U
def T (a : PR 3) (N U x : PTm n) : PTm n := C N U+GaussianRationalHornerLipschitz.constant N U (A a N x)
def stageIndex (N U k : PTm n) : PTm n := stage (C N U) k
def sampleIndex (a : PR 3) (N U x k : PTm n) : PTm n := sample N (C N U) (T a N U x) k
def query (point : PR 2) (a : PR 3) (N U x k : PTm n) : PTm n := ap2 point (sampleIndex a N U x k) x
def targetDenominator (k : PTm n) : PTm n := pw two (k+one)
def rootList (step a : PR 3) (N U x k : PTm n) : PTm n := roots step a N (stageIndex N U k) x
def selected (step a : PR 3) (point : PR 2) (N U x k : PTm n) : PTm n :=
  GaussianRationalProductWitness.selected (rootList step a N U x k) N (query point a N U x k) one (targetDenominator k)
def selectedPoint (step a : PR 3) (point : PR 2) (N U x k : PTm n) : PTm n :=
  entry (rootList step a N U x k) (selected step a point N U x k)

ipra_subst C
ipra_subst T
ipra_subst stageIndex
ipra_subst sampleIndex
ipra_subst query
ipra_subst targetDenominator
ipra_subst rootList
ipra_subst selected
ipra_subst selectedPoint

def pointBounds (point : PR 2) (U x : PTm n) : Fm PTm n :=
  .all (bounded (ap2 point (var 0) (Syn.shift x)) (Syn.shift U) one)
def normalizedZero (a : PR 3) (point : PR 2) (N U x : PTm n) : Fm PTm n :=
  .all (bounded (evaluate (GaussianRootSamples.sample a (Syn.shift N) (var 0) (Syn.shift x))
    (ap2 point (var 0) (Syn.shift x))) (T a (Syn.shift N) (Syn.shift U) (Syn.shift x)) (pw two (var 0)))

ipra_subst pointBounds [Syn.subst_shift, Syn.shift_subst]
ipra_subst normalizedZero [Syn.subst_shift, Syn.shift_subst]

theorem point_at (point : PR 2) (U x s : PTm n) (h : Γ ⊢[PRAAx] pointBounds point U x) :
    Γ ⊢[PRAAx] bounded (ap2 point s x) U one := by
  simpa [pointBounds] using h.allE s
theorem zero_at (a : PR 3) (point : PR 2) (N U x s : PTm n) (h : Γ ⊢[PRAAx] normalizedZero a point N U x) :
    Γ ⊢[PRAAx] bounded (evaluate (GaussianRootSamples.sample a N s x) (ap2 point s x)) (T a N U x) (pw two s) := by
  simpa [normalizedZero] using h.allE s

theorem target_denominator_positive (k : PTm n) : Γ ⊢[PRAAx] le one (targetDenominator k) :=
  GaussianFactorBudget.power_positive _ _ (le_succ_self one)

theorem product_bound (step a : PR 3) (point : PR 2) (N U x k : PTm n)
    (hRD : Γ ⊢[PRAAx] monicRD step) (hCN : Γ ⊢[PRAAx] CN a N x)
    (hN : Γ ⊢[PRAAx] le one N) (hU : Γ ⊢[PRAAx] le one U)
    (hPoints : Γ ⊢[PRAAx] pointBounds point U x) (hZero : Γ ⊢[PRAAx] normalizedZero a point N U x) : Γ ⊢[PRAAx]
    bounded (GaussianRationalReconstruction.product (rootList step a N U x k) N (query point a N U x k))
      (pw one N) (pw (targetDenominator k) N) := by
  have finite := GaussianRootFiniteEvaluation.finite_evaluation_bound step a N U (stageIndex N U k)
    (sampleIndex a N U x k) x (query point a N U x k) (T a N U x) hRD hCN hN hU
      (point_at point U x (sampleIndex a N U x k) hPoints) (zero_at a point N U x (sampleIndex a N U x k) hZero)
  have denPos := positive_product _ _
    (GaussianRootAdequacySchedule.evaluation_denominator_positive (Γ := Γ) N (R a N x) (C N U) k)
    (GaussianRootAdequacySchedule.sample_denominator_positive N (C N U) (T a N U x) k)
  have targetPos := GaussianPolynomialPerturbation.power_positive (Γ := Γ) _ N (target_denominator_positive k)
  have budget := GaussianRootAdequacySchedule.finite_evaluation_budget N (R a N x) (C N U) (T a N U x) k hN
  have norm := GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ one (pw (targetDenominator k) N) denPos targetPos
    (le_congr (mul_comm _ _) (one_mul _).eqSymm budget) finite
  exact GaussianRationalReciprocal.bound_congr
    (GaussianRootSamples.product_evaluation step a N (R a N x) (stageIndex N U k) x (query point a N U x k))
    (GaussianPolynomialPerturbation.one_power N).eqSymm (.eqRefl _) norm

theorem selected_certificate (step a : PR 3) (point : PR 2) (N U x k : PTm n)
    (hRD : Γ ⊢[PRAAx] monicRD step) (hCN : Γ ⊢[PRAAx] CN a N x)
    (hN : Γ ⊢[PRAAx] le one N) (hU : Γ ⊢[PRAAx] le one U)
    (hPoints : Γ ⊢[PRAAx] pointBounds point U x) (hZero : Γ ⊢[PRAAx] normalizedZero a point N U x) : Γ ⊢[PRAAx]
    lt (selected step a point N U x k) (length (rootList step a N U x k)) ⋏
      distanceBounded (query point a N U x k) (selectedPoint step a point N U x k) one (targetDenominator k) :=
  GaussianRationalProductWitness.product_witness _ _ _ _ _ hN (target_denominator_positive k)
    (le_congr (.eqRefl _) (GaussianRootRadius.roots_length step a N (stageIndex N U k) x).eqSymm (le_refl _))
    (product_bound _ _ _ _ _ _ _ hRD hCN hN hU hPoints hZero)

def output (step a : PR 3) (point : PR 2) (N U x k : PTm n) : PTm n :=
  pairT (stageIndex N U k) (pairT (sampleIndex a N U x k)
    (pairT (selected step a point N U x k) (selectedPoint step a point N U x k)))
def outputF (step a : PR 3) (point : PR 2) : PR 4 := PTm.toPR (output step a point (var 0) (var 1) (var 2) (var 3))
ipra_subst output
theorem output_program (step a : PR 3) (point : PR 2) (N U x k : PTm n) : Γ ⊢[PRAAx]
    PTm.app (outputF step a point) ![N,U,x,k] ≐ output step a point N U x k := by
  simpa [outputF] using toPR_eq (Γ := Γ) (output step a point (var 0) (var 1) (var 2) (var 3) : PTm 4) ![N,U,x,k]

def certificate (step a : PR 3) (point : PR 2) (N x k t s i w : PTm n) : Fm PTm n :=
  le k t ⋏ (le (k+one) s ⋏ (lt i (length (roots step a N t x)) ⋏
    (w ≐ entry (roots step a N t x) i ⋏ distanceBounded (ap2 point s x) w one (targetDenominator k))))
ipra_subst certificate

theorem output_certificate (step a : PR 3) (point : PR 2) (N U x k : PTm n)
    (hRD : Γ ⊢[PRAAx] monicRD step) (hCN : Γ ⊢[PRAAx] CN a N x)
    (hN : Γ ⊢[PRAAx] le one N) (hU : Γ ⊢[PRAAx] le one U)
    (hPoints : Γ ⊢[PRAAx] pointBounds point U x) (hZero : Γ ⊢[PRAAx] normalizedZero a point N U x) : Γ ⊢[PRAAx]
    certificate step a point N x k
      (fstT (PTm.app (outputF step a point) ![N,U,x,k]))
      (fstT (sndT (PTm.app (outputF step a point) ![N,U,x,k])))
      (fstT (sndT (sndT (PTm.app (outputF step a point) ![N,U,x,k]))))
      (sndT (sndT (sndT (PTm.app (outputF step a point) ![N,U,x,k])))) := by
  let run := PTm.app (outputF step a point) ![N,U,x,k]
  have program := output_program (Γ := Γ) step a point N U x k
  have tEq : Γ ⊢[PRAAx] fstT run ≐ stageIndex N U k :=
    program.fstE
  have tailEq := program.sndE
  have sEq : Γ ⊢[PRAAx] fstT (sndT run) ≐ sampleIndex a N U x k :=
    tailEq.fstE
  have pairEq := tailEq.sndE
  have iEq : Γ ⊢[PRAAx] fstT (sndT (sndT run)) ≐ selected step a point N U x k :=
    pairEq.fstE
  have wEq : Γ ⊢[PRAAx] sndT (sndT (sndT run)) ≐ selectedPoint step a point N U x k :=
    pairEq.sndE
  have found := selected_certificate step a point N U x k hRD hCN hN hU hPoints hZero
  have listEq : Γ ⊢[PRAAx] roots step a N (fstT run) x ≐ rootList step a N U x k := by
    ipra_congr (roots step a (var 0) (var 1) (var 2) : PTm 3) with [.eqRefl N, tEq, .eqRefl x] using [rootList]
  have lenEq : Γ ⊢[PRAAx] length (roots step a N (fstT run) x) ≐ length (rootList step a N U x k) :=
    congrFst listEq
  exact .andI (le_congr (.eqRefl _) tEq.eqSymm (GaussianRootAdequacySchedule.stage_ge_index _ _))
    (.andI (le_congr (.eqRefl _) sEq.eqSymm (GaussianRootAdequacySchedule.sample_ge_succ _ _ _ _))
      (.andI (lt_congr iEq.eqSymm lenEq.eqSymm (Prf.andE₁ found))
        (.andI (wEq.eqTrans (entry_congr listEq.eqSymm iEq.eqSymm))
          (GaussianRationalDistanceOrder.distance_congr
            (congrAp2 point sEq (.eqRefl _)).eqSymm wEq.eqSymm (.eqRefl _) (.eqRefl _) (Prf.andE₂ found)))))

theorem finite_root_to_support_closed (step a : PR 3) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (monicRD step ⟶ CN a (var 0) (var 2) ⟶ le one (var 0) ⟶ le one (var 1) ⟶
      pointBounds point (var 1) (var 2) ⟶ normalizedZero a point (var 0) (var 1) (var 2) ⟶
      (le (var 3) (stageIndex (var 0) (var 1) (var 3)) ⋏
        (le (var 3+one) (sampleIndex a (var 0) (var 1) (var 2) (var 3)) ⋏
          (lt (selected step a point (var 0) (var 1) (var 2) (var 3))
            (length (rootList step a (var 0) (var 1) (var 2) (var 3))) ⋏
            distanceBounded (query point a (var 0) (var 1) (var 2) (var 3))
              (selectedPoint step a point (var 0) (var 1) (var 2) (var 3)) one (targetDenominator (var 3)))))) := by
  apply closeUniv 4
  refine .impI (.impI (.impI (.impI (.impI (.impI ?_)))))
  exact .andI (GaussianRootAdequacySchedule.stage_ge_index _ _)
    (.andI (GaussianRootAdequacySchedule.sample_ge_succ _ _ _ _)
      (selected_certificate _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk
        Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))

theorem finite_root_witness_program_closed (step a : PR 3) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (PTm.app (outputF step a point) ![var 0,var 1,var 2,var 3] ≐ output step a point (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (output_program _ _ _ _ _ _ _)

theorem returned_root_witness_closed (step a : PR 3) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (monicRD step ⟶ CN a (var 0) (var 2) ⟶ le one (var 0) ⟶ le one (var 1) ⟶
      pointBounds point (var 1) (var 2) ⟶ normalizedZero a point (var 0) (var 1) (var 2) ⟶
      certificate step a point (var 0) (var 2) (var 3)
        (fstT (PTm.app (outputF step a point) ![var 0,var 1,var 2,var 3]))
        (fstT (sndT (PTm.app (outputF step a point) ![var 0,var 1,var 2,var 3])))
        (fstT (sndT (sndT (PTm.app (outputF step a point) ![var 0,var 1,var 2,var 3]))))
        (sndT (sndT (sndT (PTm.app (outputF step a point) ![var 0,var 1,var 2,var 3]))))) := by
  apply closeUniv 4
  refine .impI (.impI (.impI (.impI (.impI (.impI ?_)))))
  exact output_certificate _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk
    Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

end LeanProofs.IPRA.Analysis.GaussianRootApproximationWitness

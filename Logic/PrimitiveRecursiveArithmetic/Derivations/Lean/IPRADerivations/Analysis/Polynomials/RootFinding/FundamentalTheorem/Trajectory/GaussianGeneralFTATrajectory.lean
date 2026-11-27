import IPRADerivations.Analysis.Polynomials.Evaluation.GaussianGeneralPolynomialSamples

/-!
# Actual varying-precision general FTA trajectory

The fixed coefficient evaluator supplies a fresh actual polynomial at
precision j+L in each numerical iteration. The PR4 recursor starts at the
canonical Gaussian zero and executes the already constructed nonmonic
descent step. Its equations, canonical values, source precision guard and
computed initial residual bound are derived. No trajectory, successful
step, global invariant, convergence or polynomial-value law is assumed.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGeneralFTATrajectory

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero qadd canonical evaluate)
open LeanProofs.IPRA.Analysis.GaussianGeneralCoefficientNames (generalCN referencePrecision)
open LeanProofs.IPRA.Analysis.GaussianGeneralFTAConstants (L K H B)
open LeanProofs.IPRA.Analysis.GaussianGeneralPolynomialSamples (sample sourceInput)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (bounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def precision (a : PR 3) (N h x j : PTm n) : PTm n := j+L a N h x
def polynomial (a : PR 3) (N h x j : PTm n) : PTm n := sample a N (precision a N h x j) x
def stepBody (a : PR 3) : PTm 5 := ap3 GaussianNonmonicRD.step (var 2)
  (polynomial a (var 2) (var 3) (var 4) (var 0)) (var 1)
def trajectoryF (a : PR 3) : PR 4 := recDef (qzero : PTm 3) (stepBody a)
def trajectory (a : PR 3) (N h x j : PTm n) : PTm n := PTm.app (trajectoryF a) ![j,N,h,x]
def delta (a : PR 3) (N h x j : PTm n) : PTm n := GaussianNonmonicRD.delta N
  (polynomial a N h x j) (trajectory a N h x j)

ipra_subst precision
ipra_subst polynomial
ipra_subst trajectory
ipra_subst delta

theorem trajectory_zero (a : PR 3) (N h x : PTm n) : Γ ⊢[PRAAx] trajectory a N h x zero ≐ qzero := by
  have h0 := rec_zero_vecCons (Γ := Γ) (qzero : PTm 3) (stepBody a) ![N,h,x]
  simpa only [trajectory,trajectoryF,GaussianRationalHorner.subst_qzero] using h0

theorem trajectory_succ (a : PR 3) (N h x j : PTm n) : Γ ⊢[PRAAx]
    trajectory a N h x (succ j) ≐ ap3 GaussianNonmonicRD.step N (polynomial a N h x j) (trajectory a N h x j) := by
  have hs := rec_succ_vecCons (Γ := Γ) (qzero : PTm 3) (stepBody a) j ![N,h,x]
  simpa only [trajectory,trajectoryF,stepBody,subst_ap3,subst_polynomial,Syn.subst_var,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] using hs

theorem trajectory_index_congr (a : PR 3) (N h x : PTm n) {j k : PTm n} (hjk : Γ ⊢[PRAAx] j ≐ k) : Γ ⊢[PRAAx]
    trajectory a N h x j ≐ trajectory a N h x k := by
  apply congrApp
  intro i
  fin_cases i
  · exact hjk
  · exact .eqRefl _
  · exact .eqRefl _
  · exact .eqRefl _

theorem trajectory_update (a : PR 3) (N h x j : PTm n) : Γ ⊢[PRAAx]
    trajectory a N h x (succ j) ≐ qadd (trajectory a N h x j) (delta a N h x j) :=
  (trajectory_succ a N h x j).eqTrans (GaussianNonmonicRD.program_at N (polynomial a N h x j) (trajectory a N h x j))

theorem trajectory_advance (a : PR 3) (N h x j : PTm n) : Γ ⊢[PRAAx]
    trajectory a N h x (succ j) ≐ GaussianDescentClock.advance GaussianNonmonicRD.step N
      (polynomial a N h x j) (trajectory a N h x j) :=
  (trajectory_update a N h x j).eqTrans
    (GaussianNonmonicRD.advance_at N (polynomial a N h x j) (trajectory a N h x j)).eqSymm

theorem trajectory_canonical (a : PR 3) (N h x j : PTm n) : Γ ⊢[PRAAx] canonical (trajectory a N h x j) := by
  refine .orE (zero_or_succ j) ?_ ?_
  · exact GaussianRationalHorner.canonical_congr
      ((trajectory_index_congr a N h x Prf.hyp0).eqTrans (trajectory_zero a N h x))
      GaussianRationalSyntheticDivision.qzero_canonical
  · exact GaussianRationalHorner.canonical_congr
      ((trajectory_index_congr a N h x Prf.hyp0).eqTrans
        ((trajectory_succ a N h x (pred j)).eqTrans (GaussianNonmonicRD.program_at N
          (polynomial a N h x (pred j)) (trajectory a N h x (pred j)))))
      (GaussianNonmonicRD.next_canonical _ _ _)

theorem precision_lower (a : PR 3) (N h x j : PTm n) : Γ ⊢[PRAAx] le (referencePrecision h) (precision a N h x j) :=
  le_trans (GaussianGeneralFTAConstants.L_lower a N h x) (le_add_left (L a N h x) j)
theorem precision_zero (a : PR 3) (N h x : PTm n) : Γ ⊢[PRAAx] precision a N h x zero ≐ L a N h x := zero_add _
theorem precision_succ (a : PR 3) (N h x j : PTm n) : Γ ⊢[PRAAx]
    precision a N h x (succ j) ≐ succ (precision a N h x j) := by unfold precision; ipra_ring

theorem polynomial_length (a : PR 3) (N h x j : PTm n) : Γ ⊢[PRAAx]
    Foundations.SequenceComposition.length (polynomial a N h x j) ≐ succ N := GaussianGeneralPolynomialSamples.sample_length _ _ _ _

theorem polynomial_nonconstant (a : PR 3) (N k h x j : PTm n) (hInput : Γ ⊢[PRAAx] sourceInput a N k h x) :
    Γ ⊢[PRAAx] GaussianBalancedRadiusSyntax.nonconstant (polynomial a N h x j) N :=
  GaussianGeneralPolynomialSamples.tail_nonconstant a N k h (precision a N h x j) x hInput (precision_lower a N h x j)

theorem initial_bound (a : PR 3) (N h x : PTm n) (hCN : Γ ⊢[PRAAx] generalCN a N x) : Γ ⊢[PRAAx]
    bounded (evaluate (polynomial a N h x zero) (trajectory a N h x zero)) (B a x) one :=
  GaussianRationalReciprocal.bound_congr
    (GaussianRationalTranslation.evaluate_congr (.eqRefl _) (trajectory_zero a N h x)).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianGeneralPolynomialSamples.sample_initial_bound a N (precision a N h x zero) x hCN)

def J (a : PR 3) (N h x t : PTm n) : PTm n := K N*(t+H a N h x+two)
def alpha (a : PR 3) (N h x t : PTm n) : PTm n := trajectory a N h x (J a N h x t)
def M (a : PR 3) (N h x t : PTm n) : PTm n := J a N h x t+L a N h x
ipra_subst J
ipra_subst alpha
ipra_subst M

theorem J_lower (a : PR 3) (N h x t : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    le (t+two) (J a N h x t) :=
  le_trans (le_of_eq_add (d := H a N h x) (by ipra_ring))
    (le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right (t+H a N h x+two) (GaussianGeneralFTAConstants.K_positive N hN)))
theorem alpha_canonical (a : PR 3) (N h x t : PTm n) : Γ ⊢[PRAAx] canonical (alpha a N h x t) :=
  trajectory_canonical _ _ _ _ _
theorem M_lower (a : PR 3) (N h x t : PTm n) : Γ ⊢[PRAAx] le (referencePrecision h) (M a N h x t) :=
  precision_lower a N h x (J a N h x t)
theorem alpha_polynomial (a : PR 3) (N h x t : PTm n) : Γ ⊢[PRAAx]
    polynomial a N h x (J a N h x t) ≐ sample a N (M a N h x t) x := .eqRefl _

def nameData (N h x : PTm n) : PTm n := pairT N (pairT h x)
def nameBody (a : PR 3) : PTm 2 := alpha a (fstT (var 1)) (fstT (sndT (var 1)))
  (sndT (sndT (var 1))) (var 0)
def nameF (a : PR 3) : PR 2 := PTm.toPR (nameBody a)
ipra_subst nameData

theorem name_body_at (a : PR 3) (N h x t : PTm n) : Γ ⊢[PRAAx]
    inst2 (nameBody a) t (nameData N h x) ≐ alpha a N h x t := by
  have fields := Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (alpha a (var 0) (var 1) (var 2) (var 3) : PTm 4)
    (σ := ![fstT (nameData N h x),fstT (sndT (nameData N h x)),sndT (sndT (nameData N h x)),t])
    (σ' := ![N,h,x,t]) (fun i => by
      fin_cases i
      · exact fst_pair _ _
      · exact (snd_pair _ _).fstE
      · exact (snd_pair _ _).sndE
      · exact .eqRefl _)
  simpa only [nameBody,inst2,subst_alpha,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using fields

theorem name_at (a : PR 3) (N h x t : PTm n) : Γ ⊢[PRAAx]
    ap2 (nameF a) t (nameData N h x) ≐ alpha a N h x t := by
  have program : Γ ⊢[PRAAx] ap2 (nameF a) t (nameData N h x) ≐ inst2 (nameBody a) t (nameData N h x) := by
    simpa [nameF,ap2,inst2] using toPR_eq (Γ := Γ) (nameBody a) ![t,nameData N h x]
  exact program.eqTrans (name_body_at a N h x t)
theorem returned_canonical (a : PR 3) (N h x t : PTm n) : Γ ⊢[PRAAx]
    canonical (ap2 (nameF a) t (nameData N h x)) :=
  GaussianRationalHorner.canonical_congr (name_at a N h x t) (alpha_canonical a N h x t)

theorem actual_trajectory_equations_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((trajectory a (var 0) (var 1) (var 2) zero ≐ qzero) ⋏
      (trajectory a (var 0) (var 1) (var 2) (succ (var 3)) ≐ ap3 GaussianNonmonicRD.step (var 0)
        (polynomial a (var 0) (var 1) (var 2) (var 3)) (trajectory a (var 0) (var 1) (var 2) (var 3)))) :=
  closeUniv 4 (.andI (trajectory_zero _ _ _ _) (trajectory_succ _ _ _ _ _))
theorem actual_trajectory_update_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (trajectory a (var 0) (var 1) (var 2) (succ (var 3)) ≐
      qadd (trajectory a (var 0) (var 1) (var 2) (var 3)) (delta a (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (trajectory_update _ _ _ _ _)
theorem canonical_trajectory_precision_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (canonical (trajectory a (var 0) (var 1) (var 2) (var 3)) ⋏
      le (referencePrecision (var 1)) (precision a (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.andI (trajectory_canonical _ _ _ _ _) (precision_lower _ _ _ _ _))
theorem actual_initial_residual_bound_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (generalCN a (var 0) (var 2) ⟶ bounded
      (evaluate (polynomial a (var 0) (var 1) (var 2) zero) (trajectory a (var 0) (var 1) (var 2) zero))
        (B a (var 2)) one) :=
  closeUniv 3 (.impI (initial_bound _ _ _ _ Prf.hyp0))
theorem actual_polynomial_nonconstant_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (sourceInput a (var 0) (var 1) (var 2) (var 3) ⟶
      GaussianBalancedRadiusSyntax.nonconstant (polynomial a (var 0) (var 2) (var 3) (var 4)) (var 0)) :=
  closeUniv 5 (.impI (polynomial_nonconstant _ _ _ _ _ _ Prf.hyp0))
theorem actual_alpha_query_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((ap2 (nameF a) (var 3) (nameData (var 0) (var 1) (var 2)) ≐ alpha a (var 0) (var 1) (var 2) (var 3)) ⋏
      (polynomial a (var 0) (var 1) (var 2) (J a (var 0) (var 1) (var 2) (var 3)) ≐
        sample a (var 0) (M a (var 0) (var 1) (var 2) (var 3)) (var 2))) :=
  closeUniv 4 (.andI (name_at _ _ _ _ _) (alpha_polynomial _ _ _ _ _))
theorem actual_alpha_canonical_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (canonical (ap2 (nameF a) (var 3) (nameData (var 0) (var 1) (var 2))) ⋏
      le (referencePrecision (var 1)) (M a (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.andI (returned_canonical _ _ _ _ _) (M_lower _ _ _ _ _))

end LeanProofs.IPRA.Analysis.GaussianGeneralFTATrajectory

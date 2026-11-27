import IPRADerivations.Analysis.Polynomials.Evaluation.NamedValues.GaussianGeneralPolynomialSamples
import IPRADerivations.Analysis.Polynomials.RootFinding.FundamentalTheorem.Trajectory.GaussianGeneralFTARates

/-!
# Actual adjacent-sample coefficient drift for the general FTA

All N+1 original coefficient observations obey the given Cauchy-name
condition. Their actual Horner values at any point in the computed disk
differ by at most B Q^j/(8D) between precisions j+L and j+1+L.
The computed L and the exact source rate supply the whole error budget;
no polynomial drift, leading-coefficient agreement or evaluation law is
assumed. Every numerical parameter, including the degree, is internal.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGeneralFTACoefficientDrift

open_ipra
open LeanProofs.IPRA.Analysis.GaussianGeneralFTAConstants
  (B R L QNum QDen)
open LeanProofs.IPRA.Analysis.GaussianGeneralCoefficientNames (generalCN)
open LeanProofs.IPRA.Analysis.GaussianGeneralPolynomialSamples (sample)
open LeanProofs.IPRA.Analysis.GaussianCoefficientNameBounds (unit unit_positive)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (bounded distanceBounded qsub)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (evaluate)
open LeanProofs.IPRA.Analysis.GaussianDescentClockArithmetic (positive_product)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def precision (a : PR 3) (N h x j : PTm n) : PTm n := j+L a N h x
def numerator (a : PR 3) (N x j : PTm n) : PTm n := B a x*pw (QNum N) j
def denominator (N j : PTm n) : PTm n := QDen N*pw (QDen N) j
def degreeCost (a : PR 3) (N h x : PTm n) : PTm n := succ N*pw (R a N h x) N

ipra_subst precision
ipra_subst numerator
ipra_subst denominator
ipra_subst degreeCost

theorem precision_succ (a : PR 3) (N h x j : PTm n) : Γ ⊢[PRAAx]
    precision a N h x (succ j) ≐ succ (precision a N h x j) := by unfold precision; ipra_ring

theorem denominator_positive (N j : PTm n) : Γ ⊢[PRAAx] le one (denominator N j) :=
  positive_product _ _ (GaussianGeneralFTAConstants.QDen_positive N)
    (GaussianPolynomialPerturbation.power_positive _ _ (GaussianGeneralFTAConstants.QDen_positive N))

/-- This cross comparison uses only local natural input bounds. Its final
application obtains every one of them from the actual computed constants. -/
theorem adjacent_cross (B d q S ell j : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hHalf : Γ ⊢[PRAAx] le d (two*q))
    (hPrecision : Γ ⊢[PRAAx] le (two*d*S) (unit ell)) : Γ ⊢[PRAAx]
    le ((S*(unit (j+ell)+unit (succ (j+ell))))*(d*pw d j))
      ((B*pw q j)*(unit (j+ell)*unit (succ (j+ell)))) := by
  have rate : Γ ⊢[PRAAx] le (pw d j) (pw two j*pw q j) :=
    le_congr (.eqRefl _) (AnalyticNumberTheory.LocalFactor.pw_mul_base two q j)
      (pw_le_pw j hHalf)
  have three_four : Γ ⊢[PRAAx] le (two+one) (two*two) :=
    le_congr (by ipra_ring) (by ipra_ring) (le_succ_self (succ two))
  have three_B : Γ ⊢[PRAAx] le (two+one) ((two*two)*B) :=
    le_trans three_four (le_congr (one_mul _) (mul_comm _ _) (mul_le_mul_right (two*two) hB))
  have left : Γ ⊢[PRAAx]
      le ((two+one)*S*d*pw d j) ((two*two)*B*S*d*pw two j*pw q j) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (le_mul_mono three_B (mul_le_mul_right (S*d) rate))
  have right : Γ ⊢[PRAAx]
      le ((two*two)*B*S*d*pw two j*pw q j) (two*B*pw q j*unit (j+ell)) := by
    have raw := mul_le_mul_right (two*B*pw q j*pw two j) hPrecision
    exact le_congr (by ipra_ring) (by
      refine withEq (pw_add two j ell) fun e => ?_
      simp only [unit]
      apply deriveNat; ipra_simps; rw [e]; ring) raw
  have reduced := le_trans left right
  have expanded := mul_le_mul_right (unit (j+ell)) reduced
  exact le_congr
    (by
      refine withEq (pw_succ two (j+ell)) fun e => ?_
      simp only [unit]
      apply deriveNat; ipra_simps; rw [e]; ring)
    (by
      refine withEq (pw_succ two (j+ell)) fun e => ?_
      simp only [unit]
      apply deriveNat; ipra_simps; rw [e]; ring) expanded

theorem computed_precision_budget (a : PR 3) (N h x : PTm n) : Γ ⊢[PRAAx]
    le (two*QDen N*degreeCost a N h x) (unit (L a N h x)) := by
  have shape : Γ ⊢[PRAAx]
      two*QDen N*degreeCost a N h x ≐ GaussianGeneralFTAConstants.precisionCost a N h x := by
    refine withEq (GaussianGeneralFTAConstants.QDen_value N) fun e => ?_
    unfold degreeCost GaussianGeneralFTAConstants.precisionCost
    apply deriveNat; ipra_simps; rw [e]; ring
  exact le_congr shape.eqSymm (.eqRefl _) (GaussianGeneralFTAConstants.L_budget a N h x)

theorem computed_adjacent_cross (a : PR 3) (N h x j : PTm n) : Γ ⊢[PRAAx]
    le ((degreeCost a N h x*(unit (precision a N h x j)+unit (precision a N h x (succ j))))*denominator N j)
      (numerator a N x j*(unit (precision a N h x j)*unit (precision a N h x (succ j)))) := by
  have raw := adjacent_cross (Γ := Γ) (B a x) (QDen N) (QNum N) (degreeCost a N h x) (L a N h x) j
    (GaussianGeneralFTAConstants.B_positive a x)
    (GaussianGeneralFTARates.half_cross _ (GaussianGeneralFTAConstants.QDen_lower N))
    (computed_precision_budget a N h x)
  have e : Γ ⊢[PRAAx] unit (succ (j+L a N h x)) ≐ unit (precision a N h x (succ j)) :=
    congrAp2 powF (precision_succ a N h x j).eqSymm (.eqRefl _)
  exact le_congr (congrMul (congrMul (.eqRefl _) (congrAdd (.eqRefl _) e)) (.eqRefl _))
    (congrMul (.eqRefl _) (congrMul (.eqRefl _) e)) raw

theorem adjacent_evaluation_bound (a : PR 3) (N h x j z : PTm n)
    (hCN : Γ ⊢[PRAAx] generalCN a N x)
    (hz : Γ ⊢[PRAAx] bounded z (R a N h x) one) : Γ ⊢[PRAAx]
    distanceBounded (evaluate (sample a N (precision a N h x j) x) z)
      (evaluate (sample a N (precision a N h x (succ j)) x) z)
      (numerator a N x j) (denominator N j) := by
  have initial := GaussianRationalAllCoefficientPerturbation.evaluation_bound _ _ z N (R a N h x)
    (unit (precision a N h x j)+unit (precision a N h x (succ j)))
    (unit (precision a N h x j)*unit (precision a N h x (succ j)))
    (GaussianGeneralPolynomialSamples.sample_length a N _ x)
    (GaussianGeneralPolynomialSamples.sample_length a N _ x)
    (GaussianGeneralFTAConstants.R_positive a N h x)
    (positive_product _ _ (unit_positive _) (unit_positive _))
    (GaussianGeneralPolynomialSamples.all_coefficient_coherence a N _ _ x hCN) hz
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
    (positive_product _ _ (unit_positive _) (unit_positive _)) (denominator_positive N j)
    (computed_adjacent_cross a N h x j) initial

def difference (a : PR 3) (N h x j z : PTm n) : PTm n :=
  qsub (evaluate (sample a N (precision a N h x j) x) z)
    (evaluate (sample a N (precision a N h x (succ j)) x) z)
def differenceF (a : PR 3) : PR 5 :=
  PTm.toPR (difference a (var 0) (var 1) (var 2) (var 3) (var 4))
def output (a : PR 3) (N h x j z : PTm n) : PTm n :=
  pairT (difference a N h x j z) (pairT (numerator a N x j) (denominator N j))
def outputF (a : PR 3) : PR 5 :=
  PTm.toPR (output a (var 0) (var 1) (var 2) (var 3) (var 4))
def run (a : PR 3) (N h x j z : PTm n) : PTm n := PTm.app (outputF a) ![N,h,x,j,z]

ipra_subst difference
ipra_subst output
ipra_subst run

theorem difference_program_at (a : PR 3) (N h x j z : PTm n) : Γ ⊢[PRAAx]
    PTm.app (differenceF a) ![N,h,x,j,z] ≐ difference a N h x j z := by
  simpa [differenceF] using toPR_eq (Γ := Γ)
    (difference a (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![N,h,x,j,z]

theorem program_at (a : PR 3) (N h x j z : PTm n) : Γ ⊢[PRAAx]
    run a N h x j z ≐ output a N h x j z := by
  simpa [run,outputF] using toPR_eq (Γ := Γ)
    (output a (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![N,h,x,j,z]

theorem returned_difference (a : PR 3) (N h x j z : PTm n) : Γ ⊢[PRAAx]
    fstT (run a N h x j z) ≐ difference a N h x j z :=
  (program_at a N h x j z).fstE
theorem returned_numerator (a : PR 3) (N h x j z : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run a N h x j z)) ≐ numerator a N x j :=
  (program_at a N h x j z).sndE.fstE
theorem returned_denominator (a : PR 3) (N h x j z : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (run a N h x j z)) ≐ denominator N j :=
  (program_at a N h x j z).sndE.sndE

theorem difference_program_bound (a : PR 3) (N h x j z : PTm n)
    (hCN : Γ ⊢[PRAAx] generalCN a N x)
    (hz : Γ ⊢[PRAAx] bounded z (R a N h x) one) : Γ ⊢[PRAAx]
    bounded (PTm.app (differenceF a) ![N,h,x,j,z]) (numerator a N x j) (denominator N j) :=
  GaussianRationalReciprocal.bound_congr (difference_program_at a N h x j z).eqSymm
    (.eqRefl _) (.eqRefl _) (adjacent_evaluation_bound a N h x j z hCN hz)

theorem returned_bound (a : PR 3) (N h x j z : PTm n)
    (hCN : Γ ⊢[PRAAx] generalCN a N x)
    (hz : Γ ⊢[PRAAx] bounded z (R a N h x) one) : Γ ⊢[PRAAx]
    bounded (fstT (run a N h x j z)) (fstT (sndT (run a N h x j z))) (sndT (sndT (run a N h x j z))) :=
  GaussianRationalReciprocal.bound_congr (returned_difference a N h x j z).eqSymm
    (returned_numerator a N h x j z).eqSymm (returned_denominator a N h x j z).eqSymm
    (adjacent_evaluation_bound a N h x j z hCN hz)

theorem local_adjacent_cross_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 0) ⟶ le (var 1) (two*var 2) ⟶ le (two*var 1*var 3) (unit (var 4)) ⟶
      le ((var 3*(unit (var 5+var 4)+unit (succ (var 5+var 4))))*(var 1*pw (var 1) (var 5)))
        ((var 0*pw (var 2) (var 5))*(unit (var 5+var 4)*unit (succ (var 5+var 4))))) :=
  closeUniv 6 (.impI (.impI (.impI (adjacent_cross _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

theorem computed_coefficient_drift_budget_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le ((degreeCost a (var 0) (var 1) (var 2)*
        (unit (precision a (var 0) (var 1) (var 2) (var 3))+unit (precision a (var 0) (var 1) (var 2) (succ (var 3)))))*
        denominator (var 0) (var 3))
      (numerator a (var 0) (var 2) (var 3)*
        (unit (precision a (var 0) (var 1) (var 2) (var 3))*unit (precision a (var 0) (var 1) (var 2) (succ (var 3)))))) :=
  closeUniv 4 (computed_adjacent_cross _ _ _ _ _)

theorem original_adjacent_evaluation_drift_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (generalCN a (var 0) (var 2) ⟶ bounded (var 4) (R a (var 0) (var 1) (var 2)) one ⟶
      distanceBounded
        (evaluate (sample a (var 0) (precision a (var 0) (var 1) (var 2) (var 3)) (var 2)) (var 4))
        (evaluate (sample a (var 0) (precision a (var 0) (var 1) (var 2) (succ (var 3))) (var 2)) (var 4))
        (numerator a (var 0) (var 2) (var 3)) (denominator (var 0) (var 3))) :=
  closeUniv 5 (.impI (.impI (adjacent_evaluation_bound _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_drift_program_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((run a (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output a (var 0) (var 1) (var 2) (var 3) (var 4)) ⋏
      (PTm.app (differenceF a) ![var 0,var 1,var 2,var 3,var 4] ≐ difference a (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.andI (program_at _ _ _ _ _ _) (difference_program_at _ _ _ _ _ _))

theorem actual_drift_program_bound_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (generalCN a (var 0) (var 2) ⟶ bounded (var 4) (R a (var 0) (var 1) (var 2)) one ⟶
      bounded (PTm.app (differenceF a) ![var 0,var 1,var 2,var 3,var 4])
        (numerator a (var 0) (var 2) (var 3)) (denominator (var 0) (var 3))) :=
  closeUniv 5 (.impI (.impI (difference_program_bound _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem returned_drift_bound_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (generalCN a (var 0) (var 2) ⟶ bounded (var 4) (R a (var 0) (var 1) (var 2)) one ⟶
      bounded (fstT (run a (var 0) (var 1) (var 2) (var 3) (var 4)))
        (fstT (sndT (run a (var 0) (var 1) (var 2) (var 3) (var 4))))
        (sndT (sndT (run a (var 0) (var 1) (var 2) (var 3) (var 4))))) :=
  closeUniv 5 (.impI (.impI (returned_bound _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGeneralFTACoefficientDrift

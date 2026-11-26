import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianGammaFiniteCoefficientRecurrence
import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianGammaRecurrenceWeights
import IPRADerivations.Analysis.Gamma.Taylor.GaussianGammaAllDegreeCoefficientStability
import IPRADerivations.Core.CongruenceTactic

/-!
# The exact recurrence on the original fixed Gamma coefficient samples

Original all-degree horizon coherence rewrites EVERY coefficient in the
actual finite recurrence onto the SAME fixedCoefficient(q,R,j). Actual
combined-kernel readers become the literal gamma/reconstructed-zeta
weight program. The genuine resulting finite sum shares one source
precision q and radius R. At R=e+1 every degree guard is discharged;
there is no assumed recurrence or coefficient-name comparison premise.
Named C42 observation errors remain a separate next step.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaFixedCoefficientRecurrence

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qmul)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRationalCoefficientRecursion (priorTerm priorBody)
open GaussianRationalLowCoefficientConvolution (data)
open GaussianRationalNaturalScale (natScale natScale_congr)
open GaussianGammaReciprocalDegreeCells (degree)
open GaussianGammaFiniteCoefficientStability (fixedCoefficient)
open GaussianGammaRecurrenceWeights (weight)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def term (q R e j : PTm n) : PTm n := qmul (fixedCoefficient q R j) (weight q (two*R) (monus e j))
def sumData (q R e : PTm n) : PTm n := pairT q (pairT R e)
def body : PTm 2 := term (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0)
def weightedSum (q R e : PTm n) : PTm n := GaussianRationalFiniteSum.sum body e (sumData q R e)
@[simp] theorem subst_term {l : ℕ} (σ : Fin n → PTm l) (q R e j : PTm n) :
    Syn.subst σ (term q R e j) = term (Syn.subst σ q) (Syn.subst σ R) (Syn.subst σ e) (Syn.subst σ j) := by simp [term]
@[simp] theorem subst_sumData {l : ℕ} (σ : Fin n → PTm l) (q R e : PTm n) :
    Syn.subst σ (sumData q R e) = sumData (Syn.subst σ q) (Syn.subst σ R) (Syn.subst σ e) := by simp [sumData]
@[simp] theorem subst_weightedSum {l : ℕ} (σ : Fin n → PTm l) (q R e : PTm n) :
    Syn.subst σ (weightedSum q R e) = weightedSum (Syn.subst σ q) (Syn.subst σ R) (Syn.subst σ e) := by simp [weightedSum]

theorem term_congr {q p R S e f j k : PTm n} (hq : Γ ⊢[PRAAx] q ≐ p) (hR : Γ ⊢[PRAAx] R ≐ S)
    (he : Γ ⊢[PRAAx] e ≐ f) (hj : Γ ⊢[PRAAx] j ≐ k) : Γ ⊢[PRAAx] term q R e j ≐ term p S f k := by
  ipra_congr (term (var 0) (var 1) (var 2) (var 3) : PTm 4) with [hq, hR, he, hj]

theorem term_at (q R e j : PTm n) : Γ ⊢[PRAAx] inst2 body j (sumData q R e) ≐ term q R e j := by
  have tail := snd_pair (Γ := Γ) q (pairT R e)
  simp only [body,inst2,subst_term,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact term_congr (fst_pair _ _) ((congrFst tail).eqTrans (fst_pair _ _))
    ((congrSnd tail).eqTrans (snd_pair _ _)) (.eqRefl _)

theorem horizon_dominates (e : PTm n) : Γ ⊢[PRAAx] le e (degree e) :=
  le_of_eq_add (d := two) (by unfold degree; ipra_ring)

theorem original_reader_fixed (q R e j : PTm n) (hj : Γ ⊢[PRAAx] le j e) : Γ ⊢[PRAAx]
    GaussianGammaFiniteCoefficientRecurrence.coefficient q (two*R) e e j ≐ fixedCoefficient q R j :=
  GaussianGammaAllDegreeCoefficientStability.original_fixed_horizon q R e e j (le_trans hj (horizon_dominates e)) hj

theorem original_prior_term (q R e j : PTm n) (hj : Γ ⊢[PRAAx] le j e) : Γ ⊢[PRAAx]
    priorTerm (GaussianGammaCombinedEulerKernelPolynomial.polynomial q (two*R) e) (degree e)
      (GaussianGammaFiniteEulerFactorization.whole q (two*R) e e) (GaussianGammaFiniteEulerFactorization.totalDegree (two*R) e e) e j ≐
        term q R e j :=
  qmul_congr (original_reader_fixed q R e j hj)
    (GaussianGammaRecurrenceWeights.original_kernel_reader q (two*R) e (monus e j)
      (le_trans (GaussianRationalMonicReconstruction.monus_le_left _ _) (horizon_dominates e)))

theorem original_prior_sum (q R e : PTm n) : Γ ⊢[PRAAx]
    GaussianGammaFiniteCoefficientRecurrence.recurrenceSum q (two*R) e e e ≐ weightedSum q R e := by
  apply GaussianRationalFiniteSum.sum_congr_bounded
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift e) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] le (var 0) (Syn.shift e) := le_of_lt Prf.hyp0
  have h := (GaussianRationalCoefficientRecursion.prior_at (Γ := Δ)
    (GaussianGammaCombinedEulerKernelPolynomial.polynomial (Syn.shift q) (two*Syn.shift R) (Syn.shift e)) (degree (Syn.shift e))
    (GaussianGammaFiniteEulerFactorization.whole (Syn.shift q) (two*Syn.shift R) (Syn.shift e) (Syn.shift e))
    (GaussianGammaFiniteEulerFactorization.totalDegree (two*Syn.shift R) (Syn.shift e) (Syn.shift e)) (Syn.shift e) (var 0)).eqTrans
      ((original_prior_term _ _ _ _ hi).eqTrans (term_at _ _ _ _).eqSymm)
  simpa only [Δ,Syn.shift,GaussianRationalLowCoefficientConvolution.subst_data,
    GaussianGammaCombinedEulerKernelPolynomial.subst_polynomial,GaussianGammaReciprocalDegreeCells.subst_degree,
    GaussianGammaFiniteEulerFactorization.subst_whole,GaussianGammaFiniteEulerFactorization.subst_totalDegree,
    PTm.subst_mul,two,PTm.subst_succ,PTm.subst_zero,subst_sumData] using h

theorem original_fixed_coefficient_recurrence (q R s : PTm n) (hH : Γ ⊢[PRAAx] le (succ s) (succ (two*R))) : Γ ⊢[PRAAx]
    natScale s (fixedCoefficient q R (succ s)) ≐ weightedSum q R (succ s) :=
  (natScale_congr (.eqRefl _) (original_reader_fixed q R (succ s) (succ s) (le_refl _)).eqSymm).eqTrans
    ((GaussianGammaFiniteCoefficientRecurrence.original_sampled_coefficient_recurrence q (two*R) (succ s) (succ s) s
      (horizon_dominates (succ s)) (le_refl _) hH).eqTrans (original_prior_sum q R (succ s)))

theorem canonical_radius_dominates (e : PTm n) : Γ ⊢[PRAAx] le e (succ (two*succ e)) :=
  le_of_eq_add (d := e+num 3) (by ipra_ring)

theorem original_canonical_radius_recurrence (q s : PTm n) : Γ ⊢[PRAAx]
    natScale s (fixedCoefficient q (succ (succ s)) (succ s)) ≐ weightedSum q (succ (succ s)) (succ s) :=
  original_fixed_coefficient_recurrence q (succ (succ s)) s (canonical_radius_dominates (succ s))

theorem original_Gamma_fixed_coefficient_literal_weighted_recurrence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (succ (var 2)) (succ (two*var 1)) ⟶
      natScale (var 2) (fixedCoefficient (var 0) (var 1) (succ (var 2))) ≐ weightedSum (var 0) (var 1) (succ (var 2))) :=
  closeUniv 3 (.impI (original_fixed_coefficient_recurrence _ _ _ Prf.hyp0))

theorem original_Gamma_canonical_radius_literal_coefficient_recurrence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (natScale (var 1) (fixedCoefficient (var 0) (succ (succ (var 1))) (succ (var 1))) ≐
      weightedSum (var 0) (succ (succ (var 1))) (succ (var 1))) := closeUniv 2 (original_canonical_radius_recurrence _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaFixedCoefficientRecurrence

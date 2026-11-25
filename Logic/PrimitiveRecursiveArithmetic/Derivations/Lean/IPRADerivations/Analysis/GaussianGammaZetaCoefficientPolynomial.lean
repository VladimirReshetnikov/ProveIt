import IPRADerivations.Analysis.GaussianGammaZetaDegreeName
import IPRADerivations.Analysis.GaussianBivariatePowerExpansion
import IPRADerivations.Core.CongruenceTactic
import IPRADerivations.Core.CommonLemmas

/-!
# Actual stored coefficients for the original Gamma zeta-tail polynomial

The stored degree L+2 polynomial has zero constant and linear terms. Its
degree m≥2 coefficient is the original logarithmic sign/m multiplied by
the original C17 reciprocal-power-tail sample at the same precision.
Its actual Horner evaluation is the already verified original zeta-degree
observation. Coefficient sampling does not depend on the evaluation point.
The uniform weighted coefficient norm and infinite coefficient
stabilization for the full Gamma product remain separate obligations.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaCoefficientPolynomial

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qzero qmul evaluate ofGaussian)
open GaussianRationalSyntheticDivision (qmul_congr qadd_congr qzero_add)
open GaussianRationalReciprocal (power)
open GaussianGammaReciprocalDegreeCells (degree)
open GaussianGammaZetaDegreeName (coefficientData coefficientPart coefficientBody)
open RationalGaussianEmbedding (embed)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (pred monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def coefficient (q N e : PTm n) : PTm n := RationalArithmetic.select (Signum.sg (pred e)) qzero
  (qmul (GaussianFiniteLogarithmPolynomial.coefficient (pred e))
    (embed (RationalReciprocalPowerName.tailSample q e N)))
def polynomialData (q N L : PTm n) : PTm n := pairT q (pairT N L)
def rowBody : PTm 2 := coefficient (fstT (var 1)) (fstT (sndT (var 1)))
  (monus (degree (sndT (sndT (var 1)))) (var 0))
def polynomial (q N L : PTm n) : PTm n := sequence rowBody (succ (degree L)) (polynomialData q N L)
@[simp] theorem subst_coefficient {m : ℕ} (σ : Fin n → PTm m) (q N e : PTm n) :
    Syn.subst σ (coefficient q N e) = coefficient (Syn.subst σ q) (Syn.subst σ N) (Syn.subst σ e) := by
  simp [coefficient,Signum.sg]
@[simp] theorem subst_polynomialData {m : ℕ} (σ : Fin n → PTm m) (q N L : PTm n) :
    Syn.subst σ (polynomialData q N L) = polynomialData (Syn.subst σ q) (Syn.subst σ N) (Syn.subst σ L) := by simp [polynomialData]
@[simp] theorem subst_polynomial {m : ℕ} (σ : Fin n → PTm m) (q N L : PTm n) :
    Syn.subst σ (polynomial q N L) = polynomial (Syn.subst σ q) (Syn.subst σ N) (Syn.subst σ L) := by simp [polynomial]

theorem coefficient_congr {q N e q' N' e' : PTm n}
    (hq : Γ ⊢[PRAAx] q ≐ q') (hN : Γ ⊢[PRAAx] N ≐ N') (he : Γ ⊢[PRAAx] e ≐ e') : Γ ⊢[PRAAx]
    coefficient q N e ≐ coefficient q' N' e' := by
  ipra_congr (coefficient (var 0) (var 1) (var 2) : PTm 3) with [hq, hN, he]

alias signum_congr := Common.congrSg
theorem coefficient_zero (q N : PTm n) : Γ ⊢[PRAAx] coefficient q N zero ≐ qzero :=
  RationalArithmetic.select_zero _ _ _ ((signum_congr pred_zero).eqTrans Signum.sg_zero)
theorem coefficient_one (q N : PTm n) : Γ ⊢[PRAAx] coefficient q N one ≐ qzero :=
  RationalArithmetic.select_zero _ _ _ ((signum_congr (pred_succ zero)).eqTrans Signum.sg_zero)
theorem coefficient_high (q N j : PTm n) : Γ ⊢[PRAAx]
    coefficient q N (degree j) ≐ qmul (GaussianFiniteLogarithmPolynomial.coefficient (succ j))
      (embed (RationalReciprocalPowerName.tailSample q (degree j) N)) :=
  (RationalArithmetic.select_one _ _ _ ((signum_congr (pred_succ (succ j))).eqTrans (Signum.sg_succ j))).eqTrans
    (qmul_congr (GaussianFiniteLogarithmPolynomial.coefficient_congr (pred_succ (succ j))) (.eqRefl _))

theorem row_at (q N L i : PTm n) : Γ ⊢[PRAAx]
    inst2 rowBody i (polynomialData q N L) ≐ coefficient q N (monus (degree L) i) := by
  simp only [rowBody,inst2,subst_coefficient,GaussianGammaReciprocalDegreeCells.subst_degree,
    subst_fstT,subst_sndT,PTm.subst_monus,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  have t := snd_pair (Γ := Γ) q (pairT N L)
  exact coefficient_congr (fst_pair _ _) ((congrFst t).eqTrans (fst_pair _ _))
    (congrMonus (congrSucc (congrSucc ((congrSnd t).eqTrans (snd_pair _ _)))) (.eqRefl _))
theorem polynomial_length (q N L : PTm n) : Γ ⊢[PRAAx] length (polynomial q N L) ≐ succ (degree L) :=
  sequence_length _ _ _
theorem polynomial_lookup (q N L i : PTm n) (hi : Γ ⊢[PRAAx] le i (degree L)) : Γ ⊢[PRAAx]
    entry (polynomial q N L) i ≐ coefficient q N (monus (degree L) i) :=
  (sequence_decode rowBody ((succ_monus_succ _ _).eqTrans hi)).eqTrans (row_at q N L i)
theorem polynomial_exponent (q N L e : PTm n) (he : Γ ⊢[PRAAx] le e (degree L)) : Γ ⊢[PRAAx]
    entry (polynomial q N L) (monus (degree L) e) ≐ coefficient q N e :=
  (polynomial_lookup q N L _ (GaussianRationalMonicReconstruction.monus_le_left _ _)).eqTrans
    (coefficient_congr (.eqRefl _) (.eqRefl _) (GaussianRationalMonicReconstruction.complement _ _ he))
theorem polynomial_constant (q N L : PTm n) : Γ ⊢[PRAAx]
    entry (polynomial q N L) (degree L) ≐ qzero :=
  (polynomial_lookup q N L _ (le_refl _)).eqTrans
    ((coefficient_congr (.eqRefl _) (.eqRefl _) (monus_self _)).eqTrans (coefficient_zero q N))
theorem polynomial_linear (q N L : PTm n) : Γ ⊢[PRAAx]
    entry (polynomial q N L) (monus (degree L) one) ≐ qzero :=
  (polynomial_exponent q N L one (le_trans (le_succ_self one) (GaussianGammaZetaDegreeName.degree_positive L))).eqTrans
    (coefficient_one q N)
theorem polynomial_high (q N L j : PTm n) (hj : Γ ⊢[PRAAx] le j L) : Γ ⊢[PRAAx]
    entry (polynomial q N L) (monus (degree L) (degree j)) ≐
      qmul (GaussianFiniteLogarithmPolynomial.coefficient (succ j))
        (embed (RationalReciprocalPowerName.tailSample q (degree j) N)) :=
  (polynomial_exponent q N L (degree j)
    (le_congr (by unfold degree; ipra_ring) (by unfold degree; ipra_ring) (add_le_add_right two hj))).eqTrans
      (coefficient_high q N j)

def summand (q z B N e : PTm n) : PTm n := qmul (coefficient q N e) (power (ofGaussian z B) e)
def allTerm : PTm 2 := summand (fstT (var 1)) (fstT (sndT (var 1)))
  (fstT (sndT (sndT (var 1)))) (sndT (sndT (sndT (var 1)))) (var 0)
@[simp] theorem subst_summand {m : ℕ} (σ : Fin n → PTm m) (q z B N e : PTm n) :
    Syn.subst σ (summand q z B N e) = summand (Syn.subst σ q) (Syn.subst σ z)
      (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ e) := by simp [summand]
theorem summand_congr {q z B N e q' z' B' N' e' : PTm n}
    (hq : Γ ⊢[PRAAx] q ≐ q') (hz : Γ ⊢[PRAAx] z ≐ z') (hB : Γ ⊢[PRAAx] B ≐ B')
    (hN : Γ ⊢[PRAAx] N ≐ N') (he : Γ ⊢[PRAAx] e ≐ e') : Γ ⊢[PRAAx]
    summand q z B N e ≐ summand q' z' B' N' e' := by
  ipra_congr (summand (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) with [hq, hz, hB, hN, he]
theorem all_term_at (q z B N e : PTm n) : Γ ⊢[PRAAx]
    inst2 allTerm e (coefficientData q z B N) ≐ summand q z B N e := by
  simp only [allTerm,inst2,subst_summand,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  have t₁ := snd_pair (Γ := Γ) q (pairT z (pairT B N))
  have t₂ := (congrSnd t₁).eqTrans (snd_pair z (pairT B N))
  exact summand_congr (fst_pair _ _) ((congrFst t₁).eqTrans (fst_pair _ _))
    ((congrFst t₂).eqTrans (fst_pair _ _)) ((congrSnd t₂).eqTrans (snd_pair _ _)) (.eqRefl _)

theorem evaluation_with_zeros (q z B N L : PTm n) : Γ ⊢[PRAAx]
    evaluate (polynomial q N L) (ofGaussian z B) ≐
      GaussianRationalFiniteSum.sum allTerm (succ (degree L)) (coefficientData q z B N) := by
  refine (GaussianBivariatePowerExpansion.evaluate_power_sum _ _ _ (polynomial_length q N L)).eqTrans
    (GaussianRationalFiniteSum.sum_congr_bounded GaussianRationalPowerExpansion.termBody allTerm (succ (degree L))
      (GaussianRationalPowerExpansion.data (polynomial q N L) (degree L) (ofGaussian z B))
      (coefficientData q z B N) (.allI (.impI ?_)))
  let Δ := lt (var 0) (succ (degree (Syn.shift L))) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] le (var 0) (degree (Syn.shift L)) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  have source := (GaussianRationalPowerExpansion.term_body_at (Γ := Δ) (polynomial (Syn.shift q) (Syn.shift N) (Syn.shift L))
    (degree (Syn.shift L)) (ofGaussian (Syn.shift z) (Syn.shift B)) (var 0)).eqTrans
      (qmul_congr (polynomial_exponent (Syn.shift q) (Syn.shift N) (Syn.shift L) (var 0) hi) (.eqRefl _))
  have right := all_term_at (Γ := Δ) (Syn.shift q) (Syn.shift z) (Syn.shift B) (Syn.shift N) (var 0)
  simpa only [Δ,Syn.shift,subst_polynomial,GaussianGammaReciprocalDegreeCells.subst_degree,
    GaussianRationalPowerExpansion.subst_data,GaussianRationalHorner.subst_ofGaussian,
    GaussianGammaZetaDegreeName.subst_coefficientData,ConciseIPRA.PTm.subst_succ] using source.eqTrans right.eqSymm

theorem summand_zero (q z B N : PTm n) : Γ ⊢[PRAAx] summand q z B N zero ≐ qzero :=
  (qmul_congr (coefficient_zero q N) (.eqRefl _)).eqTrans (GaussianRationalSyntheticDivision.qmul_zero_left _)
theorem summand_one (q z B N : PTm n) : Γ ⊢[PRAAx] summand q z B N one ≐ qzero :=
  (qmul_congr (coefficient_one q N) (.eqRefl _)).eqTrans (GaussianRationalSyntheticDivision.qmul_zero_left _)
theorem summand_high (q z B N j : PTm n) : Γ ⊢[PRAAx]
    summand q z B N (degree j) ≐ coefficientPart q z B N j :=
  (qmul_congr (coefficient_high q N j) (.eqRefl _)).eqTrans
    ((GaussianReciprocalHorner.qmul_associative _ _ _).eqTrans
      ((qmul_congr (.eqRefl _) (GaussianRationalPowerAlgebra.qmul_commutative _ _)).eqTrans
        (GaussianReciprocalHorner.qmul_associative _ _ _).eqSymm))

/-- The two zero coefficients are removed by the actual finite-sum
first-term theorem, followed by literal original degree-cell equality. -/
theorem polynomial_evaluation (q z B N L : PTm n) : Γ ⊢[PRAAx]
    evaluate (polynomial q N L) (ofGaussian z B) ≐
      GaussianRationalFiniteSum.sum coefficientBody (succ L) (coefficientData q z B N) := by
  have first := (all_term_at (Γ := Γ) q z B N zero).eqTrans (summand_zero q z B N)
  have second : Γ ⊢[PRAAx] inst2 (shiftBody allTerm) zero (coefficientData q z B N) ≐ qzero := by
    simp only [inst2_shiftBody]
    exact (all_term_at q z B N one).eqTrans (summand_one q z B N)
  have high : Γ ⊢[PRAAx]
      GaussianRationalFiniteSum.sum (shiftBody (shiftBody allTerm)) (succ L) (coefficientData q z B N) ≐
        GaussianRationalFiniteSum.sum coefficientBody (succ L) (coefficientData q z B N) := by
    apply GaussianRationalFiniteSum.sum_congr_bounded
    refine .allI (.impI ?_)
    simp only [inst2_shiftBody]
    have h := (all_term_at (Γ := lt (var 0) (succ (Syn.shift L)) :: Γ.map Fm.shift)
      (Syn.shift q) (Syn.shift z) (Syn.shift B) (Syn.shift N) (degree (var 0))).eqTrans
        ((summand_high _ _ _ _ _).eqTrans (GaussianGammaZetaDegreeName.coefficient_term_at _ _ _ _ _).eqSymm)
    simpa only [Syn.shift,GaussianGammaZetaDegreeName.subst_coefficientData,ConciseIPRA.PTm.subst_succ,degree] using h
  have inner := (GaussianRationalFiniteSum.sum_shift_first (shiftBody allTerm) (succ L) (coefficientData q z B N)).eqTrans
    ((qadd_congr second high).eqTrans (qzero_add _ (GaussianRationalFiniteSum.sum_canonical coefficientBody _ _)))
  have outer := (GaussianRationalFiniteSum.sum_shift_first allTerm (succ (succ L)) (coefficientData q z B N)).eqTrans
    ((qadd_congr first inner).eqTrans (qzero_add _ (GaussianRationalFiniteSum.sum_canonical coefficientBody _ _)))
  exact (evaluation_with_zeros q z B N L).eqTrans outer

/-- The original sampling clock, original reciprocal-power coefficients
and original finite polynomial observation agree as actual codes. -/
theorem original_observation_binding (p z R B N L : PTm n) : Γ ⊢[PRAAx]
    evaluate (polynomial (GaussianGammaZetaDegreeName.clock p R) N L) (ofGaussian z B) ≐
      GaussianGammaZetaDegreeName.observation p z R B N L :=
  polynomial_evaluation _ _ _ _ _

theorem original_sample_binding (p z R B N L : PTm n) : Γ ⊢[PRAAx]
    evaluate (polynomial (GaussianGammaZetaDegreeName.clock p R) N L) (ofGaussian z B) ≐
      GaussianGammaZetaDegreeName.sample p z R B N L :=
  (original_observation_binding _ _ _ _ _ _).eqTrans (GaussianGammaZetaDegreeName.sample_at _ _ _ _ _ _).eqSymm

def polynomialF : PR 3 := PTm.toPR (polynomial (var 0) (var 1) (var 2))
theorem polynomial_program (q N L : PTm n) : Γ ⊢[PRAAx] ap3 polynomialF q N L ≐ polynomial q N L := by
  simpa [polynomialF,ap3] using toPR_eq (Γ := Γ) (polynomial (var 0) (var 1) (var 2) : PTm 3) ![q,N,L]

theorem actual_zeta_tail_polynomial_coefficients_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (var 3) (var 2) ⟶
      entry (polynomial (var 0) (var 1) (var 2)) (monus (degree (var 2)) (degree (var 3))) ≐
        qmul (GaussianFiniteLogarithmPolynomial.coefficient (succ (var 3)))
          (embed (RationalReciprocalPowerName.tailSample (var 0) (degree (var 3)) (var 1)))) :=
  closeUniv 4 (.impI (polynomial_high _ _ _ _ Prf.hyp0))

theorem actual_zeta_tail_polynomial_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (evaluate (polynomial (GaussianGammaZetaDegreeName.clock (var 0) (var 2)) (var 4) (var 5)) (ofGaussian (var 1) (var 3)) ≐
      GaussianGammaZetaDegreeName.sample (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (original_sample_binding _ _ _ _ _ _)

theorem actual_zeta_tail_coefficient_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap3 polynomialF (var 0) (var 1) (var 2) ≐ polynomial (var 0) (var 1) (var 2)) :=
  closeUniv 3 (polynomial_program _ _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaZetaCoefficientPolynomial

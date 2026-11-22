import IPRADerivations.Analysis.GaussianRationalPolynomialExponentialStability
import IPRADerivations.Analysis.GaussianRationalPolynomialProductDegree

/-!
# Actual finite coefficient sums of the literal polynomial exponential

The SAME existing exponential buffer has its low-exponent coefficient
equal to the actual finite sum of the actual power coefficients divided
by factorials. Genuine original padding and coefficient recurrences prove
this identity. Source H_d and true power support then reduce the sum to
powers k<=e, retaining the original numerical power cap K.
No formal exponential/composition or Bell coefficient law is an input.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalPolynomialExponentialCoefficients

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qzero qmul canonical)
open GaussianRationalSyntheticDivision (qone qzero_canonical qadd_congr qmul_congr canonicalCoefficients canonical_coefficient_at)
open GaussianRationalPolynomialPowers (powerPrefix prefix_length prefix_canonical prefix_zero)
open GaussianRationalPolynomialExponential (stage stage_coefficient_succ inverseFactorial inverse_factorial_zero)
open GaussianRationalLowCoefficientConvolution (exponentCoefficient exponent_inside exponent_outside)
open GaussianRationalPolynomialExponentialStability (coefficient exponent_congr)
open GaussianRationalFiniteSum (sum)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def term (C N K e k : PTm n) : PTm n := qmul (inverseFactorial k)
  (exponentCoefficient (powerPrefix C N K k) (k*N) e)
def data (C N K e : PTm n) : PTm n := pairT C (pairT N (pairT K e))
def termBody : PTm 2 := term (fstT (var 1)) (fstT (sndT (var 1)))
  (fstT (sndT (sndT (var 1)))) (sndT (sndT (sndT (var 1)))) (var 0)
def coefficientSum (C N K e j : PTm n) : PTm n := sum termBody (succ j) (data C N K e)
@[simp] theorem subst_term {l : ℕ} (σ : Fin n → PTm l) (C N K e k : PTm n) :
    Syn.subst σ (term C N K e k) = term (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ K) (Syn.subst σ e) (Syn.subst σ k) := by
  simp [term]
@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (C N K e : PTm n) :
    Syn.subst σ (data C N K e) = data (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ K) (Syn.subst σ e) := by simp [data]
@[simp] theorem subst_coefficientSum {l : ℕ} (σ : Fin n → PTm l) (C N K e j : PTm n) :
    Syn.subst σ (coefficientSum C N K e j) = coefficientSum (Syn.subst σ C) (Syn.subst σ N)
      (Syn.subst σ K) (Syn.subst σ e) (Syn.subst σ j) := by simp [coefficientSum]

theorem term_congr {C C' N N' K K' e e' k k' : PTm n} (hC : Γ ⊢[PRAAx] C ≐ C')
    (hN : Γ ⊢[PRAAx] N ≐ N') (hK : Γ ⊢[PRAAx] K ≐ K') (he : Γ ⊢[PRAAx] e ≐ e')
    (hk : Γ ⊢[PRAAx] k ≐ k') : Γ ⊢[PRAAx] term C N K e k ≐ term C' N' K' e' k' := by
  simpa only [subst_term,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (term (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
      (σ := ![C,N,K,e,k]) (σ' := ![C',N',K',e',k'])
      (fun i => by fin_cases i; exact hC; exact hN; exact hK; exact he; exact hk)
theorem term_at (C N K e k : PTm n) : Γ ⊢[PRAAx]
    inst2 termBody k (data C N K e) ≐ term C N K e k := by
  simp only [termBody,inst2,subst_term,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  have h1 := snd_pair (Γ := Γ) C (pairT N (pairT K e))
  have h2 := (congrSnd h1).eqTrans (snd_pair N (pairT K e))
  exact term_congr (fst_pair _ _) ((congrFst h1).eqTrans (fst_pair _ _))
    ((congrFst h2).eqTrans (fst_pair _ _)) ((congrSnd h2).eqTrans (snd_pair _ _)) (.eqRefl _)

theorem exponent_canonical (C N e : PTm n) (hC : Γ ⊢[PRAAx] canonicalCoefficients C)
    (hL : Γ ⊢[PRAAx] length C ≐ succ N) : Γ ⊢[PRAAx] canonical (exponentCoefficient C N e) := by
  refine .orE (lt_or_le N e) ?_ ?_
  · exact GaussianRationalHorner.canonical_congr (exponent_outside C N e Prf.hyp0) qzero_canonical
  · have hi : (le e N :: Γ) ⊢[PRAAx] lt (monus N e) (length C) :=
      lt_congr (.eqRefl _) hL.wk.eqSymm ((succ_monus_succ _ _).eqTrans (GaussianRationalMonicReconstruction.monus_le_left _ _))
    exact GaussianRationalHorner.canonical_congr (exponent_inside C N e Prf.hyp0)
      (canonical_coefficient_at C _ hC.wk hi)

theorem padded_exponent (C N K j e : PTm n) (he : Γ ⊢[PRAAx] le e N) : Γ ⊢[PRAAx]
    GaussianRationalPolynomialBuffers.padCoefficient (stage C N K j) N (monus (succ j*N) e) ≐ coefficient C N K j e := by
  refine .orE (lt_or_le (j*N) e) ?_ ?_
  · have hn : (lt (j*N) e :: Γ) ⊢[PRAAx] le e (j*N+N) := le_trans he.wk (le_add_left _ _)
    have hd := GaussianRationalPolynomialProductDegree.difference_at (j*N) N e Prf.hyp0 hn
    have hlt : (lt (j*N) e :: Γ) ⊢[PRAAx] lt (monus (succ j*N) e) N :=
      lt_congr (congrMonus (by ipra_ring) (.eqRefl e)).eqSymm (.eqRefl N) hd
    exact (GaussianRationalPolynomialBuffers.pad_coefficient_before _ _ _ hlt).eqTrans
      (exponent_outside (stage C N K j) (j*N) e Prf.hyp0).eqSymm
  · exact (GaussianRationalPolynomialExponentialStability.padded_coefficient C N K j e Prf.hyp0).eqTrans
      (exponent_inside (stage C N K j) (j*N) e Prf.hyp0).eqSymm

theorem coefficient_recurrence (C N K j e : PTm n) (he : Γ ⊢[PRAAx] le e N) : Γ ⊢[PRAAx]
    coefficient C N K (succ j) e ≐ GaussianRationalHorner.qadd (coefficient C N K j e) (term C N K e (succ j)) := by
  have hN : Γ ⊢[PRAAx] le N (succ j*N) := le_congr (.eqRefl _) (by ipra_ring) (le_add_right N (j*N))
  have he' := le_trans he hN
  exact (exponent_inside _ _ _ he').eqTrans
    ((stage_coefficient_succ C N K j (monus (succ j*N) e) (GaussianRationalMonicReconstruction.monus_le_left _ _)).eqTrans
      (qadd_congr (padded_exponent C N K j e he)
        (qmul_congr (.eqRefl _) (exponent_inside (powerPrefix C N K (succ j)) (succ j*N) e he').eqSymm)))

theorem coefficient_zero (C N K e : PTm n) : Γ ⊢[PRAAx] coefficient C N K zero e ≐ term C N K e zero := by
  have hg : Γ ⊢[PRAAx] canonical (exponentCoefficient (powerPrefix C N K zero) (zero*N) e) :=
    exponent_canonical _ _ _ (prefix_canonical C N K zero) (prefix_length C N K zero)
  have hs : Γ ⊢[PRAAx] coefficient C N K zero e ≐ exponentCoefficient (powerPrefix C N K zero) (zero*N) e :=
    exponent_congr ((GaussianRationalPolynomialExponential.stage_zero C N K).eqTrans (prefix_zero C N K).eqSymm) (.eqRefl _) (.eqRefl _)
  have ht : Γ ⊢[PRAAx] term C N K e zero ≐ exponentCoefficient (powerPrefix C N K zero) (zero*N) e :=
    (qmul_congr inverse_factorial_zero (.eqRefl _)).eqTrans
      ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans (GaussianReciprocalHorner.qmul_one_right _ hg))
  exact hs.eqTrans ht.eqSymm

theorem sum_zero (C N K e : PTm n) : Γ ⊢[PRAAx] coefficient C N K zero e ≐ coefficientSum C N K e zero := by
  have hs : Γ ⊢[PRAAx] coefficientSum C N K e zero ≐ term C N K e zero :=
    (GaussianRationalFiniteSum.sum_succ termBody zero (data C N K e)).eqTrans
      ((qadd_congr (GaussianRationalFiniteSum.sum_zero termBody (data C N K e)) (term_at C N K e zero)).eqTrans
        (GaussianRationalSyntheticDivision.qzero_add _ (GaussianRationalHorner.qmul_canonical _ _)))
  exact (coefficient_zero C N K e).eqTrans hs.eqSymm

def sumLaw (C N K e j : PTm n) : Fm PTm n := coefficient C N K j e ≐ coefficientSum C N K e j
@[simp] theorem subst_sumLaw {l : ℕ} (σ : Fin n → PTm l) (C N K e j : PTm n) :
    (sumLaw C N K e j).subst σ = sumLaw (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ K)
      (Syn.subst σ e) (Syn.subst σ j) := by simp [sumLaw]

theorem sum_step (C N K e j : PTm n) (he : Γ ⊢[PRAAx] le e N) (ih : Γ ⊢[PRAAx] sumLaw C N K e j) :
    Γ ⊢[PRAAx] sumLaw C N K e (succ j) :=
  (coefficient_recurrence C N K j e he).eqTrans
    ((qadd_congr ih (term_at C N K e (succ j)).eqSymm).eqTrans
      (GaussianRationalFiniteSum.sum_succ termBody (succ j) (data C N K e)).eqSymm)

theorem coefficient_sum (C N K e j : PTm n) (he : Γ ⊢[PRAAx] le e N) : Γ ⊢[PRAAx]
    coefficient C N K j e ≐ coefficientSum C N K e j := by
  have hn : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift e) (Syn.shift N) := by
    simpa only [Fm.shift,subst_le,Syn.shift] using he.shift
  have all : Γ ⊢[PRAAx] .all (sumLaw (Syn.shift C) (Syn.shift N) (Syn.shift K) (Syn.shift e) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_sumLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact sum_zero C N K e
    · simp only [subst_sumLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact sum_step _ _ _ _ _ hn.wk Prf.hyp0
  change Γ ⊢[PRAAx] sumLaw C N K e j
  simpa only [subst_sumLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j

theorem finite_low_expansion (C N K e : PTm n) (hC : Γ ⊢[PRAAx] entry C N ≐ qzero)
    (he : Γ ⊢[PRAAx] le e N) (hK : Γ ⊢[PRAAx] le e K) : Γ ⊢[PRAAx]
    exponentCoefficient (GaussianRationalPolynomialExponential.polynomial C N K) (K*N) e ≐ coefficientSum C N K e e :=
  (GaussianRationalPolynomialExponentialStability.finite_exponential_cutoff C N K e hC he hK).eqTrans
    (coefficient_sum C N K e e he)
theorem logarithm_low_expansion (d K e : PTm n) (he : Γ ⊢[PRAAx] le e d)
    (hK : Γ ⊢[PRAAx] le e K) : Γ ⊢[PRAAx]
    exponentCoefficient (GaussianFiniteLogarithmPolynomial.composition d K) (K*d) e ≐
      coefficientSum (GaussianFiniteLogarithmPolynomial.polynomial d) d K e e :=
  finite_low_expansion _ _ _ _ (GaussianFiniteLogarithmPolynomial.polynomial_constant d) he hK

def sumF : PR 5 := PTm.toPR (coefficientSum (var 0) (var 1) (var 2) (var 3) (var 4))
def output (C N K e : PTm n) : PTm n := pairT
  (exponentCoefficient (GaussianRationalPolynomialExponential.polynomial C N K) (K*N) e) (coefficientSum C N K e e)
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (C N K e : PTm n) : PTm n := PTm.app outputF ![C,N,K,e]
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (C N K e : PTm n) :
    Syn.subst σ (output C N K e) = output (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ K) (Syn.subst σ e) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (C N K e : PTm n) :
    Syn.subst σ (run C N K e) = run (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ K) (Syn.subst σ e) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem sum_program_at (C N K e j : PTm n) : Γ ⊢[PRAAx]
    PTm.app sumF ![C,N,K,e,j] ≐ coefficientSum C N K e j := by
  simpa [sumF] using toPR_eq (Γ := Γ) (coefficientSum (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![C,N,K,e,j]
theorem program_at (C N K e : PTm n) : Γ ⊢[PRAAx] run C N K e ≐ output C N K e := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![C,N,K,e]
theorem returned_coefficient (C N K e : PTm n) : Γ ⊢[PRAAx]
    fstT (run C N K e) ≐ exponentCoefficient (GaussianRationalPolynomialExponential.polynomial C N K) (K*N) e :=
  (congrFst (program_at C N K e)).eqTrans (fst_pair _ _)
theorem returned_sum (C N K e : PTm n) : Γ ⊢[PRAAx] sndT (run C N K e) ≐ coefficientSum C N K e e :=
  (congrSnd (program_at C N K e)).eqTrans (snd_pair _ _)
theorem returned_agreement (C N K e : PTm n) (hC : Γ ⊢[PRAAx] entry C N ≐ qzero)
    (he : Γ ⊢[PRAAx] le e N) (hK : Γ ⊢[PRAAx] le e K) : Γ ⊢[PRAAx]
    fstT (run C N K e) ≐ sndT (run C N K e) :=
  (returned_coefficient C N K e).eqTrans ((finite_low_expansion C N K e hC he hK).eqTrans (returned_sum C N K e).eqSymm)
theorem returned_logarithm_agreement (d K e : PTm n) (he : Γ ⊢[PRAAx] le e d)
    (hK : Γ ⊢[PRAAx] le e K) : Γ ⊢[PRAAx]
    fstT (run (GaussianFiniteLogarithmPolynomial.polynomial d) d K e) ≐
      sndT (run (GaussianFiniteLogarithmPolynomial.polynomial d) d K e) :=
  returned_agreement _ _ _ _ (GaussianFiniteLogarithmPolynomial.polynomial_constant d) he hK

theorem actual_exponential_coefficient_recurrence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (var 4) (var 1) ⟶ coefficient (var 0) (var 1) (var 2) (succ (var 3)) (var 4) ≐
      GaussianRationalHorner.qadd (coefficient (var 0) (var 1) (var 2) (var 3) (var 4))
        (term (var 0) (var 1) (var 2) (var 4) (succ (var 3)))) :=
  closeUniv 5 (.impI (coefficient_recurrence _ _ _ _ _ Prf.hyp0))
theorem literal_actual_coefficient_sum_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (var 3) (var 1) ⟶ coefficient (var 0) (var 1) (var 2) (var 4) (var 3) ≐
      coefficientSum (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (coefficient_sum _ _ _ _ _ Prf.hyp0))
theorem literal_low_exponential_expansion_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (entry (var 0) (var 1) ≐ qzero ⟶ le (var 3) (var 1) ⟶ le (var 3) (var 2) ⟶
      exponentCoefficient (GaussianRationalPolynomialExponential.polynomial (var 0) (var 1) (var 2)) (var 2*var 1) (var 3) ≐
        coefficientSum (var 0) (var 1) (var 2) (var 3) (var 3)) :=
  closeUniv 4 (.impI (.impI (.impI (finite_low_expansion _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))
theorem original_logarithm_coefficient_expansion_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 2) (var 0) ⟶ le (var 2) (var 1) ⟶
      exponentCoefficient (GaussianFiniteLogarithmPolynomial.composition (var 0) (var 1)) (var 1*var 0) (var 2) ≐
        coefficientSum (GaussianFiniteLogarithmPolynomial.polynomial (var 0)) (var 0) (var 1) (var 2) (var 2)) :=
  closeUniv 3 (.impI (.impI (logarithm_low_expansion _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_finite_coefficient_sum_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (PTm.app sumF ![var 0,var 1,var 2,var 3,var 4] ≐ coefficientSum (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (sum_program_at _ _ _ _ _)
theorem actual_coefficient_expansion_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (program_at _ _ _ _)
theorem actual_returned_coefficient_expansion_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (entry (var 0) (var 1) ≐ qzero ⟶ le (var 3) (var 1) ⟶ le (var 3) (var 2) ⟶
      fstT (run (var 0) (var 1) (var 2) (var 3)) ≐ sndT (run (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (.impI (.impI (returned_agreement _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))
theorem original_returned_logarithm_coefficient_expansion_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 2) (var 0) ⟶ le (var 2) (var 1) ⟶
      fstT (run (GaussianFiniteLogarithmPolynomial.polynomial (var 0)) (var 0) (var 1) (var 2)) ≐
        sndT (run (GaussianFiniteLogarithmPolynomial.polynomial (var 0)) (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (returned_logarithm_agreement _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianRationalPolynomialExponentialCoefficients

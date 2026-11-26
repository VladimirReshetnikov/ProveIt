import IPRADerivations.Analysis.Polynomials.GaussianRationalLowCoefficientConvolution
import IPRADerivations.Analysis.Logarithm.GaussianFiniteLogarithmPolynomial
import IPRADerivations.Foundations.BoundedSyntaxInduction

/-!
# Actual low-exponent support of the existing polynomial powers

For an ORIGINAL zero constant coefficient, the SAME constructed j-th
power has zero coefficients at exponents e<j in the required range e<=N.
The existing bounded convolution and a genuine compiled bounded induction
prove this for numerical power caps/indices. No power-support or evaluator
law is supplied. The source H_d specialization derives its zero constant.
Full Bell identification and the analytic C4 tail remain separate.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalPolynomialPowerSupport

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qzero qmul)
open GaussianRationalSyntheticDivision (qmul_congr qmul_zero_left qmul_zero_right)
open GaussianRationalPolynomialPowers (powerPrefix prefix_succ)
open GaussianRationalLowCoefficientConvolution (exponentCoefficient exponent_inside cauchySum term termBody term_at data)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (entry_congr)
open LeanProofs.IPRA.Foundations.BoundedSyntax (BFm formula)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def lowSupport (C N K j : PTm n) : Fm PTm n := .all
  (lt (var 0) (succ (Syn.shift N)) ⟶ lt (var 0) (Syn.shift j) ⟶
    exponentCoefficient (powerPrefix (Syn.shift C) (Syn.shift N) (Syn.shift K) (Syn.shift j))
      (Syn.shift j*Syn.shift N) (var 0) ≐ qzero)
def supportLaw (C N K j : PTm n) : Fm PTm n := le j K ⟶ lowSupport C N K j
def supportSyntax (C N K j : PTm n) : BFm n := .imp (.le j K) (.all (succ N)
  (.imp (.lt (var 0) (Syn.shift j)) (.eq
    (exponentCoefficient (powerPrefix (Syn.shift C) (Syn.shift N) (Syn.shift K) (Syn.shift j))
      (Syn.shift j*Syn.shift N) (var 0)) qzero)))
@[simp] theorem subst_lowSupport {l : ℕ} (σ : Fin n → PTm l) (C N K j : PTm n) :
    (lowSupport C N K j).subst σ = lowSupport (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ K) (Syn.subst σ j) := by
  simp [lowSupport,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_supportLaw {l : ℕ} (σ : Fin n → PTm l) (C N K j : PTm n) :
    (supportLaw C N K j).subst σ = supportLaw (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ K) (Syn.subst σ j) := by
  simp [supportLaw]
theorem support_formula (C N K j : PTm n) : formula (supportSyntax C N K j) = supportLaw C N K j := by
  simp [supportSyntax,supportLaw,lowSupport,formula,BFm.le,BFm.lt,le,lt]

theorem support_at (C N K j e : PTm n) (h : Γ ⊢[PRAAx] lowSupport C N K j)
    (he : Γ ⊢[PRAAx] le e N) (hj : Γ ⊢[PRAAx] lt e j) : Γ ⊢[PRAAx]
    exponentCoefficient (powerPrefix C N K j) (j*N) e ≐ qzero := by
  have gate : Γ ⊢[PRAAx] lt e (succ N) ⟶ lt e j ⟶ exponentCoefficient (powerPrefix C N K j) (j*N) e ≐ qzero := by
    simpa only [lowSupport,Fm.subst_imp,Fm.subst_eq,subst_lt,ConciseIPRA.PTm.subst_succ,
      GaussianRationalLowCoefficientConvolution.subst_exponentCoefficient,GaussianRationalPolynomialPowers.subst_prefix,
      PTm.subst_mul,GaussianRationalHorner.subst_qzero,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE e
  exact .impE (.impE gate ((succ_monus_succ _ _).eqTrans he)) hj

theorem min_product (e j N : PTm n) (hN : Γ ⊢[PRAAx] le e N)
    (hj : Γ ⊢[PRAAx] le e j) : Γ ⊢[PRAAx] le e (j*N) := by
  refine .orE (zero_or_succ N) ?_ ?_
  · exact le_congr (.eqRefl _) ((congrMul (.eqRefl j) Prf.hyp0).eqTrans (mul_zero j)).eqSymm
      (le_congr (.eqRefl _) Prf.hyp0 hN.wk)
  · have hp : ((N ≐ succ (PTm.pred N)) :: Γ) ⊢[PRAAx] le one N :=
      le_congr (.eqRefl _) Prf.hyp0.eqSymm (zero_lt_succ _)
    exact le_trans hj.wk (le_congr (one_mul j) (mul_comm N j) (mul_le_mul_right j hp))

theorem cauchy_term_zero (C N K j e i : PTm n) (hC : Γ ⊢[PRAAx] entry C N ≐ qzero)
    (hSupport : Γ ⊢[PRAAx] lowSupport C N K j) (he : Γ ⊢[PRAAx] le e N)
    (hej : Γ ⊢[PRAAx] le e j) (hi : Γ ⊢[PRAAx] le i e) : Γ ⊢[PRAAx]
    term (powerPrefix C N K j) C (j*N) N e i ≐ qzero := by
  refine .orE (lt_or_eq_of_le hi) ?_ ?_
  · have hiz := support_at C N K j i hSupport.wk (le_trans (le_of_lt Prf.hyp0) he.wk)
      (lt_of_lt_of_le Prf.hyp0 hej.wk)
    have hip : (lt i e :: Γ) ⊢[PRAAx] le i (j*N) :=
      le_trans (le_of_lt Prf.hyp0) (min_product e j N he.wk hej.wk)
    have hEntry := (exponent_inside (powerPrefix C N K j) (j*N) i hip).eqSymm.eqTrans hiz
    exact (qmul_congr hEntry (.eqRefl _)).eqTrans (qmul_zero_left _)
  · have hidx : ((i ≐ e) :: Γ) ⊢[PRAAx] monus N (monus e i) ≐ N :=
      (congrMonus (.eqRefl _) ((congrMonus (.eqRefl _) Prf.hyp0).eqTrans (monus_self e))).eqTrans (monus_zero N)
    exact (qmul_congr (.eqRefl _) ((entry_congr (.eqRefl _) hidx).eqTrans hC.wk)).eqTrans (qmul_zero_right _)

theorem cauchy_zero (C N K j e : PTm n) (hC : Γ ⊢[PRAAx] entry C N ≐ qzero)
    (hSupport : Γ ⊢[PRAAx] lowSupport C N K j) (he : Γ ⊢[PRAAx] le e N)
    (hej : Γ ⊢[PRAAx] le e j) : Γ ⊢[PRAAx] cauchySum (powerPrefix C N K j) C (j*N) N e ≐ qzero := by
  have hc : Γ.map Fm.shift ⊢[PRAAx] entry (Syn.shift C) (Syn.shift N) ≐ qzero := by
    simpa only [Fm.shift,Fm.subst_eq,Foundations.MasterCertificate.subst_entry,GaussianRationalHorner.subst_qzero,Syn.shift] using hC.shift
  have hs : Γ.map Fm.shift ⊢[PRAAx] lowSupport (Syn.shift C) (Syn.shift N) (Syn.shift K) (Syn.shift j) := by
    simpa only [Fm.shift,subst_lowSupport,Syn.shift] using hSupport.shift
  have hn : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift e) (Syn.shift N) := by
    simpa only [Fm.shift,subst_le,Syn.shift] using he.shift
  have hj : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift e) (Syn.shift j) := by
    simpa only [Fm.shift,subst_le,Syn.shift] using hej.shift
  refine GaussianRationalMatrixFiniteSums.sum_zero_of_terms termBody (succ e) (data (powerPrefix C N K j) C (j*N) N e) (.allI (.impI ?_))
  let Δ := lt (var 0) (succ (Syn.shift e)) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] le (var 0) (Syn.shift e) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  have ht := (term_at (Γ := Δ) (powerPrefix (Syn.shift C) (Syn.shift N) (Syn.shift K) (Syn.shift j))
      (Syn.shift C) (Syn.shift j*Syn.shift N) (Syn.shift N) (Syn.shift e) (var 0)).eqTrans
    (cauchy_term_zero (Syn.shift C) (Syn.shift N) (Syn.shift K) (Syn.shift j) (Syn.shift e) (var 0) hc.wk hs.wk hn.wk hj.wk hi)
  simpa only [Δ,Syn.shift,GaussianRationalLowCoefficientConvolution.subst_data,
    GaussianRationalPolynomialPowers.subst_prefix,PTm.subst_mul,ConciseIPRA.PTm.subst_succ,GaussianRationalHorner.subst_qzero] using ht

theorem successor_zero (C N K j e : PTm n) (hC : Γ ⊢[PRAAx] entry C N ≐ qzero)
    (hSupport : Γ ⊢[PRAAx] lowSupport C N K j) (he : Γ ⊢[PRAAx] le e N)
    (hej : Γ ⊢[PRAAx] lt e (succ j)) (hj : Γ ⊢[PRAAx] lt j K) : Γ ⊢[PRAAx]
    exponentCoefficient (powerPrefix C N K (succ j)) (succ j*N) e ≐ qzero := by
  have ej : Γ ⊢[PRAAx] le e j := (succ_monus_succ _ _).eqSymm.eqTrans hej
  have hp := min_product e j N he ej
  have hnext := le_trans hp (mul_le_mul_right N (le_succ_self j))
  have hEntry : Γ ⊢[PRAAx] entry (powerPrefix C N K (succ j)) (monus (succ j*N) e) ≐
      entry (GaussianRationalPolynomialProduct.product (powerPrefix C N K j) C (j*N) N) (monus (j*N+N) e) :=
    entry_congr (prefix_succ C N K j hj) (congrMonus (by ipra_ring) (.eqRefl _))
  exact (exponent_inside _ _ _ hnext).eqTrans (hEntry.eqTrans
    ((GaussianRationalLowCoefficientConvolution.coefficient_cauchy (powerPrefix C N K j) C (j*N) N e hp he).eqTrans
      (cauchy_zero C N K j e hC hSupport he ej)))

theorem support_zero (C N K : PTm n) : Γ ⊢[PRAAx] supportLaw C N K zero := by
  refine .impI (.allI (.impI (.impI ?_)))
  exact lt_zero_absurd _ (by simpa only [Syn.shift,ConciseIPRA.PTm.subst_zero] using
    (Prf.hyp0 (Ax := PRAAx)))

theorem low_support_step (C N K j : PTm n) (hC : Γ ⊢[PRAAx] entry C N ≐ qzero)
    (hs : Γ ⊢[PRAAx] lowSupport C N K j) (hj : Γ ⊢[PRAAx] lt j K) : Γ ⊢[PRAAx] lowSupport C N K (succ j) := by
  have hc : Γ.map Fm.shift ⊢[PRAAx] entry (Syn.shift C) (Syn.shift N) ≐ qzero := by
    simpa only [Fm.shift,Fm.subst_eq,Foundations.MasterCertificate.subst_entry,GaussianRationalHorner.subst_qzero,Syn.shift] using hC.shift
  have hss : Γ.map Fm.shift ⊢[PRAAx] lowSupport (Syn.shift C) (Syn.shift N) (Syn.shift K) (Syn.shift j) := by
    simpa only [Fm.shift,subst_lowSupport,Syn.shift] using hs.shift
  have hjs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift j) (Syn.shift K) := by
    simpa only [Fm.shift,subst_lt,Syn.shift] using hj.shift
  refine .allI (.impI (.impI ?_))
  let Δ := lt (var 0) (succ (Syn.shift j)) :: lt (var 0) (succ (Syn.shift N)) :: Γ.map Fm.shift
  have he : Δ ⊢[PRAAx] le (var 0) (Syn.shift N) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp1
  have hej : Δ ⊢[PRAAx] lt (var 0) (succ (Syn.shift j)) := Prf.hyp0
  simpa only [Δ,Syn.shift,ConciseIPRA.PTm.subst_succ,GaussianRationalLowCoefficientConvolution.subst_exponentCoefficient,
    GaussianRationalPolynomialPowers.subst_prefix,PTm.subst_mul] using
    successor_zero (Syn.shift C) (Syn.shift N) (Syn.shift K) (Syn.shift j) (var 0) hc.wk.wk hss.wk.wk he hej hjs.wk.wk

theorem support_step (C N K j : PTm n) (hC : Γ ⊢[PRAAx] entry C N ≐ qzero)
    (ih : Γ ⊢[PRAAx] supportLaw C N K j) : Γ ⊢[PRAAx] supportLaw C N K (succ j) := by
  refine .impI ?_
  have hj : (le (succ j) K :: Γ) ⊢[PRAAx] le j K := le_trans (le_succ_self j) Prf.hyp0
  exact low_support_step C N K j hC.wk (.impE ih.wk hj) Prf.hyp0

theorem power_support (C N K j : PTm n) (hC : Γ ⊢[PRAAx] entry C N ≐ qzero)
    (hj : Γ ⊢[PRAAx] le j K) : Γ ⊢[PRAAx] lowSupport C N K j := by
  have hc : Γ.map Fm.shift ⊢[PRAAx] entry (Syn.shift C) (Syn.shift N) ≐ qzero := by
    simpa only [Fm.shift,Fm.subst_eq,Foundations.MasterCertificate.subst_entry,GaussianRationalHorner.subst_qzero,Syn.shift] using hC.shift
  have all : Γ ⊢[PRAAx] .all (formula (supportSyntax (Syn.shift C) (Syn.shift N) (Syn.shift K) (var 0))) := by
    refine Foundations.BoundedSyntaxInduction.induction _ ?_ ?_
    · simpa only [support_formula,subst_supportLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using support_zero (Γ := Γ) C N K
    · simpa only [support_formula,subst_supportLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
        support_step (Γ := formula (supportSyntax (Syn.shift C) (Syn.shift N) (Syn.shift K) (var 0)) :: Γ.map Fm.shift)
          (Syn.shift C) (Syn.shift N) (Syn.shift K) (var 0) hc.wk
          (by simpa only [support_formula] using (Prf.hyp0 (Ax := PRAAx)))
  have gate : Γ ⊢[PRAAx] supportLaw C N K j := by
    simpa only [support_formula,subst_supportLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j
  exact .impE gate hj

theorem low_power_zero (C N K j e : PTm n) (hC : Γ ⊢[PRAAx] entry C N ≐ qzero)
    (hj : Γ ⊢[PRAAx] le j K) (he : Γ ⊢[PRAAx] le e N) (hej : Γ ⊢[PRAAx] lt e j) : Γ ⊢[PRAAx]
    exponentCoefficient (powerPrefix C N K j) (j*N) e ≐ qzero :=
  support_at C N K j e (power_support C N K j hC hj) he hej

theorem logarithm_power_zero (d K j e : PTm n) (hj : Γ ⊢[PRAAx] le j K)
    (he : Γ ⊢[PRAAx] le e d) (hej : Γ ⊢[PRAAx] lt e j) : Γ ⊢[PRAAx]
    exponentCoefficient (powerPrefix (GaussianFiniteLogarithmPolynomial.polynomial d) d K j) (j*d) e ≐ qzero :=
  low_power_zero _ _ _ _ _ (GaussianFiniteLogarithmPolynomial.polynomial_constant d) hj he hej

def output (C N K j e : PTm n) : PTm n :=
  pairT (powerPrefix C N K j) (exponentCoefficient (powerPrefix C N K j) (j*N) e)
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (C N K j e : PTm n) : PTm n := PTm.app outputF ![C,N,K,j,e]
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (C N K j e : PTm n) :
    Syn.subst σ (output C N K j e) = output (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ K) (Syn.subst σ j) (Syn.subst σ e) := by
  simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (C N K j e : PTm n) :
    Syn.subst σ (run C N K j e) = run (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ K) (Syn.subst σ j) (Syn.subst σ e) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem program_at (C N K j e : PTm n) : Γ ⊢[PRAAx] run C N K j e ≐ output C N K j e := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![C,N,K,j,e]
theorem returned_power (C N K j e : PTm n) : Γ ⊢[PRAAx] fstT (run C N K j e) ≐ powerPrefix C N K j :=
  (congrFst (program_at C N K j e)).eqTrans (fst_pair _ _)
theorem returned_coefficient (C N K j e : PTm n) : Γ ⊢[PRAAx]
    sndT (run C N K j e) ≐ exponentCoefficient (powerPrefix C N K j) (j*N) e :=
  (congrSnd (program_at C N K j e)).eqTrans (snd_pair _ _)
theorem returned_zero (C N K j e : PTm n) (hC : Γ ⊢[PRAAx] entry C N ≐ qzero)
    (hj : Γ ⊢[PRAAx] le j K) (he : Γ ⊢[PRAAx] le e N) (hej : Γ ⊢[PRAAx] lt e j) : Γ ⊢[PRAAx]
    sndT (run C N K j e) ≐ qzero :=
  (returned_coefficient C N K j e).eqTrans (low_power_zero C N K j e hC hj he hej)

theorem actual_power_low_support_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (entry (var 0) (var 1) ≐ qzero ⟶ le (var 3) (var 2) ⟶ lowSupport (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (power_support _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_low_power_coefficient_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (entry (var 0) (var 1) ≐ qzero ⟶ le (var 3) (var 2) ⟶ le (var 4) (var 1) ⟶ lt (var 4) (var 3) ⟶
      exponentCoefficient (powerPrefix (var 0) (var 1) (var 2) (var 3)) (var 3*var 1) (var 4) ≐ qzero) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (low_power_zero _ _ _ _ _ Prf.hyp0.wk.wk.wk hyp2 Prf.hyp1 Prf.hyp0)))))
theorem original_logarithm_power_support_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (var 2) (var 1) ⟶ le (var 3) (var 0) ⟶ lt (var 3) (var 2) ⟶
      exponentCoefficient (powerPrefix (GaussianFiniteLogarithmPolynomial.polynomial (var 0)) (var 0) (var 1) (var 2))
        (var 2*var 0) (var 3) ≐ qzero) :=
  closeUniv 4 (.impI (.impI (.impI (logarithm_power_zero _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))
theorem actual_power_support_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (program_at _ _ _ _ _)
theorem actual_returned_low_power_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (entry (var 0) (var 1) ≐ qzero ⟶ le (var 3) (var 2) ⟶ le (var 4) (var 1) ⟶ lt (var 4) (var 3) ⟶
      sndT (run (var 0) (var 1) (var 2) (var 3) (var 4)) ≐ qzero) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (returned_zero _ _ _ _ _ Prf.hyp0.wk.wk.wk hyp2 Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianRationalPolynomialPowerSupport

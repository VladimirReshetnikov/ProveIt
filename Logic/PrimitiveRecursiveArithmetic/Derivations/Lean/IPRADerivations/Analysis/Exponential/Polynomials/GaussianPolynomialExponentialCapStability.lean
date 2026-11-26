import IPRADerivations.Analysis.Exponential.Polynomials.GaussianRationalPolynomialExponentialStability
import IPRADerivations.Core.CongruenceTactic

/-!
# Exact cap independence of the original finite exponential coefficients

A genuine joint numerical QF induction shows that the SAME original
power-prefix and exponential-stage buffers are literally independent
of the ambient power cap as long as the stage fits both caps. The
original repeated-table factors are identified only under their actual
cap guards. The old zero-constant support theorem then proves that an
exponent-e coefficient agrees at any two actual exponential cutoffs
K,H with e<=K,H and e<=N. No formal polynomial exponential, power
recurrence, or wanted coefficient equality is an input premise.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialExponentialCapStability

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qzero)
open GaussianRationalPolynomialPowers (powerPrefix)
open GaussianRationalPolynomialExponential (stage polynomial inverseFactorial)
open GaussianRationalPolynomialBuffers (added leftPad)
open GaussianRationalCoefficientScaling (scaled)
open GaussianRationalLowCoefficientConvolution (exponentCoefficient)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def parts (N j Q P : PTm n) : PTm n :=
  added (leftPad Q N) (scaled P (inverseFactorial (succ j))) (succ (succ j*N))
@[simp] theorem subst_parts {m : ℕ} (σ : Fin n → PTm m) (N j Q P : PTm n) :
    Syn.subst σ (parts N j Q P) = parts (Syn.subst σ N) (Syn.subst σ j) (Syn.subst σ Q) (Syn.subst σ P) := by simp [parts]

theorem parts_congr (N j : PTm n) {Q Q' P P' : PTm n} (hQ : Γ ⊢[PRAAx] Q ≐ Q')
    (hP : Γ ⊢[PRAAx] P ≐ P') : Γ ⊢[PRAAx] parts N j Q P ≐ parts N j Q' P' := by
  ipra_congr (parts (var 0) (var 1) (var 2) (var 3) : PTm 4) with [.eqRefl N, .eqRefl j, hQ, hP]

def capLaw (C N K H j : PTm n) : Fm PTm n := le j K ⟶ le j H ⟶
  powerPrefix C N K j ≐ powerPrefix C N H j ⋏ stage C N K j ≐ stage C N H j
@[simp] theorem subst_capLaw {m : ℕ} (σ : Fin n → PTm m) (C N K H j : PTm n) :
    (capLaw C N K H j).subst σ = capLaw (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ K)
      (Syn.subst σ H) (Syn.subst σ j) := by simp [capLaw]

theorem cap_zero (C N K H : PTm n) : Γ ⊢[PRAAx] capLaw C N K H zero :=
  .impI (.impI (.andI
    ((GaussianRationalPolynomialPowers.prefix_zero C N K).eqTrans (GaussianRationalPolynomialPowers.prefix_zero C N H).eqSymm)
    ((GaussianRationalPolynomialExponential.stage_zero C N K).eqTrans (GaussianRationalPolynomialExponential.stage_zero C N H).eqSymm)))

theorem cap_step (C N K H j : PTm n) (ih : Γ ⊢[PRAAx] capLaw C N K H j) : Γ ⊢[PRAAx]
    capLaw C N K H (succ j) := by
  refine .impI (.impI ?_)
  let Δ := le (succ j) H :: le (succ j) K :: Γ
  have hk : Δ ⊢[PRAAx] le j K := le_trans (le_succ_self j) Prf.hyp1
  have hh : Δ ⊢[PRAAx] le j H := le_trans (le_succ_self j) Prf.hyp0
  have previous := Prf.impE (Prf.impE ih.wk.wk hk) hh
  have powers : Δ ⊢[PRAAx] powerPrefix C N K (succ j) ≐ powerPrefix C N H (succ j) :=
    (GaussianRationalPolynomialPowers.prefix_succ C N K j Prf.hyp1).eqTrans
      ((GaussianPolynomialDeterminantTerms.product_congr previous.andE₁ (.eqRefl C) (.eqRefl (j*N)) (.eqRefl N)).eqTrans
        (GaussianRationalPolynomialPowers.prefix_succ C N H j Prf.hyp0).eqSymm)
  have stages : Δ ⊢[PRAAx] stage C N K (succ j) ≐ stage C N H (succ j) :=
    (GaussianRationalPolynomialExponential.stage_succ C N K j).eqTrans
      ((parts_congr N j previous.andE₂ powers).eqTrans
        (GaussianRationalPolynomialExponential.stage_succ C N H j).eqSymm)
  exact .andI powers stages

theorem common_stage (C N K H j : PTm n) (hK : Γ ⊢[PRAAx] le j K) (hH : Γ ⊢[PRAAx] le j H) : Γ ⊢[PRAAx]
    powerPrefix C N K j ≐ powerPrefix C N H j ⋏ stage C N K j ≐ stage C N H j := by
  have all : Γ ⊢[PRAAx] .all (capLaw (Syn.shift C) (Syn.shift N) (Syn.shift K) (Syn.shift H) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,⟨le_QF _ _,⟨trivial,trivial⟩⟩⟩ ?_ ?_
    · simp only [subst_capLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact cap_zero C N K H
    · simp only [subst_capLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact cap_step _ _ _ _ _ Prf.hyp0
  have gate : Γ ⊢[PRAAx] capLaw C N K H j := by
    simpa only [subst_capLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j
  exact Prf.impE (Prf.impE gate hK) hH

theorem power_cap_identity (C N K H j : PTm n) (hK : Γ ⊢[PRAAx] le j K) (hH : Γ ⊢[PRAAx] le j H) : Γ ⊢[PRAAx]
    powerPrefix C N K j ≐ powerPrefix C N H j := (common_stage C N K H j hK hH).andE₁
theorem stage_cap_identity (C N K H j : PTm n) (hK : Γ ⊢[PRAAx] le j K) (hH : Γ ⊢[PRAAx] le j H) : Γ ⊢[PRAAx]
    stage C N K j ≐ stage C N H j := (common_stage C N K H j hK hH).andE₂

theorem exponential_coefficient_cap_identity (C N K H e : PTm n)
    (hC : Γ ⊢[PRAAx] LeanProofs.IPRA.Foundations.MasterCertificate.entry C N ≐ qzero)
    (he : Γ ⊢[PRAAx] le e N) (hK : Γ ⊢[PRAAx] le e K) (hH : Γ ⊢[PRAAx] le e H) : Γ ⊢[PRAAx]
    exponentCoefficient (polynomial C N K) (K*N) e ≐ exponentCoefficient (polynomial C N H) (H*N) e :=
  (GaussianRationalPolynomialExponentialStability.finite_exponential_cutoff C N K e hC he hK).eqTrans
    ((GaussianRationalPolynomialExponentialStability.exponent_congr (stage_cap_identity C N K H e hK hH)
      (.eqRefl (e*N)) (.eqRefl e)).eqTrans
        (GaussianRationalPolynomialExponentialStability.finite_exponential_cutoff C N H e hC he hH).eqSymm)

theorem original_power_and_exponential_common_stage_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (var 4) (var 2) ⟶ le (var 4) (var 3) ⟶
      powerPrefix (var 0) (var 1) (var 2) (var 4) ≐ powerPrefix (var 0) (var 1) (var 3) (var 4) ⋏
        stage (var 0) (var 1) (var 2) (var 4) ≐ stage (var 0) (var 1) (var 3) (var 4)) :=
  closeUniv 5 (.impI (.impI (common_stage _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem original_exponential_coefficient_cap_independence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (LeanProofs.IPRA.Foundations.MasterCertificate.entry (var 0) (var 1) ≐ qzero ⟶
      le (var 4) (var 1) ⟶ le (var 4) (var 2) ⟶ le (var 4) (var 3) ⟶
      exponentCoefficient (polynomial (var 0) (var 1) (var 2)) (var 2*var 1) (var 4) ≐
        exponentCoefficient (polynomial (var 0) (var 1) (var 3)) (var 3*var 1) (var 4)) :=
  closeUniv 5 (.impI (.impI (.impI (.impI
    (exponential_coefficient_cap_identity _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianPolynomialExponentialCapStability

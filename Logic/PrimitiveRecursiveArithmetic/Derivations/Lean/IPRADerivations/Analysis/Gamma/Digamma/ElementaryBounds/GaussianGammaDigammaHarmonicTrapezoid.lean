import IPRADerivations.Analysis.Euler.HarmonicLogarithms.GaussianHarmonicIntervalLinearRemainder
import IPRADerivations.Analysis.Gamma.Digamma.Derivative.GaussianGammaDigammaEulerDerivative

/-!
# Trapezoid bound on the original harmonic mesh

The affine chord through 1/A and 1/(A+W) bounds every right
rectangle in the block. Quantifier-free induction adds the cleared
rectangle inequalities on the original factorial mesh.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaHarmonicTrapezoid

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB inst2_h)
open LeanProofs.IPRA.AnalyticNumberTheory.LogElementary (mul_quo_succ)
open GaussianRationalHorner (positive_product)
open Products (fact)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem chord (A W F j : PTm n) (hj : Γ ⊢[PRAAx] le (succ j) W) :
    Γ ⊢[PRAAx] le (A*(A+W)*quo F (succ (A+j))+succ j*F) ((A+W)*F) := by
  let P := A+monus W (succ j)
  have h := mul_le_mul_right P (mul_quo_succ (Γ := Γ) (A+j) F)
  have e := natEq (eq_add_of_le hj)
  unfold P at h
  ipra_le sl h+𝔞 (succ j)*𝔞 (monus W (succ j))*𝔞 (quo F (succ (A+j))) using
    linear_combination (𝔞 F-𝔞 A*𝔞 (quo F (succ (A+j))))*e

def prefixLaw (A W F j : PTm n) : Fm PTm n :=
  le j W ⟶ le (two*A*(A+W)*S (A+j) F+j*succ j*F) (two*A*(A+W)*S A F+two*(A+W)*j*F)

ipra_subst prefixLaw

private theorem prefix_zero (A W F : PTm n) : Γ ⊢[PRAAx] prefixLaw A W F zero := by
  refine .impI ?_
  have e := congrAp2 (sumF hB) (LeanProofs.IPRA.add_zero (Γ := le zero W::Γ) A) (.eqRefl F)
  have h := natEq e
  change (le zero W::Γ) ⊢[PRAAx] le (two*A*(A+W)*S (A+zero) F+zero*succ zero*F)
    (two*A*(A+W)*S A F+two*(A+W)*zero*F)
  ipra_le 0 with (2*𝔞 A*(𝔞 A+𝔞 W))*h

private theorem prefix_step (A W F j : PTm n) (ih : Γ ⊢[PRAAx] prefixLaw A W F j) :
    Γ ⊢[PRAAx] prefixLaw A W F (succ j) := by
  refine .impI ?_
  let Δ := le (succ j) W :: Γ
  have h : Δ ⊢[PRAAx] le (succ j) W := Prf.hyp0
  have old := Prf.impE ih.wk (le_trans (le_succ_self j) h)
  have loc := chord A W F j h
  have step : Δ ⊢[PRAAx] S (A+succ j) F ≐ S (A+j) F+quo F (succ (A+j)) := by
    refine (congrAp2 (sumF hB) (add_succ A j) (.eqRefl _)).eqTrans ((sum_succ' hB _ _).eqTrans ?_)
    rw [inst2_h]
    exact .eqRefl _
  have e := natEq step
  change Δ ⊢[PRAAx] le (two*A*(A+W)*S (A+succ j) F+succ j*succ (succ j)*F)
    (two*A*(A+W)*S A F+two*(A+W)*succ j*F)
  ipra_le sl old+2*sl loc with (2*𝔞 A*(𝔞 A+𝔞 W))*e

theorem prefix_bound (A W F j : PTm n) : Γ ⊢[PRAAx] prefixLaw A W F j := by
  have h : Γ ⊢[PRAAx] .all (prefixLaw (Syn.shift A) (Syn.shift W) (Syn.shift F) (var 0)) := by
    refine PRA.qfInd _ (by unfold prefixLaw; exact ⟨le_QF _ _,le_QF _ _⟩) ?_ ?_
    · simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using prefix_zero (Γ := Γ) A W F
    · simpa only [subst_prefixLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
        prefix_step (Syn.shift A) (Syn.shift W) (Syn.shift F) (var 0) Prf.hyp0
  simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE j

theorem block (A W F : PTm n) :
    Γ ⊢[PRAAx] le (two*A*(A+W)*S (A+W) F)
      (two*A*(A+W)*S A F+W*(two*A+W)*F) := by
  have e := Prf.impE (prefix_bound (Γ := Γ) A W F W) (le_refl W)
  ipra_le sl e+𝔞 W*𝔞 F

theorem factorial_trapezoid (a b Q L : PTm n) (hq : Γ ⊢[PRAAx] le one Q) :
    Γ ⊢[PRAAx] le (two*a*(a+b)*S (Q*(a+b)) (fact L))
      (two*a*(a+b)*S (Q*a) (fact L)+b*(two*a+b)*fact L) := by
  let F := fact L
  let A := Q*a
  let W := Q*b
  have t := block (Γ := Γ) A W F
  have e : Γ ⊢[PRAAx] S (A+W) F ≐ S (Q*(a+b)) F :=
    congrAp2 (sumF hB) (by unfold A W; ipra_ring) (.eqRefl _)
  apply RationalValueBounds.positive_cancel (positive_product Q Q hq hq)
  exact le_congr ((congrMul (.eqRefl _) e).eqTrans (by
    dsimp only [A,W,F]
    ipra_ring)) (by dsimp only [A,W,F]; ipra_ring) t

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaHarmonicTrapezoid

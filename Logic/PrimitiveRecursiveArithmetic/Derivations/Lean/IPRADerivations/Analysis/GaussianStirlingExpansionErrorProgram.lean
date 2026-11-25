import IPRADerivations.Analysis.GaussianStirlingExpansionConditionalError

/-!
# The error-producing program for multiplicative Stirling truncation

At each fixed order the actual primitive-recursive program returns
the truncated polynomial and its certified rational error radius
at the caller's precision. Its premise is the original named
logarithmic truncation rate at that order.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingExpansionErrorProgram

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalMetric (distanceBounded)
open GaussianStirlingExpansionConditionalError (logRate radius budget numerator original_approximation)
open GaussianStirlingExpansionExponentialError (logBudget TaylorBudget expansionDenominator)
open GaussianStirlingExpansionFiniteError (query approximation)
open GaussianStirlingMultiplicative (quotientF quotientData)
open GaussianStirlingNames (source)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def output (m : ℕ) (p a b C : PTm n) : PTm n :=
  pairT (approximation m a b) (pairT (numerator m p a b C) (expansionDenominator m p a))

def outputF (m : ℕ) : PR 4 := PTm.toPR (output m (var 0) (var 1) (var 2) (var 3))
def run (m : ℕ) (p a b C : PTm n) : PTm n := ConciseIPRA.PTm.app (outputF m) ![p,a,b,C]

@[simp] theorem subst_output {k : ℕ} (σ : Fin n → PTm k) (m : ℕ) (p a b C : PTm n) :
    Syn.subst σ (output m p a b C) = output m (Syn.subst σ p) (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ C) := by
  simp [output,approximation,query,numerator,budget,radius,logBudget,TaylorBudget,expansionDenominator,RationalSupMetric.numeratorOf]

theorem program_at (m : ℕ) (p a b C : PTm n) : Γ ⊢[PRAAx] run m p a b C ≐ output m p a b C := by
  simpa only [run,outputF,subst_output,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
    toPR_eq (Γ := Γ) (output m (var 0) (var 1) (var 2) (var 3) : PTm 4) ![p,a,b,C]

theorem returned_approximation_bound (m : ℕ) (p a b x C : PTm n) (hs : Γ ⊢[PRAAx] source a b)
    (hab : Γ ⊢[PRAAx] le b a) (hsmall : Γ ⊢[PRAAx] le (two*(logBudget m*b)) a)
    (h : Γ ⊢[PRAAx] logRate m a b x C) :
    Γ ⊢[PRAAx] distanceBounded (ap2 quotientF p (quotientData a b x)) (fstT (run m p a b C))
      (fstT (sndT (run m p a b C))) (sndT (sndT (run m p a b C))) := by
  have read := program_at (Γ := Γ) m p a b C
  have aRead := (congrFst read).eqTrans (fst_pair _ _)
  have eRead := (congrSnd read).eqTrans (snd_pair _ _)
  exact GaussianRationalDistanceOrder.distance_congr (.eqRefl _) aRead.eqSymm
    ((congrFst eRead).eqTrans (fst_pair _ _)).eqSymm ((congrSnd eRead).eqTrans (snd_pair _ _)).eqSymm
    (original_approximation m p a b x C hs hab hsmall h)

theorem actual_Stirling_multiplicative_error_program_closed (m : ℕ) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (source (var 1) (var 2) ⟶ le (var 2) (var 1) ⟶ le (two*(logBudget m*var 2)) (var 1) ⟶
        logRate m (var 1) (var 2) (var 3) (var 4) ⟶
        distanceBounded (ap2 quotientF (var 0) (quotientData (var 1) (var 2) (var 3)))
          (fstT (run m (var 0) (var 1) (var 2) (var 4)))
          (fstT (sndT (run m (var 0) (var 1) (var 2) (var 4))))
          (sndT (sndT (run m (var 0) (var 1) (var 2) (var 4))))) :=
  closeUniv 5 (.impI (.impI (.impI (.impI
    (returned_approximation_bound m _ _ _ _ _ Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianStirlingExpansionErrorProgram

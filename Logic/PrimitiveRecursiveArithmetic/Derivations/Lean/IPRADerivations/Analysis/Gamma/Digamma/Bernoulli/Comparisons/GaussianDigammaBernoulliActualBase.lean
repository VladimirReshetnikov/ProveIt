import IPRADerivations.Analysis.Gamma.Digamma.Bernoulli.Comparisons.GaussianDigammaBernoulliPositive
import IPRADerivations.Analysis.Gamma.Digamma.Bernoulli.FirstTerm.GaussianDigammaFirstBernoulliImproper

/-!
# The actual digamma base supplies the higher positivity proofs

The mesh demand is the one from the literal first Bernoulli
weighted prefix. Its uniform cutoff proof discharges the base
premise for each higher order.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianDigammaBernoulliActualBase

open_ipra
open GaussianDigammaBernoulliBaseAgreement (agreement)
open GaussianDigammaBernoulliName (nameF nameData)
open GaussianDigammaBernoulliPositive (floorPoint named_lower named_positive)
open GaussianDigammaFirstBernoulliImproper (baseF baseData base_regular meshDemand subst_meshDemand original_base_rate)
open GaussianGammaCanonicalExponent (constantF)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianStirlingMultiplicativeBoundsStrictOrder (strictOrder)
open GaussianStirlingNames (source)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def demandF : PR 3 := PTm.toPR (meshDemand (var 0) (var 1) (var 2))
def baseCost (A : PTm n) : PTm n := two*A+num 36

theorem demand_at (p A B : PTm n) : Γ ⊢[PRAAx] ap3 demandF p A B ≐ meshDemand p A B := by
  simpa only [demandF,ap3,subst_meshDemand,Syn.subst_var,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
    toPR_eq (Γ := Γ) (meshDemand (var 0) (var 1) (var 2) : PTm 3) ![p,A,B]

theorem actual_agreement (A B : PTm n) (hs : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] agreement baseF demandF A B (baseData A B) (baseCost A) := by
  refine .allI (.allI (.impI ?_))
  let sh (v : PTm n) := Syn.shift (Syn.shift v)
  let a := sh A
  let b := sh B
  let p : PTm (n+2) := var 1
  let Q : PTm (n+2) := var 0
  let hyp := le one Q ⋏ le (ap3 demandF p a b) Q
  let Δ := hyp :: (Γ.map Fm.shift).map Fm.shift
  have s : Δ ⊢[PRAAx] source a b := by simpa [Δ,a,b,sh,Fm.shift,Syn.shift] using hs.shift.shift.wk
  have hq : Δ ⊢[PRAAx] le (ap3 demandF p a b) Q := Prf.hyp0.andE₂
  have h : Δ ⊢[PRAAx] le (meshDemand p a b) Q := le_congr (demand_at p a b) (.eqRefl _) hq
  simpa [agreement,baseCost,GaussianDigammaBernoulliRecurrence.prefixAt,sh,a,b,p,Q,Δ,hyp,Syn.shift,two,one] using
    original_base_rate p a b Q s h

theorem original_named_lower (m : ℕ) (A B : PTm n) (hs : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] realOrder constantF (nameF baseF m) (floorPoint m A B) (nameData m A B (baseData A B)) :=
  named_lower baseF demandF m A B _ _ hs (base_regular A B hs) (actual_agreement A B hs)

theorem original_named_positive (m : ℕ) (A B : PTm n) (hs : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] strictOrder constantF (nameF baseF m) (GaussianPositiveRationalLogarithm.fraction zero one)
      (nameData m A B (baseData A B)) :=
  named_positive baseF demandF m A B _ _ hs (base_regular A B hs) (actual_agreement A B hs)

theorem actual_digamma_Bernoulli_recurrence_positivity_closed (m : ℕ) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 (source (var 0) (var 1) ⟶
      (realOrder constantF (nameF baseF m) (floorPoint m (var 0) (var 1))
        (nameData m (var 0) (var 1) (baseData (var 0) (var 1))) ⋏
      strictOrder constantF (nameF baseF m) (GaussianPositiveRationalLogarithm.fraction zero one)
        (nameData m (var 0) (var 1) (baseData (var 0) (var 1))))) :=
  closeUniv 2 (.impI (.andI (original_named_lower m _ _ Prf.hyp0) (original_named_positive m _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianDigammaBernoulliActualBase

import IPRADerivations.Analysis.Exponential.GaussianExponentialReference
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedMultiplyRate

/-!
# Observations of the actual named sum with prescribed bounds

The two all-sample bounds apply at the clock selected by the original
sum evaluator. Its exact rational addition therefore obeys their sum.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedBoundedSumObservation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNameArithmetic (addF addData)
open GaussianNamedMultiplyRate (sampleBound)
open GaussianRationalMetric (bounded)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem sample_bound_at (F₁ F₂ : PR 2) (x y M P p : PTm n)
    (hx : Γ ⊢[PRAAx] sampleBound F₁ x M) (hy : Γ ⊢[PRAAx] sampleBound F₂ y P) :
    Γ ⊢[PRAAx] bounded (ap2 (addF F₁ F₂) p (addData x y)) (M+P) one := by
  let q := GaussianFastValueCut.exponent two p
  have raw := (GaussianNameArithmetic.add_at (Γ := Γ) F₁ F₂ x y p).eqTrans
    (GaussianExponentialReference.recode_fixed _ (GaussianRationalHorner.qadd_canonical _ _))
  exact GaussianRationalReciprocal.bound_congr raw.eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianRationalPowerDifference.bounded_sum_same _ _ _ _ _ (le_refl one)
      (GaussianNamedMultiplyRate.sample_bound_at F₁ x M q hx)
      (GaussianNamedMultiplyRate.sample_bound_at F₂ y P q hy))

theorem sample_bounds (F₁ F₂ : PR 2) (x y M P : PTm n)
    (hx : Γ ⊢[PRAAx] sampleBound F₁ x M) (hy : Γ ⊢[PRAAx] sampleBound F₂ y P) :
    Γ ⊢[PRAAx] sampleBound (addF F₁ F₂) (addData x y) (M+P) := by
  refine .allI ?_
  let sh (t : PTm n) := Syn.shift t
  have hx' : Γ.map Fm.shift ⊢[PRAAx] sampleBound F₁ (sh x) (sh M) := by simpa [Fm.shift,Syn.shift,sh] using hx.shift
  have hy' : Γ.map Fm.shift ⊢[PRAAx] sampleBound F₂ (sh y) (sh P) := by simpa [Fm.shift,Syn.shift,sh] using hy.shift
  simpa only [sampleBound,GaussianNameArithmetic.subst_addData,Syn.shift,sh,PTm.subst_add] using
    sample_bound_at F₁ F₂ (sh x) (sh y) (sh M) (sh P) (var 0) hx' hy'

end LeanProofs.IPRA.Analysis.GaussianNamedBoundedSumObservation

import IPRADerivations.Analysis.Series.Harmonic.RationalHarmonicIntervalVariation
import IPRADerivations.Core.CommonLemmas
import IPRADerivations.Core.InductionTactic

/-!
# A dyadic upper bound for the finite harmonic numerator

Each doubling adds at most one denominator unit to the harmonic sum.
The estimate holds for the original quotient summands and for any
common numerator.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalHarmonicDyadicUpper

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB S_one pw2_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicChebyshev (S_mono)
open LeanProofs.IPRA.Common (mul_cancel_le)
open RationalHarmonicIntervalVariation (harmonic_increment)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem next (j F : PTm n)
    (ih : Γ ⊢[PRAAx] le (S (pw two j) F) ((one+j)*F)) :
    Γ ⊢[PRAAx] le (S (pw two (succ j)) F) ((one+succ j)*F) := by
  let v := pw two j
  have hv : Γ ⊢[PRAAx] le one v :=
    le_congr (.eqRefl _) (pw2_pos j).eqSymm (zero_lt_succ _)
  have same : Γ ⊢[PRAAx] pw two (succ j) ≐ v+v :=
    (pw_succ _ _).eqTrans (by ipra_ring)
  have delta : Γ ⊢[PRAAx] monus (v+v) v ≐ v := add_monus' v v
  have increment := harmonic_increment (Γ := Γ) (v+v) v F (le_add_right v v)
  have clear : Γ ⊢[PRAAx] le (v*S (pw two (succ j)) F) (v*(S v F+F)) :=
    le_congr (congrMul (.eqRefl _) (congrAp2 (sumF hB) same.eqSymm (.eqRefl F)))
      ((congrAdd (.eqRefl _) (congrMul delta (.eqRefl F))).eqTrans (by ipra_ring)) increment
  exact le_trans (mul_cancel_le hv clear)
    (le_congr (.eqRefl _) (by ipra_ring) (add_le_add_right F ih))

private abbrev boundF : Fm PTm 2 :=
  le (S (pw two (var 0)) (var 1)) ((one+var 0)*var 1)

private theorem bound₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] boundF := by
  ipra_ind (le_QF _ _) [subst_le, subst_ap2]
  · exact le_congr (S_one _).eqSymm (by ipra_ring) (le_refl _)
  · exact next _ _ Prf.hyp0

theorem dyadic (j F : PTm n) : Γ ⊢[PRAAx] le (S (pw two j) F) ((one+j)*F) := by
  simpa [one,two] using inst (Γ := Γ) bound₀ (![j,F] : Fin 2 → PTm n)

theorem upper (N j F : PTm n) (hN : Γ ⊢[PRAAx] le N (pw two j)) :
    Γ ⊢[PRAAx] le (S N F) ((one+j)*F) :=
  le_trans (S_mono F hN) (dyadic j F)

theorem actual_harmonic_dyadic_upper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 0) (pw two (var 1)) ⟶ le (S (var 0) (var 2)) ((one+var 1)*var 2)) :=
  closeUniv 3 (.impI (upper _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.RationalHarmonicDyadicUpper

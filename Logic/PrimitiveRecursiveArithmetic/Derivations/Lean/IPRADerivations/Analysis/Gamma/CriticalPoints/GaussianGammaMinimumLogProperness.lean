import IPRADerivations.Analysis.Gamma.GaussianGammaPositiveRationalProperness

/-!
# The original positive log-Gamma respects equality of rational inputs

The independent clocks of the projected Gamma and positive logarithm
remain in place while changing the numerator and denominator of the
input. Both positive-log certificates may use a common upper bound.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaMinimumLogProperness

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (bounded_radius_mono)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans)
open GaussianNamedPositiveLogarithm (admissible admissible_at)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianStirlingGammaLogarithm
  (source arg euler_real_source logGammaF logGammaData gammaLogMargin gammaRetimedF gammaRetimedData
    gamma_retimed_cross gammaData gammaRealF log_input)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem log_source_enlarge (f : PR 2) (x E T U : PTm n)
    (h : Γ ⊢[PRAAx] GaussianNamedPositiveLogarithm.source f x E T)
    (hu : Γ ⊢[PRAAx] le T U) : Γ ⊢[PRAAx] GaussianNamedPositiveLogarithm.source f x E U := by
  let s (t : PTm n) := Syn.shift t
  let Δ := Γ.map Fm.shift
  let z := ap2 f (var 0) (s x)
  have h' : Δ ⊢[PRAAx] GaussianNamedPositiveLogarithm.source f (s x) (s E) (s T) := by
    simpa [Δ,Fm.shift,Syn.shift,s] using h.shift
  have hu' : Δ ⊢[PRAAx] le (s T) (s U) := by
    simpa [Δ,Fm.shift,Syn.shift,s] using hu.shift
  have hobs := admissible_at f (var 0) (s x) (s E) (s T) h'
  have bounds := hobs.andE₂
  have widened := bounded_radius_mono z (s T) one (s U) one (le_refl _) (le_refl _)
    (le_congr (by ipra_ring) (by ipra_ring) hu') bounds.andE₂.andE₂.andE₂
  refine .andI h.andE₁ (.andI h.andE₂.andE₁ (.allI ?_))
  exact .andI hobs.andE₁ (.andI bounds.andE₁ (.andI bounds.andE₂.andE₁
    (.andI bounds.andE₂.andE₂.andE₁ widened)))

theorem log_gamma_cross (a b c d : PTm n) (ha : Γ ⊢[PRAAx] source a b) (hc : Γ ⊢[PRAAx] source c d)
    (e : Γ ⊢[PRAAx] fraction a b ≐ fraction c d) :
    Γ ⊢[PRAAx] crossEquivalent logGammaF logGammaF (logGammaData a b) (logGammaData c d) := by
  let T := GaussianNameBounds.U gammaRealF (gammaData a b)
  let U := GaussianNameBounds.U gammaRealF (gammaData c d)
  let x := gammaRetimedData a b
  let y := gammaRetimedData c d
  have bridge := GaussianGammaPositiveRationalProperness.original_cross (arg a) a b b c d
    (.andI (euler_real_source a b ha).andE₁ ha.andE₁) hc e
  have cross := cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (gamma_retimed_cross a b ha))
    (cross_trans _ _ _ _ _ _ bridge (gamma_retimed_cross c d hc))
  exact GaussianNamedPositiveLogarithm.proper gammaRetimedF gammaRetimedF x y gammaLogMargin (T+U)
    (log_source_enlarge _ _ _ T _ (log_input a b ha) (le_add_right _ _))
    (log_source_enlarge _ _ _ U _ (log_input c d hc) (le_add_left _ _)) cross

theorem actual_original_log_Gamma_equal_rational_inputs_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((source (var 0) (var 1) ⋏ (source (var 2) (var 3) ⋏ fraction (var 0) (var 1) ≐ fraction (var 2) (var 3))) ⟶
      crossEquivalent logGammaF logGammaF (logGammaData (var 0) (var 1)) (logGammaData (var 2) (var 3))) :=
  closeUniv 4 (.impI (log_gamma_cross _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaMinimumLogProperness

import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactAlignedTime
import IPRADerivations.Analysis.Integration.CompactGrids.Splits.GaussianCompactRiemannAdditivity

/-!
# Original shared-step splitting from aligned-time observations alone

Only the actual zero-time-distance sample comparison is assumed. The
original inside/grid-value geometry, literal sum split and common-weight
finite sum bound are reused. Empty width-scaled sums are literal zero,
so both widths may be zero without a sampled near-time modulus.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianCompactAlignedSplit

open_ipra
open GaussianCompactAlignedTime (alignedSamples)
open GaussianRationalHorner (qadd)
open GaussianRationalMetric (distanceBounded)
open GaussianCoefficientNameBounds (unit)
open GaussianCompactRiemannName (sampleBody sampleData quadrature)
open GaussianCompactRiemannSplit (fullData prefixPart suffixPart)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def positiveInput (F : PR 3) (a C1 C2 E K x : PTm n) : Fm PTm n :=
  le one a ⋏ (le one E ⋏ (le one K ⋏ (le one C1 ⋏ (le one C2 ⋏ alignedSamples F a (C1+C2) E x))))
ipra_subst positiveInput

theorem prefix_term_distance (F : PR 3) (i s a C1 C2 E K x : PTm n) (h : Γ ⊢[PRAAx] positiveInput F a C1 C2 E K x)
    (hi : Γ ⊢[PRAAx] lt i (C1*K)) : Γ ⊢[PRAAx]
    distanceBounded (inst2 (sampleBody F) i (fullData s K a C1 C2 E x))
      (inst2 (sampleBody F) i (sampleData s (C1*K) a C1 E x)) two (unit s) :=
  GaussianCompactRiemannAdditivity.aligned_prefix_term_distance F i s a C1 C2 E K x h hi

theorem suffix_term_distance (F : PR 3) (i s a C1 C2 E K x : PTm n) (h : Γ ⊢[PRAAx] positiveInput F a C1 C2 E K x)
    (hi : Γ ⊢[PRAAx] lt i (C2*K)) : Γ ⊢[PRAAx]
    distanceBounded (inst2 (offB (sampleBody F)) i (pairT (C1*K) (fullData s K a C1 C2 E x)))
      (inst2 (sampleBody F) i (sampleData s (C2*K) (a+C1) C2 E x)) two (unit s) :=
  GaussianCompactRiemannAdditivity.aligned_suffix_term_distance F i s a C1 C2 E K x h hi

theorem prefix_distance (F : PR 3) (s a C1 C2 E K x : PTm n) (h : Γ ⊢[PRAAx] positiveInput F a C1 C2 E K x) : Γ ⊢[PRAAx]
    distanceBounded (prefixPart F s K a C1 C2 E x) (quadrature F s (C1*K) a C1 E x) (C1*two) (E*unit s) :=
  GaussianCompactRiemannAdditivity.aligned_prefix_distance F s a C1 C2 E K x h

theorem suffix_distance (F : PR 3) (s a C1 C2 E K x : PTm n) (h : Γ ⊢[PRAAx] positiveInput F a C1 C2 E K x) : Γ ⊢[PRAAx]
    distanceBounded (suffixPart F s K a C1 C2 E x) (quadrature F s (C2*K) (a+C1) C2 E x) (C2*two) (E*unit s) :=
  GaussianCompactRiemannAdditivity.aligned_suffix_distance F s a C1 C2 E K x h

/-- Quantitative shared-step additivity of the actual stored compact
quadratures, from actual aligned-time sample comparison alone. -/
theorem positive_split (F : PR 3) (s a C1 C2 E K x : PTm n) (h : Γ ⊢[PRAAx] positiveInput F a C1 C2 E K x) : Γ ⊢[PRAAx]
    distanceBounded (quadrature F s ((C1+C2)*K) a (C1+C2) E x)
      (qadd (quadrature F s (C1*K) a C1 E x) (quadrature F s (C2*K) (a+C1) C2 E x)) (two*(C1+C2)) (E*unit s) :=
  GaussianCompactRiemannAdditivity.aligned_positive_split F s a C1 C2 E K x h

alias quadrature_congr := GaussianCompactRiemannName.quadrature_congr
alias quadrature_empty := GaussianCompactRiemannAdditivity.quadrature_empty
alias quadrature_canonical := GaussianCompactRiemannAdditivity.quadrature_canonical
alias zero_left_identity := GaussianCompactRiemannAdditivity.zero_left_identity
alias zero_right_identity := GaussianCompactRiemannAdditivity.zero_right_identity

def splitLaw (F : PR 3) (s a C1 C2 E K x : PTm n) : Fm PTm n :=
  distanceBounded (quadrature F s ((C1+C2)*K) a (C1+C2) E x)
    (qadd (quadrature F s (C1*K) a C1 E x) (quadrature F s (C2*K) (a+C1) C2 E x))
    (two*(C1+C2)) (E*unit s)
ipra_subst splitLaw

theorem split_transport (F : PR 3) (s a E K x C1 C2 D1 D2 : PTm n)
    (h1 : Γ ⊢[PRAAx] C1 ≐ D1) (h2 : Γ ⊢[PRAAx] C2 ≐ D2)
    (h : Γ ⊢[PRAAx] splitLaw F s a D1 D2 E K x) : Γ ⊢[PRAAx] splitLaw F s a C1 C2 E K x :=
  GaussianCompactRiemannAdditivity.split_transport F s a E K x C1 C2 D1 D2 h1 h2 h

alias distance_of_identity := GaussianCompactRiemannAdditivity.distance_of_identity

def input (F : PR 3) (a C1 C2 E K x : PTm n) : Fm PTm n :=
  le one a ⋏ (le one E ⋏ (le one K ⋏ alignedSamples F a (C1+C2) E x))
ipra_subst input

/-- Actual aligned-time splitting, allowing either width zero. -/
theorem shared_step_additivity (F : PR 3) (s a C1 C2 E K x : PTm n)
    (h : Γ ⊢[PRAAx] input F a C1 C2 E K x) : Γ ⊢[PRAAx] splitLaw F s a C1 C2 E K x := by
  apply GaussianCompactRiemannAdditivity.split_allowing_zero F s a C1 C2 E K x h.andE₂.andE₁
  refine .impI (.impI ?_)
  exact positive_split F s a C1 C2 E K x
    (.andI h.andE₁.wk.wk (.andI h.andE₂.andE₁.wk.wk (.andI h.andE₂.andE₂.andE₁.wk.wk
      (.andI Prf.hyp1 (.andI Prf.hyp0 h.andE₂.andE₂.andE₂.wk.wk)))))

theorem actual_aligned_time_zero_safe_split_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (input F (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      splitLaw F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) :=
  closeUniv 7 (.impI (shared_step_additivity F _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianCompactAlignedSplit

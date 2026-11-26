import IPRADerivations.Analysis.Integration.CompactGrids.Splits.GaussianCompactZeroWidth

/-!
# Shared-step compact quadrature splitting with zero widths

A zero width uses its genuine empty sum even though the width-scaled
count is zero. Both degenerate cases are literal canonical identities.
The positive case is exactly the existing metric split on the original
shared step, so differing evaluator encodings retain their two ordinary
observation errors. No output equality is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianCompactZeroSafeSplit

open_ipra
open GaussianCompactRiemannName (quadrature sampledModulus)
open GaussianRationalHorner (qadd qzero)
open GaussianRationalMetric (distanceBounded)
open GaussianCoefficientNameBounds (unit)

variable {n : ℕ} {Γ : List (Fm PTm n)}

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

def input (F : PR 3) (a C1 C2 E K L x : PTm n) : Fm PTm n :=
  le one a ⋏ (le one E ⋏ (le one K ⋏ sampledModulus F a (C1+C2) E L x))
ipra_subst input

/-- The existing genuine metric split, now allowing either width zero. -/
theorem shared_step_additivity (F : PR 3) (s a C1 C2 E K L x : PTm n)
    (h : Γ ⊢[PRAAx] input F a C1 C2 E K L x) : Γ ⊢[PRAAx] splitLaw F s a C1 C2 E K x := by
  apply GaussianCompactRiemannAdditivity.split_allowing_zero F s a C1 C2 E K x h.andE₂.andE₁
  refine .impI (.impI ?_)
  exact GaussianCompactRiemannAdditivity.shared_step_additivity F s a C1 C2 E K L x
    (.andI h.andE₁.wk.wk (.andI h.andE₂.andE₁.wk.wk (.andI h.andE₂.andE₂.andE₁.wk.wk
      (.andI Prf.hyp1 (.andI Prf.hyp0 h.andE₂.andE₂.andE₂.wk.wk)))))

theorem original_zero_count_quadrature_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (quadrature F (var 0) zero (var 1) (var 2) (var 3) (var 4) ≐ qzero) :=
  closeUniv 5 (quadrature_empty F _ _ _ _ _)

theorem original_zero_safe_shared_step_split_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input F (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      splitLaw F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 7)) :=
  closeUniv 8 (.impI (shared_step_additivity F _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianCompactZeroSafeSplit

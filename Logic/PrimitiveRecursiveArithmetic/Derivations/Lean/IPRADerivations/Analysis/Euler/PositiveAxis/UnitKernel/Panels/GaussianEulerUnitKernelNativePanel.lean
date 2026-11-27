import IPRADerivations.Analysis.Euler.PositiveAxis.UnitKernel.Compact.GaussianEulerUnitKernelCompactName

/-!
# Every proper native rational panel has an actual compact unit name

A rational panel is proper when its left numerator is positive and its
right numerator is strictly below the denominator. Its own denominator
is then a certified kernel margin. Every original compact source also
implies these two native endpoint conditions.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitKernelNativePanel

open_ipra
open GaussianEulerUnitKernelCompactName (source start_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def proper (a C E : PTm n) : Fm PTm n := le one a ⋏ lt (a+C) E

ipra_subst proper

theorem denominator_positive (a C E : PTm n) (h : Γ ⊢[PRAAx] proper a C E) : Γ ⊢[PRAAx] le one E :=
  le_trans h.andE₁ (le_trans (le_add_right a C) (le_of_lt h.andE₂))

theorem proper_from_source (z R B a C E G : PTm n) (h : Γ ⊢[PRAAx] source z R B a C E G) :
    Γ ⊢[PRAAx] proper a C E := by
  refine .andI (start_positive z R B a C E G h) (.orE (lt_or_le (a+C) E) Prf.hyp0 ?_)
  have left := add_le_add_right (G*(a+C)) h.andE₂.andE₁
  have narrower : Γ ⊢[PRAAx] lt (G*(a+C)) (G*E) := le_trans
    (le_congr (by ipra_ring) (by ipra_ring) left) h.andE₂.andE₂.andE₂
  have opposite := le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right G (Prf.hyp0 : _ :: Γ ⊢[PRAAx] le E (a+C)))
  exact .botE _ (lt_irrefl _ _ (le_trans narrower.wk opposite))

theorem source_at_denominator (z R B a C E : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianEulerUpperPowerCoefficients.source z R B)
    (h : Γ ⊢[PRAAx] proper a C E) : Γ ⊢[PRAAx] source z R B a C E E := by
  have e := denominator_positive a C E h
  have left : Γ ⊢[PRAAx] le E (E*a) :=
    le_congr (one_mul _) (mul_comm _ _) (mul_le_mul_right E h.andE₁)
  have right : Γ ⊢[PRAAx] le (E*(a+C)+E) (E*E) :=
    le_congr (by ipra_ring) (.eqRefl _) (mul_le_mul_right E (le_congr (succ_eq_add_one _) (.eqRefl _) h.andE₂))
  exact .andI (.andI hz.andE₁ (.andI e hz.andE₂)) (.andI e (.andI left right))

theorem actual_native_unit_panel_source_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((GaussianEulerUpperPowerCoefficients.source (var 0) (var 1) (var 2) ⋏ proper (var 3) (var 4) (var 5)) ⟶
      source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 5)) :=
  closeUniv 6 (.impI (source_at_denominator _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitKernelNativePanel

import IPRADerivations.Analysis.Names.Rates.Order.GaussianNamedRealOrderTransport

/-!
# Exact real-name order from dyadically close ordered comparisons

At the selected gap-removal clock, both approximating names can depend
on the clock. Their independent-radius costs must be fixed before it is
chosen. The finite comparison then gives the exact original order
allowance with no residual perturbation.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedCofinalOrder

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNamedInverseRate (independentRate rate_at rateNumerator rateDenominator)
open GaussianNamedPositiveExponentialOrder (realOrder real_order_at scalar_coordinate_distance)
open GaussianNamedRealOrderTransport (precision upperSlack remove_upper_slack)
open GaussianRationalHorner (positive_product)
open RationalValueBounds (upper upper_of_radius upper_triangle upper_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def cost (A B : PTm n) : PTm n := A+B+num 4

def clock (f g : PR 2) (p q x y A B : PTm n) : PTm n :=
  precision (fstT (ap2 f p x)) (fstT (ap2 g q y)) (unit p*unit q) (cost A B)

theorem observation_slack (f f' g' g : PR 2) (p q t x x' y' y A B : PTm n)
    (hl : Γ ⊢[PRAAx] independentRate f f' x x' A (unit t))
    (hr : Γ ⊢[PRAAx] independentRate g' g y' y B (unit t))
    (ho : Γ ⊢[PRAAx] realOrder f' g' x' y') :
    Γ ⊢[PRAAx] upperSlack (fstT (ap2 f p x)) (fstT (ap2 g q y)) (unit p+unit q) (unit p*unit q) (cost A B) t := by
  have ht := unit_positive (Γ := Γ) t
  have dL := GaussianNamedInverseRate.denominator_positive (unit t) p t ht
  have dR := GaussianNamedInverseRate.denominator_positive (unit t) t q ht
  have dM := positive_product _ _ ht ht
  have left := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ dL
    (rate_at f f' x x' A (unit t) p t hl))
  have right := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ dR
    (rate_at g' g y' y B (unit t) t q hr))
  have middle := real_order_at f' g' x' y' t t ho
  have joined := upper_triangle _ _ _ _ _ _ _ (upper_triangle _ _ _ _ _ _ _ left middle) right
  apply upper_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ dL dM) dR) joined
  exact le_of_eq_add (d := zero) (by unfold rateNumerator rateDenominator cost; ipra_ring)

theorem observation (f f' g' g : PR 2) (p q x x' y' y A B : PTm n)
    (hl : Γ ⊢[PRAAx] independentRate f f' x x' A (unit (clock f g p q x y A B)))
    (hr : Γ ⊢[PRAAx] independentRate g' g y' y B (unit (clock f g p q x y A B)))
    (ho : Γ ⊢[PRAAx] realOrder f' g' x' y') :
    Γ ⊢[PRAAx] upper (fstT (ap2 f p x)) (fstT (ap2 g q y)) (unit p+unit q) (unit p*unit q) :=
  remove_upper_slack _ _ _ _ (cost A B) (observation_slack f f' g' g p q _ x x' y' y A B hl hr ho)

theorem actual_named_cofinal_order_observation_closed (f f' g' g : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      ((independentRate f f' (var 2) (var 3) (var 6) (unit (clock f g (var 0) (var 1) (var 2) (var 5) (var 6) (var 7))) ⋏
        (independentRate g' g (var 4) (var 5) (var 7) (unit (clock f g (var 0) (var 1) (var 2) (var 5) (var 6) (var 7))) ⋏
          realOrder f' g' (var 3) (var 4))) ⟶
        upper (fstT (ap2 f (var 0) (var 2))) (fstT (ap2 g (var 1) (var 5)))
          (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 8 (.impI (observation f f' g' g _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianNamedCofinalOrder

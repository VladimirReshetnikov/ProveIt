import IPRADerivations.Analysis.Exponential.PositiveAxis.GaussianNamedPositiveExponentialOrder
import IPRADerivations.Analysis.Inequalities.GapRemoval

/-!
# Finite transport of real order between actual Gaussian names

One original rational comparison at a computed dyadic precision removes
the auxiliary error. Cross-equivalent observations therefore transport
the exact independent real-order relation, preserving the two requested
observation errors. This is an order consumer, without any exponential
order law as a premise.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianNamedRealOrderTransport

open_ipra
open GaussianNamedPositiveExponentialOrder (realOrder real_order_at positiveSamples positive_at scalar_coordinate_distance)
open GaussianNameEquivalence (crossEquivalent)
open GaussianCoefficientNameBounds (unit unit_positive)
open RationalValueBounds (upper upper_of_radius upper_triangle crossLeft)
open RationalSupMetric (denominatorOf)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def precision (a b B C : PTm n) : PTm n := C*B*denominatorOf a*denominatorOf b
def upperSlack (a b A B C t : PTm n) : Fm PTm n := upper a b (A*unit t+C*B) (B*unit t)
ipra_subst precision
ipra_subst upperSlack

/-- Only this single actual finite comparison is needed, with no
positive tolerance or denominator premise. -/
theorem remove_upper_slack (a b A B C : PTm n)
    (h : Γ ⊢[PRAAx] upperSlack a b A B C (precision a b B C)) : Γ ⊢[PRAAx] upper a b A B := by
  have clear : Γ ⊢[PRAAx]
      le ((B*crossLeft a b)*pw two (precision a b B C))
        ((B*crossLeft b a+A*denominatorOf a*denominatorOf b)*pw two (precision a b B C)+precision a b B C) :=
    le_congr (by unfold unit; ipra_ring)
      (by unfold unit precision; ipra_ring) h
  exact GapRemoval.gap clear

theorem transport_budget (f f' g' g : PR 2) (x x' y' y p q t : PTm n)
    (hf : Γ ⊢[PRAAx] crossEquivalent f f' x x') (hg : Γ ⊢[PRAAx] crossEquivalent g' g y' y)
    (hOrder : Γ ⊢[PRAAx] realOrder f' g' x' y') : Γ ⊢[PRAAx]
    upperSlack (fstT (ap2 f p x)) (fstT (ap2 g q y)) (unit p+unit q) (unit p*unit q) (num 4) t := by
  have dl := GaussianNameEquivalence.cross_at f f' x x' p t hf
  have dr := GaussianNameEquivalence.cross_at g' g y' y t q hg
  have left := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _
    (GaussianRationalHorner.positive_product _ _ (unit_positive p) (unit_positive t)) dl)
  have right := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _
    (GaussianRationalHorner.positive_product _ _ (unit_positive t) (unit_positive q)) dr)
  have middle := real_order_at f' g' x' y' t t hOrder
  have joined := upper_triangle _ _ _ _ _ _ _ (upper_triangle _ _ _ _ _ _ _ left middle) right
  apply RationalValueBounds.upper_mono _ _ _ _ _ _
    (GaussianRationalHorner.positive_product _ _
      (GaussianRationalHorner.positive_product _ _
        (GaussianRationalHorner.positive_product _ _ (unit_positive p) (unit_positive t))
        (GaussianRationalHorner.positive_product _ _ (unit_positive t) (unit_positive t)))
      (GaussianRationalHorner.positive_product _ _ (unit_positive t) (unit_positive q))) joined
  exact le_of_eq_add (d := zero) (by ipra_ring)

theorem transport_at (f f' g' g : PR 2) (x x' y' y p q : PTm n)
    (hf : Γ ⊢[PRAAx] crossEquivalent f f' x x') (hg : Γ ⊢[PRAAx] crossEquivalent g' g y' y)
    (hOrder : Γ ⊢[PRAAx] realOrder f' g' x' y') : Γ ⊢[PRAAx]
    upper (fstT (ap2 f p x)) (fstT (ap2 g q y)) (unit p+unit q) (unit p*unit q) :=
  remove_upper_slack _ _ _ _ (num 4) (transport_budget f f' g' g x x' y' y p q
    (precision (fstT (ap2 f p x)) (fstT (ap2 g q y)) (unit p*unit q) (num 4)) hf hg hOrder)

theorem transport (f f' g' g : PR 2) (x x' y' y : PTm n)
    (hf : Γ ⊢[PRAAx] crossEquivalent f f' x x') (hg : Γ ⊢[PRAAx] crossEquivalent g' g y' y)
    (hOrder : Γ ⊢[PRAAx] realOrder f' g' x' y') : Γ ⊢[PRAAx] realOrder f g x y := by
  refine .allI (.allI ?_)
  have fs := GaussianNameEquivalence.shift_crossEquivalent (GaussianNameEquivalence.shift_crossEquivalent hf)
  have gs := GaussianNameEquivalence.shift_crossEquivalent (GaussianNameEquivalence.shift_crossEquivalent hg)
  have os : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] realOrder f' g' (Syn.shift (Syn.shift x')) (Syn.shift (Syn.shift y')) :=
    by simpa [Fm.shift,Syn.shift] using hOrder.shift.shift
  simpa only [realOrder,Syn.shift] using transport_at f f' g' g (Syn.shift (Syn.shift x))
    (Syn.shift (Syn.shift x')) (Syn.shift (Syn.shift y')) (Syn.shift (Syn.shift y)) (var 1) (var 0) fs gs os

theorem original_finite_real_upper_slack_removal_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (upperSlack (var 0) (var 1) (var 2) (var 3) (var 4) (precision (var 0) (var 1) (var 3) (var 4)) ⟶
      upper (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 5 (.impI (remove_upper_slack _ _ _ _ _ Prf.hyp0))

theorem original_named_real_order_transport_closed (f f' g' g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (crossEquivalent f f' (var 0) (var 1) ⟶ crossEquivalent g' g (var 2) (var 3) ⟶
      realOrder f' g' (var 1) (var 2) ⟶ realOrder f g (var 0) (var 3)) :=
  closeUniv 4 (.impI (.impI (.impI (transport f f' g' g _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianNamedRealOrderTransport

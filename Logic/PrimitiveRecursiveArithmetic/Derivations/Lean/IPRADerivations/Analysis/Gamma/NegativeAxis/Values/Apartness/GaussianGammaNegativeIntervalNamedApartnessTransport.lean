import IPRADerivations.Analysis.Gamma.NegativeAxis.Values.Apartness.GaussianGammaNegativeIntervalNamedApartness
import IPRADerivations.Analysis.Names.Rates.Order.GaussianNamedApartnessTransport
import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.GaussianNamedDifferenceQuotientProperness

/-!
# Transport of apartness from the negative-interval critical point
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedApartnessTransport

open_ipra
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaNegativeCriticalLocation (fractionLocationF fraction_location_regular)
open GaussianGammaNegativeIntervalNamedApartness (apart)
open GaussianNameEquivalence (crossEquivalent cross_refl)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem transport (f g : PR 2) (h N x y : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (ha : Γ ⊢[PRAAx] apart f h N x) (eq : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] apart g (succ h) N y := by
  have root := fraction_location_regular (Γ := Γ) N
  have names := GaussianNamedDifferenceQuotientProperness.difference_proper fractionLocationF fractionLocationF f g N N x y
    root root hf hg (cross_refl _ _ root) eq
  exact GaussianNamedApartnessTransport.transport _ _ h _ _ ha names

theorem actual_negative_interval_named_apartness_transport_closed (f g : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      ((pointCN f (var 2) ⋏ (pointCN g (var 3) ⋏ (apart f (var 0) (var 1) (var 2) ⋏
         crossEquivalent f g (var 2) (var 3)))) ⟶ apart g (succ (var 0)) (var 1) (var 3)) :=
  closeUniv 4 (.impI (transport f g _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedApartnessTransport

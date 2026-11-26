import IPRADerivations.Analysis.Gamma.Names.PositiveAxis.GaussianNamedGammaSecondCrossingProduct
import IPRADerivations.Analysis.Names.GoldenRatio.GaussianNamedGoldenRatioRightHalfPlane

/-!
# The second Gamma crossing at the positive golden ratio

On the positive real named domain, with apartness of the backward
argument from zero, the named pole-free backward Gamma value equals
the original forward Gamma value precisely at the independent
positive golden-ratio name. The backward provider is identified with
the literal pole-free evaluator in GaussianNamedGammaBackwardIdentification.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedGammaSecondCrossing

open_ipra
open GaussianNamedGammaSecondCrossingProduct (source crossing crossing_implies_product product_implies_crossing)
open GaussianNamedGoldenRatioProduct (product_implies_quadratic quadratic_implies_product)
open GaussianNameEquivalence (crossEquivalent)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def equalsGoldenRatio (f : PR 2) (x : PTm n) : Fm PTm n :=
  crossEquivalent f GaussianNamedGoldenRatio.nameF x GaussianNamedGoldenRatio.nameData

theorem crossing_implies_golden_ratio (f : PR 2) (x A a : PTm n)
    (hs : Γ ⊢[PRAAx] source f x A a) (h : Γ ⊢[PRAAx] crossing f x A a) :
    Γ ⊢[PRAAx] equalsGoldenRatio f x :=
  GaussianNamedGoldenRatioRightHalfPlane.root_unique f x A hs.andE₁.andE₁ hs.andE₂
    (product_implies_quadratic f x hs.andE₁.andE₁.andE₁
      (crossing_implies_product f x A a hs h))

theorem golden_ratio_implies_crossing (f : PR 2) (x A a : PTm n)
    (hs : Γ ⊢[PRAAx] source f x A a) (h : Γ ⊢[PRAAx] equalsGoldenRatio f x) :
    Γ ⊢[PRAAx] crossing f x A a :=
  product_implies_crossing f x A a hs
    (quadratic_implies_product f x hs.andE₁.andE₁.andE₁
      (GaussianNamedGoldenRatioUniqueness.equal_root_is_quadratic f x hs.andE₁.andE₁.andE₁ h))

theorem actual_original_named_Gamma_second_crossing_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source f (var 0) (var 1) (var 2) ⟶
        Fm.iff (crossing f (var 0) (var 1) (var 2)) (equalsGoldenRatio f (var 0))) :=
  closeUniv 3 (.impI (Prf.iffI
    (.impI (crossing_implies_golden_ratio f _ _ _ Prf.hyp1 Prf.hyp0))
    (.impI (golden_ratio_implies_crossing f _ _ _ Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianNamedGammaSecondCrossing

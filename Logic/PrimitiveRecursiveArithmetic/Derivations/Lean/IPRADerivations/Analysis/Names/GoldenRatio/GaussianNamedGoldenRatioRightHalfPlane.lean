import IPRADerivations.Analysis.Names.RightHalfPlane.GaussianNamedPositiveLateLogSource
import IPRADerivations.Analysis.Names.GoldenRatio.GaussianNamedGoldenRatioUniqueness
import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianNamedGammaHalfShift

/-!
# Golden-ratio uniqueness for certified positive real names

Only the late observations need to be positive. Their canonical fractions
form an equivalent name on a compact positive domain. The original
quadratic transfers to that name by the checked addition and
multiplication equivalences.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianNamedGoldenRatioRightHalfPlane

open_ipra
open GaussianNamedGoldenRatioUniqueness (quadratic)
open GaussianNamedGoldenRatio (onePoint)
open GaussianNamedPositiveLateLogSource (retimedF retimedData)
open GaussianNameArithmetic (multiplyF multiplyData addF addData)
open GaussianSignedNameExponentialOrder (realSamples)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans cross_refl)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianNamedGammaHalfShift (add_cross)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem quadratic_transport (f g : PR 2) (x y : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) (hq : Γ ⊢[PRAAx] quadratic f x) :
    Γ ⊢[PRAAx] quadratic g y := by
  let a := onePoint (n := n)
  have constant := constant_regular (Γ := Γ) a
  have backwards := cross_symm f g x y he
  have square := multiply_cross g f g f y x y x hg hf hg hf backwards backwards
  have sum := add_cross f g constantF constantF x y a a hf hg constant constant he (cross_refl _ _ constant)
  exact cross_trans (multiplyF g g) (multiplyF f f) (addF g constantF)
    (multiplyData g g y y) (multiplyData f f x x) (addData y a) square
    (cross_trans (multiplyF f f) (addF f constantF) (addF g constantF) _ _ _ hq sum)

theorem root_unique (f : PR 2) (x A : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianNamedRightHalfPlane.source f x A)
    (hr : Γ ⊢[PRAAx] realSamples f x)
    (hq : Γ ⊢[PRAAx] quadratic f x) :
    Γ ⊢[PRAAx] crossEquivalent f GaussianNamedGoldenRatio.nameF x GaussianNamedGoldenRatio.nameData := by
  let F := retimedF f
  let y := retimedData x A
  have reg := hs.andE₁
  have eq := GaussianNamedPositiveLateLogSource.original_cross f x A reg
  have retimed := GaussianNamedPositiveLateLogSource.positive_source f x A hs hr
  have qr := quadratic_transport f F x y reg retimed.andE₁ eq hq
  have root := GaussianNamedGoldenRatioUniqueness.root_unique F y (two*A) (GaussianNameBounds.U f x) retimed qr
  exact cross_trans f F GaussianNamedGoldenRatio.nameF x y GaussianNamedGoldenRatio.nameData eq root

theorem actual_original_positive_real_named_golden_ratio_unique_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      ((GaussianNamedRightHalfPlane.source f (var 0) (var 1) ⋏ realSamples f (var 0)) ⟶
        Fm.iff (quadratic f (var 0))
          (crossEquivalent f GaussianNamedGoldenRatio.nameF (var 0) GaussianNamedGoldenRatio.nameData)) :=
  closeUniv 2 (.impI (.andI (.impI (root_unique f _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0))
    (.impI (GaussianNamedGoldenRatioUniqueness.equal_root_is_quadratic f _ Prf.hyp1.andE₁.andE₁ Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianNamedGoldenRatioRightHalfPlane

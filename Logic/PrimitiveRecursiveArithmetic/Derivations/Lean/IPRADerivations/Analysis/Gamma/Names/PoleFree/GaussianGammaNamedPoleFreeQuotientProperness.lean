import IPRADerivations.Analysis.Gamma.Names.PoleFree.GaussianGammaNamedHalfPlanePoleFreeQuotient
import IPRADerivations.Analysis.Gamma.Names.PoleFree.GaussianGammaNamedPoleFreeIncrementSource

/-!
# Base-input replacement for the original pole-free Gamma quotient

Adding the same increment preserves equivalence of the upper arguments.
The general Gamma properness theorem applies to the two endpoint pairs
with their separate pole certificates. The quotient retains the original
increment and its certified reciprocal.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaNamedPoleFreeQuotientProperness

open_ipra
open GaussianGammaNamedPoleFree (source name_regular)
open GaussianNameArithmetic (add_equivalent)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_to_diagonal)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "SF" => GaussianNamedGammaSmallIncrementInput.sumF
local notation "sd" => GaussianNamedGammaSmallIncrementInput.sumData
local notation "P" => GaussianGammaNamedPoleFree.nameF
local notation "pd" => GaussianGammaNamedPoleFree.data
local notation "QF" => GaussianGammaNamedHalfPlanePoleFreeQuotient.nameF
local notation "qd" => GaussianGammaNamedHalfPlanePoleFreeQuotient.data

theorem proper (f g K : PR 2) (x y z R E S D R' E' S' D' a : PTm n)
    (hLower : Γ ⊢[PRAAx] source f x R E)
    (hUpper : Γ ⊢[PRAAx] source (SF f K) (sd x z) S D)
    (hLower' : Γ ⊢[PRAAx] source g y R' E')
    (hUpper' : Γ ⊢[PRAAx] source (SF g K) (sd y z) S' D')
    (hK : Γ ⊢[PRAAx] GaussianNameReciprocal.input K a z) (he : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] crossEquivalent (QF f K) (QF g K) (qd f K x z R E S D a) (qd g K y z R' E' S' D' a) := by
  let u := SF f K
  let v := SF g K
  let X := sd x z
  let Y := sd y z
  have upperArgument : Γ ⊢[PRAAx] crossEquivalent u v X Y :=
    add_equivalent f g K K x y z z hLower.andE₁ hLower'.andE₁ hK.andE₁ hK.andE₁
      (cross_to_diagonal _ _ _ _ he) (cross_to_diagonal _ _ _ _ (cross_refl K z hK.andE₁))
  have lowerGamma := GaussianGammaNamedPoleFreeProperness.proper f g x y R R' E E' hLower hLower' he
  have upperGamma := GaussianGammaNamedPoleFreeProperness.proper u v X Y S S' D D' hUpper hUpper' upperArgument
  exact GaussianNamedIncrementDifferenceQuotientProperness.proper (P u) (P v) (P f) (P g) K
    (pd X S D) (pd Y S' D') (pd x R E) (pd y R' E') z a
    (name_regular u X S D hUpper) (name_regular v Y S' D' hUpper')
    (name_regular f x R E hLower) (name_regular g y R' E' hLower') hK upperGamma lowerGamma

theorem small_increment_proper (f g K : PR 2) (x y z R E R' E' a : PTm n)
    (hLower : Γ ⊢[PRAAx] source f x R E) (hLower' : Γ ⊢[PRAAx] source g y R' E')
    (hK : Γ ⊢[PRAAx] GaussianNameReciprocal.input K a z)
    (hSmall : Γ ⊢[PRAAx] GaussianExponentialSmallPerturbation.smallSamples K z one (two*E))
    (hSmall' : Γ ⊢[PRAAx] GaussianExponentialSmallPerturbation.smallSamples K z one (two*E'))
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) : Γ ⊢[PRAAx]
    crossEquivalent (QF f K) (QF g K) (qd f K x z R E (ConciseIPRA.PTm.succ R) (two*E) a)
      (qd g K y z R' E' (ConciseIPRA.PTm.succ R') (two*E') a) :=
  proper f g K _ _ _ _ _ _ _ _ _ _ _ _ hLower
    (GaussianGammaNamedPoleFreeIncrementSource.original_source f K x z R E hLower hK.andE₁ hSmall) hLower'
    (GaussianGammaNamedPoleFreeIncrementSource.original_source g K y z R' E' hLower' hK.andE₁ hSmall') hK he

theorem actual_named_pole_free_Gamma_quotient_properness_closed (f g K : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 12
      (((source f (var 0) (var 3) (var 4) ⋏ source (SF f K) (sd (var 0) (var 2)) (var 5) (var 6)) ⋏
        ((source g (var 1) (var 7) (var 8) ⋏ source (SF g K) (sd (var 1) (var 2)) (var 9) (var 10)) ⋏
          (GaussianNameReciprocal.input K (var 11) (var 2) ⋏ crossEquivalent f g (var 0) (var 1)))) ⟶
        crossEquivalent (QF f K) (QF g K) (qd f K (var 0) (var 2) (var 3) (var 4) (var 5) (var 6) (var 11))
          (qd g K (var 1) (var 2) (var 7) (var 8) (var 9) (var 10) (var 11))) :=
  closeUniv 12 (.impI (proper f g K _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁.andE₁ Prf.hyp0.andE₁.andE₂
    Prf.hyp0.andE₂.andE₁.andE₁ Prf.hyp0.andE₂.andE₁.andE₂ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaNamedPoleFreeQuotientProperness

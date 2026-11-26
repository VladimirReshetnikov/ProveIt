import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaDigammaNative
import IPRADerivations.Analysis.Gamma.Names.Input.GaussianGammaInputProperness
import IPRADerivations.Analysis.Gamma.Names.PoleFree.GaussianGammaRadiusOverlap

/-!
# Rescaling positive rational inputs of the original digamma name

Multiplying a numerator and denominator by the same positive natural
preserves the native digamma value. Both sides use their own original
reciprocal Gamma and logarithmic Euler integral names.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaRescaling

open_ipra
open ComplexLogarithmRemainder (scale)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaDigammaNative (nameF data derivativeData reciprocalData derivative_regular reciprocal_regular)
open GaussianGammaEncodingRescaling (fraction_rescale original_C7_rescale rescaled_source)
open GaussianGammaFiniteValueProperness (fraction_equal source_equal)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans)
open GaussianRationalHorner (ofGaussian positive_product)
open GaussianRootAlgebra (equal equal_of_values equal_symm re_scale im_scale)
open GaussianStirlingGammaLogarithm (source arg gamma_source euler_real_source)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "PF" => GaussianGammaC7Name.nameF
local notation "IF" => GaussianEulerLogarithmicImproperName.nameF

private theorem scaled_arg (a E : PTm n) : Γ ⊢[PRAAx] equal (scale E (arg a)) (arg (E*a)) := by
  apply equal_of_values <;>
    simp only [arg, re_scale, im_scale] <;>
    ipra_simps <;> ring

private theorem reciprocal_rescaling (a b E : PTm n) (h : Γ ⊢[PRAAx] source a b)
    (hE : Γ ⊢[PRAAx] le one E) (h' : Γ ⊢[PRAAx] source (E*a) (E*b)) :
    Γ ⊢[PRAAx] crossEquivalent PF PF (reciprocalData (E*a) (E*b)) (reciprocalData a b) := by
  have base := (gamma_source a b h).andE₁
  have scaled := rescaled_source (arg a) a b E base hE
  have e := scaled_arg (Γ := Γ) a E
  have converted := source_equal _ _ _ _ scaled e
  have overlap := GaussianGammaRadiusOverlap.original_P_overlap (arg (E*a)) (E*a) a (E*b)
    (gamma_source (E*a) (E*b) h').andE₁ converted
  have native := GaussianGammaInputProperness.original_C7_proper _ _ _ _ scaled e
  exact cross_trans _ _ _ _ _ _ overlap
    (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ native) (original_C7_rescale _ _ _ _ base hE))

theorem original_rescaling (a b E : PTm n) (h : Γ ⊢[PRAAx] source a b)
    (hE : Γ ⊢[PRAAx] le one E) :
    Γ ⊢[PRAAx] crossEquivalent nameF nameF (data (E*a) (E*b)) (data a b) := by
  have ha := positive_product _ _ hE h.andE₁
  have hb := positive_product _ _ hE h.andE₂
  have s : Γ ⊢[PRAAx] source (E*a) (E*b) := .andI ha hb
  have fractions : Γ ⊢[PRAAx] ofGaussian (arg (E*a)) (E*b) ≐ ofGaussian (arg a) b :=
    (fraction_equal _ _ _ hb (equal_symm (scaled_arg a E))).eqTrans (fraction_rescale _ _ _ h.andE₂ hE)
  have integral := GaussianEulerLogarithmicImproperInputProperness.original_improper_proper
    one (arg (E*a)) (arg a) (E*a) a (E*b) b (E*b) b
    (.andI (euler_real_source _ _ s).andE₁ (.andI (euler_real_source _ _ h).andE₁ fractions))
  exact multiply_cross PF PF IF IF _ _ _ _ (reciprocal_regular _ _ s) (reciprocal_regular _ _ h)
    (derivative_regular _ _ s) (derivative_regular _ _ h) (reciprocal_rescaling a b E h hE s) integral

theorem actual_original_positive_rational_digamma_rescaling_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      ((source (var 0) (var 1) ⋏ le one (var 2)) ⟶
        crossEquivalent nameF nameF (data (var 2*var 0) (var 2*var 1)) (data (var 0) (var 1))) :=
  closeUniv 3 (.impI (original_rescaling _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaRescaling

import IPRADerivations.Analysis.Stirling.GammaLogarithm.GaussianStirlingGammaLogarithm
import IPRADerivations.Analysis.Logarithm.PositiveAxis.NamedValues.GaussianNamedPositiveLogarithmScale
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Recurrence.GaussianGammaShift
import IPRADerivations.Analysis.Gamma.Names.PoleFree.GaussianGammaRadiusOverlap
import IPRADerivations.Analysis.Euler.HarmonicLogarithms.GaussianHarmonicLogarithmName

/-!
# The original logarithmic Gamma recurrence on positive rationals

The positive native Gamma source certifies the incremented numerator.
The Gamma recurrence, encoding properness and the radius overlap give
the exact multiplicative law. Applying the positive named logarithms
gives the additive law on the actual log-Gamma and harmonic log names.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingGammaLogShift

open_ipra
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaEulerHeadLower (translated)
open GaussianGammaEulerHeadShift (shifted)
open GaussianGammaInputProperness (gamma_source_equal original_Gamma_proper)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianNameArithmetic (addF addData add_equivalent multiplyF multiplyData)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans cross_to_diagonal)
open GaussianPositiveRationalLogarithm (logF fraction)
open GaussianRootAlgebra (equal equal_of_values equal_symm re_add im_add re_scale im_scale re_one im_one)
open GaussianStirlingGammaLogarithm (arg source gammaData gamma_source gamma_source_at_radius source_shift
  gamma_regular gammaRetimedF gammaRetimedData gamma_retimed_cross log_input log_gamma_regular logGammaF logGammaData)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "H" => GaussianHarmonicLogarithmName.nameF
local notation "hd" => GaussianHarmonicLogarithmName.data
local notation "gd" => GaussianGammaReciprocalInverse.gammaData

theorem native_increment (a b : PTm n) : Γ ⊢[PRAAx] equal (shifted (arg a) b) (arg (a+b)) := by
  apply equal_of_values <;> simp only [arg,shifted,translated,re_add,im_add,re_scale,im_scale,re_one,im_one] <;>
    ipra_simps <;> ring

theorem gamma_increment (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] crossEquivalent gammaF (multiplyF constantF gammaF) (gammaData (a+b) b)
      (multiplyData constantF gammaF (fraction a b) (gammaData a b)) := by
  let z := arg a
  let w := arg (a+b)
  let v := shifted z b
  have hSucc := source_shift a b h
  have hSmall : Γ ⊢[PRAAx] le (a+b) ((a+one)*b) := by ipra_le 𝔞 a*sl h.andE₂
  have ws := gamma_source_at_radius (a+b) b (a+one) hSucc (le_add_left one a) hSmall
  have same := native_increment (Γ := Γ) a b
  have vs := gamma_source_equal w v (a+one) b one b ws (equal_symm same)
  have hs : Γ ⊢[PRAAx] GaussianGammaShift.input z a b one b one b := .andI (gamma_source a b h) vs.andE₂
  have law := GaussianGammaShift.C21_Gamma_shift z a b one b one b hs
  have codes := original_Gamma_proper w v (a+one) b one b ws (equal_symm same)
  have radius := GaussianGammaRadiusOverlap.original_Gamma_overlap w (a+b) (a+one) b one b one b
    (gamma_source (a+b) b hSucc) ws
  exact cross_trans _ _ _ _ _ _ radius (cross_trans _ _ _ _ _ _ codes law)

set_option maxHeartbeats 1600000 in
theorem log_gamma_increment (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] crossEquivalent logGammaF (addF H logGammaF) (logGammaData (a+b) b)
      (addData (hd a b) (logGammaData a b)) := by
  let x := gammaData a b
  let v := gammaData (a+b) b
  let c := fraction a b
  let y := gammaRetimedData a b
  let w := gammaRetimedData (a+b) b
  let E := gammaRetimedF
  let X := GaussianPositiveRationalLogarithm.data a b
  let Z := logGammaData a b
  have hs := source_shift a b h
  have fx := log_input a b h
  have fv := log_input (a+b) b hs
  have hc := constant_regular (Γ := Γ) c
  have scale := GaussianGammaAdjacentCutoff.multiply_cross constantF constantF E gammaF c c y x hc hc fx.andE₁
    (gamma_regular a b h) (cross_refl _ _ hc) (cross_symm _ _ _ _ (gamma_retimed_cross a b h))
  have eq := cross_trans _ _ _ _ _ _ scale (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (gamma_increment a b h))
    (gamma_retimed_cross (a+b) b hs))
  have logs := GaussianNamedPositiveLogarithmScale.logarithm_scale E E a b y w _ _ _ _ h fx fv eq
  have hz := log_gamma_regular a b h
  have summed := add_equivalent logF H logGammaF logGammaF X (hd a b) Z Z
    (GaussianPositiveRationalLogarithm.name_regular a b h) (GaussianHarmonicLogarithmName.name_regular a b h)
    hz hz (cross_to_diagonal logF H X (hd a b) (GaussianHarmonicLogarithmName.cross_original a b h))
    (GaussianNameEquivalence.diagonal_refl logGammaF Z)
  exact cross_trans _ _ _ _ _ _ logs summed

set_option maxHeartbeats 1600000 in
theorem actual_positive_rational_log_Gamma_increment_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (source (var 0) (var 1) ⟶ crossEquivalent logGammaF (addF H logGammaF) (logGammaData (var 0+var 1) (var 1))
      (addData (hd (var 0) (var 1)) (logGammaData (var 0) (var 1)))) :=
  closeUniv 2 (.impI (log_gamma_increment _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianStirlingGammaLogShift

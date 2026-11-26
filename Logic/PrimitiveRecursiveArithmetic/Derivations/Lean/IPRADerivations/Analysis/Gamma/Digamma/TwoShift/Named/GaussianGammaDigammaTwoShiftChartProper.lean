import IPRADerivations.Analysis.Gamma.Digamma.TwoShift.GaussianGammaDigammaTwoShiftBinding
import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianNamedGammaHalfShift
import IPRADerivations.Analysis.Gamma.CriticalPoints.PositiveMinimum.GaussianGammaMinimumLogProperness
import IPRADerivations.Analysis.Logarithm.PositiveAxis.GaussianPositiveRationalLogarithmProperness
import IPRADerivations.Analysis.Stirling.Telescoping.GaussianStirlingRationalTelescopers

/-! The original normalized ratio logarithm respects changes of positive
rational encodings of all three arguments. -/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftChartProper

open_ipra
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaDigammaTwoShiftBinding
open GaussianNameEquivalence (crossEquivalent cross_to_diagonal cross_symm cross_trans)
open GaussianNameRingLaws (negativeF negativeData negative_fast negative_equivalent)
open GaussianPositiveRationalLogarithm (logF fraction)
open GaussianStirlingGammaLogarithm (source logGammaF logGammaData log_gamma_regular)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "H" => GaussianHarmonicLogarithmName.nameF
local notation "HD" => GaussianHarmonicLogarithmName.data
local notation "D" => GaussianPositiveRationalLogarithm.data

theorem original_log_cross (a b c d A B C D' : PTm n)
    (h : Γ ⊢[PRAAx] source a b ⋏ (source c b ⋏ source d b))
    (h' : Γ ⊢[PRAAx] source A B ⋏ (source C B ⋏ source D' B))
    (ea : Γ ⊢[PRAAx] a*B ≐ b*A) (ec : Γ ⊢[PRAAx] c*B ≐ b*C) (ed : Γ ⊢[PRAAx] d*B ≐ b*D') :
    Γ ⊢[PRAAx] crossEquivalent quotientLogF quotientLogF (quotientLogData a b c d) (quotientLogData A B C D') := by
  let α := coefficient b c d
  let β := coefficient B C D'
  let x := powerLogData a b c d
  let y := powerLogData A B C D'
  let u := denominatorLogData a b c d
  let v := denominatorLogData A B C D'
  have ab := h.andE₁
  have cd := h.andE₂.andE₁
  have dd := h.andE₂.andE₂
  have AB := h'.andE₁
  have CD := h'.andE₂.andE₁
  have DD := h'.andE₂.andE₂
  have hb := ab.andE₂
  have hB := AB.andE₂
  have equal_frac (p q : PTm n) (e : Γ ⊢[PRAAx] p*B ≐ b*q) :
      Γ ⊢[PRAAx] fraction p b ≐ fraction q B :=
    GaussianStirlingRationalTelescopers.fraction_same p b q B hb hB (e.eqTrans (mul_comm b q))
  have ce := equal_frac c C ec
  have de := equal_frac d D' ed
  have coef := GaussianRationalSyntheticDivision.qsub_congr ce de
  have logEq := GaussianPositiveRationalLogarithmProperness.original_logarithm_proper a b A B ab AB ea
  have harmonic : Γ ⊢[PRAAx] crossEquivalent H H (HD a b) (HD A B) :=
    cross_trans H logF H (HD a b) (D a b) (HD A B)
      (cross_symm _ _ _ _ (GaussianHarmonicLogarithmName.cross_original a b ab))
      (cross_trans logF logF H (D a b) (D A B) (HD A B) logEq
        (GaussianHarmonicLogarithmName.cross_original A B AB))
  have power : Γ ⊢[PRAAx] crossEquivalent powerLogF powerLogF x y :=
    GaussianGammaAdjacentCutoff.multiply_cross constantF constantF H H α β (HD a b) (HD A B)
      (constant_regular α) (constant_regular β) (GaussianHarmonicLogarithmName.name_regular a b ab)
      (GaussianHarmonicLogarithmName.name_regular A B AB)
      (GaussianSignedNameExponentialOrder.constant_equal_cross α β coef) harmonic
  have gammaC := GaussianGammaMinimumLogProperness.log_gamma_cross c b C B cd CD ce
  have gammaD := GaussianGammaMinimumLogProperness.log_gamma_cross d b D' B dd DD de
  have denom : Γ ⊢[PRAAx] crossEquivalent denominatorLogF denominatorLogF u v :=
    GaussianNamedGammaHalfShift.add_cross logGammaF logGammaF powerLogF powerLogF (logGammaData d b) (logGammaData D' B) x y
      (log_gamma_regular d b dd) (log_gamma_regular D' B DD) (power_log_regular a b c d ab) (power_log_regular A B C D' AB)
      gammaD power
  have hu := denominator_log_regular a b c d ab dd
  have hv := denominator_log_regular A B C D' AB DD
  have neg := negative_equivalent denominatorLogF denominatorLogF u v hu hv (cross_to_diagonal _ _ _ _ denom)
  exact GaussianNamedGammaHalfShift.add_cross logGammaF logGammaF (negativeF denominatorLogF) (negativeF denominatorLogF)
    (logGammaData c b) (logGammaData C B) (negativeData u) (negativeData v)
    (log_gamma_regular c b cd) (log_gamma_regular C B CD) (negative_fast _ _ hu) (negative_fast _ _ hv) gammaC neg

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftChartProper

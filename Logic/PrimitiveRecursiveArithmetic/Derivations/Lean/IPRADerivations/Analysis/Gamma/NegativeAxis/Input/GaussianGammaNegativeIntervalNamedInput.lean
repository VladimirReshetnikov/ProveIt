import IPRADerivations.Analysis.Gamma.CriticalPoints.NegativeIntervals.GaussianGammaNegativeCriticalLocationInterior
import IPRADerivations.Analysis.Gamma.NegativeAxis.CriticalPoints.Chords.GaussianGammaNegativeIntervalChordInverse
import IPRADerivations.Analysis.Euler.PositiveAxis.UnitTime.Named.GaussianNamedEulerUnitTime

/-!
# Named inputs on a negative Gamma pole interval

An offset name uses the existing unit-interval input judgment. Its
canonical fraction at each observation has the same certified separation
from both poles. The computed critical point satisfies this judgment
at its original mesh margin.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedInput

open_ipra
open GaussianGammaNegativeCriticalCorrection (guard)
open GaussianGammaNegativeCriticalEndpoints (mesh mesh_minimum rightNumerator)
open GaussianGammaNegativeCriticalGrid (denominator)
open GaussianGammaNegativeCriticalLocation
  (fractionLocation fractionLocationF fraction_location_at fraction_location_regular lower)
open GaussianGammaNegativeCriticalLocationInterior (offset_lower_at offset_upper_at)
open GaussianGammaNegativeIntervalChordInverse (poleMargin)
open GaussianNamedEulerUnitTime (source source_at)
open GaussianSignedNameExponentialOrder (realSamples)
open GaussianStirlingMultiplicativeBoundsOrder (fraction_real_part)
open GaussianUnitIntervalInputDecoding (lowerPoint upperPoint decoded_source)
open RationalArgmin (rationalLE_congr)
open RationalGaussianEmbedding (axis axis_congr)
open RationalValueBounds (upper_of_order)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def sampleNumerator (f : PR 2) (p x : PTm n) : PTm n :=
  GaussianUnitIntervalInputDecoding.numerator (ap2 f p x)

def sampleDenominator (f : PR 2) (p x : PTm n) : PTm n :=
  GaussianUnitIntervalInputDecoding.denominator (ap2 f p x)

ipra_subst sampleNumerator

ipra_subst sampleDenominator

theorem frozen_guard (f : PR 2) (p x E : PTm n) (hs : Γ ⊢[PRAAx] source f x E) :
    Γ ⊢[PRAAx] guard (sampleNumerator f p x) (sampleDenominator f p x) :=
  (GaussianNamedEulerUnitTime.encoded_source f p x E hs).andE₁

theorem frozen_margin (f : PR 2) (p x E : PTm n) (hs : Γ ⊢[PRAAx] source f x E) :
    Γ ⊢[PRAAx] poleMargin (sampleNumerator f p x) (sampleDenominator f p x) E := by
  let a := sampleNumerator f p x
  let b := sampleDenominator f p x
  have h := GaussianNamedEulerUnitTime.encoded_source f p x E hs
  have e := natEq (eq_add_of_le (le_of_lt (frozen_guard f p x E hs).andE₂))
  refine .andI h.andE₂.andE₂.andE₁ ?_
  have top : Γ ⊢[PRAAx] le (E*a+b) (E*b) := h.andE₂.andE₂.andE₂
  ipra_le sl top with -𝔞(E)*e

theorem root_real_at (p N : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (ap2 fractionLocationF p N) ⋏ axis (ap2 fractionLocationF p N) := by
  have hb := GaussianGammaNegativeCriticalLocation.denominator_positive (Γ := Γ) p N
  have eq := fraction_location_at (Γ := Γ) p N
  exact .andI
    (GaussianRationalHorner.canonical_congr eq (GaussianRationalHorner.ofGaussian_canonical _ _ hb))
    (axis_congr eq.eqSymm (GaussianStirlingNames.fraction_axis (lower p N) (denominator p N) hb))

theorem root_sample (p N : PTm n) : Γ ⊢[PRAAx]
    GaussianUnitIntervalInputDecoding.source (ap2 fractionLocationF p N) (mesh N) := by
  let m := mesh N
  let q := ap2 fractionLocationF p N
  have hm : Γ ⊢[PRAAx] le one m := le_trans (by ipra_le 7) (mesh_minimum N)
  have eq := congrFst (fraction_location_at (Γ := Γ) p N)
  have lo := rationalLE_congr (fraction_real_part one m hm) eq.eqSymm (offset_lower_at p N)
  have hi := rationalLE_congr eq.eqSymm (fraction_real_part (rightNumerator N) m hm) (offset_upper_at p N)
  exact .andI (root_real_at p N).andE₂ (.andI hm (.andI
    (upper_of_order (lowerPoint m) (fstT q) zero one lo)
    (upper_of_order (fstT q) (upperPoint m) zero one hi)))

theorem root_source (N : PTm n) : Γ ⊢[PRAAx] source fractionLocationF N (mesh N) := by
  refine .andI (fraction_location_regular N) (.allI ?_)
  simpa only [GaussianNamedEulerUnitKernel.admissibleSamples,Syn.shift,
    GaussianGammaNegativeCriticalEndpoints.subst_mesh] using
    root_sample (Γ := Γ.map Fm.shift) (var 0) (Syn.shift N)

theorem root_real (N : PTm n) : Γ ⊢[PRAAx] realSamples fractionLocationF N := by
  refine .allI ?_
  simpa only [realSamples,Syn.shift] using
    root_real_at (Γ := Γ.map Fm.shift) (var 0) (Syn.shift N)

theorem actual_negative_Gamma_critical_offset_input_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
      (source fractionLocationF (var 0) (mesh (var 0)) ⋏ realSamples fractionLocationF (var 0)) :=
  closeUniv 1 (.andI (root_source _) (root_real _))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedInput

import IPRADerivations.Analysis.Barnes.Taylor.CenteredCharts.FiniteApproximants.GaussianBarnesCanonicalFiniteCentralChart
import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.GaussianBarnesCanonicalTaylorCoefficientChart
import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.FixedCoefficients.GaussianBarnesCanonicalFixedTaylorDerivativeUniformConvergence

/-!
# Chart independence of the original Barnes factorial Taylor names

The original finite scalar and the retained Taylor coefficients agree
between charts. Combine their regular names at a common finite cutoff.
A disk-uniform cutoff then transfers equality to the original cofinal
factorial Taylor name, at independently chosen observation clocks.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorDerivativeChart

open_ipra
open ComplexLogarithmRemainder (scale)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameEquivalence (crossEquivalent cross_refl)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedUniformRateClosure (equivalent family)
open GaussianRationalHorner (ofGaussian)
open GaussianRationalNaturalScale (naturalPoint)
open LeanProofs.IPRA.Analysis.Products (fact)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "C" => GaussianBarnesCanonicalFixedTaylorCoefficientName.nameF
local notation "cd" => GaussianBarnesCanonicalFixedTaylorCoefficientName.data
local notation "S" => GaussianBarnesCanonicalFiniteCentralExponential.finiteNameF
local notation "sd" => GaussianBarnesCanonicalFiniteCentralExponential.finiteData
local notation "K" => GaussianBarnesCanonicalFixedTaylorDerivativeName.coefficientF
local notation "kd" => GaussianBarnesCanonicalFixedTaylorDerivativeName.coefficientData
local notation "F" => GaussianBarnesCanonicalFixedTaylorDerivativeName.nameF
local notation "fd" => GaussianBarnesCanonicalFixedTaylorDerivativeName.data
local notation "L" => GaussianBarnesCanonicalTaylorProductDerivativeName.nameF
local notation "ld" => GaussianBarnesCanonicalTaylorProductDerivativeName.data

theorem fixed_cross (z w R B D r M e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source w R D) (he : Γ ⊢[PRAAx] le e (previous M))
    (hq : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] crossEquivalent F F (fd z R B r M e) (fd w R D r M e) := by
  let a := naturalPoint (fact e)
  have ha := constant_regular (Γ := Γ) a
  have coefficient := multiply_cross constantF constantF C C a a (cd z R B r M e) (cd w R D r M e)
    ha ha (GaussianBarnesCanonicalFixedTaylorCoefficientName.regular z R B r M e hz he)
    (GaussianBarnesCanonicalFixedTaylorCoefficientName.regular w R D r M e hw he) (cross_refl _ _ ha)
    (GaussianBarnesCanonicalTaylorCoefficientChart.fixed_cross z w R B D r M e hz hw he hq)
  exact multiply_cross S S K K (sd z R B r) (sd w R D r) (kd z R B r M e) (kd w R D r M e)
    (GaussianBarnesCanonicalFiniteCentralExponential.finite_regular z R B r hz)
    (GaussianBarnesCanonicalFiniteCentralExponential.finite_regular w R D r hw)
    (GaussianBarnesCanonicalFixedTaylorDerivativeName.coefficient_regular z R B r M e hz he)
    (GaussianBarnesCanonicalFixedTaylorDerivativeName.coefficient_regular w R D r M e hw he)
    (GaussianBarnesCanonicalFiniteCentralChart.proper z w R B D r hz hw hq) coefficient

private theorem cofinal_rate (p z w R B D M e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source w R D) (he : Γ ⊢[PRAAx] le e (previous M))
    (hq : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) : Γ ⊢[PRAAx]
    independentRate L L (ld z R B M e) (ld w R D M e) (one+one) (unit p) := by
  let r := GaussianBarnesCanonicalFixedTaylorDerivativeUniformConvergence.cutoff p R M e
  have first := GaussianBarnesCanonicalFixedTaylorDerivativeUniformConvergence.late_rate p z R B r M e hz he (le_refl r)
  have second := GaussianBarnesCanonicalFixedTaylorDerivativeUniformConvergence.late_rate p w R D r M e hw he (le_refl r)
  have hwL := GaussianBarnesCanonicalTaylorProductDerivativeName.regular w R D M e hw he
  have aligned := GaussianNamedRateTransport.transport L F L F (ld w R D M e) (fd w R D r M e) (ld w R D M e)
    (fd z R B r M e) one (unit p) (unit_positive p) second (cross_refl _ _ hwL) (fixed_cross z w R B D r M e hz hw he hq)
  exact GaussianNamedRateComposition.same_denominator _ _ _ _ _ _ one (unit p) one (unit_positive p) first
    (GaussianNamedRateComposition.symmetric _ _ _ _ _ _ (unit_positive p) aligned)

theorem cofinal_cross (z w R B D M e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source w R D) (he : Γ ⊢[PRAAx] le e (previous M))
    (hq : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] crossEquivalent L L (ld z R B M e) (ld w R D M e) := by
  apply equivalent _ _ _ _ (one+one)
  refine .allI ?_
  let sh (t : PTm n) := Syn.shift t
  have hz' : Γ.map Fm.shift ⊢[PRAAx] source (sh z) (sh R) (sh B) := by simpa [sh,Fm.shift,Syn.shift] using hz.shift
  have hw' : Γ.map Fm.shift ⊢[PRAAx] source (sh w) (sh R) (sh D) := by simpa [sh,Fm.shift,Syn.shift] using hw.shift
  have he' : Γ.map Fm.shift ⊢[PRAAx] le (sh e) (previous (sh M)) := by simpa [sh,Fm.shift,Syn.shift] using he.shift
  have hq' : Γ.map Fm.shift ⊢[PRAAx] ofGaussian (sh z) (sh B) ≐ ofGaussian (sh w) (sh D) := by
    simpa [sh,Fm.shift,Syn.shift] using hq.shift
  simpa [family,sh,Syn.shift,one,GaussianBarnesCanonicalTaylorProductDerivativeName.data,
    GaussianBarnesCanonicalTaylorProductDerivativeName.coefficientData] using
    cofinal_rate (var 0) (sh z) (sh w) (sh R) (sh B) (sh D) (sh M) (sh e) hz' hw' he' hq'

theorem actual_Barnes_fixed_factorial_Taylor_chart_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (let z := var 0
     let w := var 1
     let R := var 2
     let B := var 3
     let D := var 4
     let r := var 5
     let M := var 6
     let e := var 7
     (source z R B ⋏ source w R D) ⟶ (le e (previous M) ⋏ ofGaussian z B ≐ ofGaussian w D) ⟶
       crossEquivalent F F (fd z R B r M e) (fd w R D r M e)) :=
  closeUniv 8 (.impI (.impI (fixed_cross _ _ _ _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0.andE₁ Prf.hyp0.andE₂)))

theorem actual_Barnes_cofinal_factorial_Taylor_chart_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (let z := var 0
     let w := var 1
     let R := var 2
     let B := var 3
     let D := var 4
     let M := var 5
     let e := var 6
     (source z R B ⋏ source w R D) ⟶ (le e (previous M) ⋏ ofGaussian z B ≐ ofGaussian w D) ⟶
       crossEquivalent L L (ld z R B M e) (ld w R D M e)) :=
  closeUniv 7 (.impI (.impI (cofinal_cross _ _ _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0.andE₁ Prf.hyp0.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorDerivativeChart

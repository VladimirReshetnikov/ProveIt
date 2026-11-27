import IPRADerivations.Analysis.Barnes.Taylor.CenteredCharts.FiniteApproximants.GaussianBarnesCanonicalFiniteCentralDiskBound
import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalFiniteWeightedTaylorValue
import IPRADerivations.Analysis.Barnes.Taylor.CenteredCharts.GaussianBarnesCanonicalHeadUniformMass

/-!
# Weighted Taylor comparison of the original finite Barnes name on a disk

Use the disk caps for the original weighted centered polynomial and
finite central scalar. The finite name, stored Taylor polynomial, and
displacement remain those of the original finite comparison.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteWeightedTaylorUniformValue

open_ipra
open ComplexLogarithmRemainder (add bounded)
open GaussianBarnesCanonicalFiniteWeightedTaylorValue (nameF data denominator numerator_with_caps rate_with_caps)
open GaussianBarnesCanonicalHeadUniformMass (headCap weighted_head_mass)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianBarnesCanonicalWeightedTaylorBallSource (input stepDivisor admission)
open GaussianGammaCanonicalExponent (gammaF)
open GaussianNameBounds (U)
open GaussianNamedInverseRate (independentRate)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "V" => GaussianBarnesCanonicalValue.prefixF
local notation "literal" => GaussianBarnesCanonicalProduct.literalData

def numerator (p R B H M : PTm n) : PTm n :=
  numerator_with_caps p R B H M (headCap R) (GaussianBarnesCanonicalFiniteCentralDiskBound.cap R)

@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (p R B H M : PTm n) :
    Syn.subst σ (numerator p R B H M) =
      numerator (Syn.subst σ p) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ H) (Syn.subst σ M) := by
  have radius_subst (x : PTm n) : Syn.subst σ (GaussianBarnesCanonicalDiskBound.prefactorRadius x) =
      GaussianBarnesCanonicalDiskBound.prefactorRadius (Syn.subst σ x) := by
    let radius {l : ℕ} (y : PTm l) : PTm l :=
      (two*(y*U GaussianStirlingConstant.nameF (GaussianStirlingConstant.nameData zero))+two)+
        (two*(y+(y*y)*(one+U gammaF zero))+two)
    change Syn.subst σ (radius x) = radius (Syn.subst σ x)
    simp [radius,one,two,GaussianStirlingConstant.nameData]
  simp [numerator,numerator_with_caps,GaussianBarnesCanonicalFiniteCentralDiskBound.cap,
    GaussianBarnesCanonicalCentralUniformBound.prefixCap,GaussianBarnesCanonicalCentralUniformBound.prefixArgumentCap,
    GaussianBarnesCanonicalCentralUniformBound.correctionCap,radius_subst,
    GaussianBarnesCanonicalFactor.exponentRadius,GaussianBarnesCanonicalFiniteExponentTaylor.scheduledNumerator,
    GaussianBarnesCanonicalFiniteExponentTaylor.scheduledDenominator,GaussianBarnesCanonicalCorrectedMercator.numerator,
    GaussianBarnesCanonicalCorrectedMercatorCofinal.analyticDenominator,GaussianBarnesCanonicalCorrectedMercator.scaleDenominator,
    GaussianBarnesCanonicalTaylorRecomposition.error,GaussianBarnesCanonicalTaylorRecomposition.capGain,
    GaussianNamedRateComposition.leadingNumerator,one,two,pw]

theorem rate (p z h R B H r M : PTm n) (hs : Γ ⊢[PRAAx] input z h R B H M) : Γ ⊢[PRAAx]
    independentRate V nameF (literal (add z h) R B (initial R+r)) (data p z h R B H r M)
      (numerator p R B H M) (denominator p R B M) := by
  have hz := hs.andE₁.andE₁
  exact rate_with_caps p z h R B H r M (headCap R) (GaussianBarnesCanonicalFiniteCentralDiskBound.cap R) hs
    (weighted_head_mass z R B (num 4) hz (zero_lt_succ _))
    (GaussianBarnesCanonicalFiniteCentralDiskBound.samples z R B r hz)

theorem shared_rate (p z h R B H r M : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hh : Γ ⊢[PRAAx] bounded h H) (hsmall : Γ ⊢[PRAAx] le (stepDivisor R*H) B) : Γ ⊢[PRAAx]
    independentRate V nameF (literal (add z h) (R+one) B (initial (R+one)+r)) (data p z h (R+one) B H r M)
      (numerator p (R+one) B H M) (denominator p (R+one) B M) :=
  rate p z h (R+one) B H r M (admission z h R B H M hz hh hsmall)

theorem actual_Barnes_finite_weighted_Taylor_uniform_value_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (let p := var 0
     let z := var 1
     let h := var 2
     let R := var 3
     let B := var 4
     let H := var 5
     let r := var 6
     let M := var 7
     input z h R B H M ⟶
       independentRate V nameF (literal (add z h) R B (initial R+r)) (data p z h R B H r M)
         (numerator p R B H M) (denominator p R B M)) :=
  closeUniv 8 (.impI (rate (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteWeightedTaylorUniformValue

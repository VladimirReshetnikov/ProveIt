import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.FirstDerivative.Cofinal.GaussianBarnesCanonicalPositiveLogarithmIncrement
import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.FirstDerivative.Cofinal.GaussianBarnesCanonicalPositiveRelativeLogarithmDerivative
import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.DerivativeRates.GaussianNativeDerivativeQuotientRate

/-! The actual difference quotient of the positive Barnes logarithm converges to its first
logarithmic derivative. The endpoints can use independent admitted disk bounds. -/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPositiveLogarithmDerivative

open_ipra
open Common
open ComplexLogarithmRemainder (im normSq eval_im_code)
open GaussianBarnesCanonicalThirdDerivativePositiveMargin (step shifted_center)
open GaussianBarnesCanonicalThirdLogarithmRows (center)
open GaussianNameEquivalence (cross_refl cross_symm)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (positive_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "L" => GaussianBarnesCanonicalPositiveLogarithm.nameF
local notation "ld" => GaussianBarnesCanonicalPositiveLogarithm.data
local notation "F" => GaussianBarnesCanonicalPositiveFirstLogarithm.nameF
local notation "fd" => GaussianBarnesCanonicalPositiveFirstLogarithm.data
local notation "J" => GaussianBarnesCanonicalRelativeLogIncrement.nameF
local notation "jd" => GaussianBarnesCanonicalRelativeLogIncrement.data
local notation "RRate" => GaussianBarnesCanonicalPositiveRelativeLogarithmDerivative.rate
local notation "source" => GaussianBarnesCanonicalPositiveRelativeLogarithmDerivative.source
local notation "gain" => GaussianBarnesCanonicalPositiveRelativeLogarithmDerivative.gain
local notation "numerator" => GaussianBarnesCanonicalPositiveRelativeLogarithmDerivative.numerator
local notation "linearF" => GaussianBarnesCanonicalPositiveRelativeLogarithmDerivative.linearF
local notation "linearData" => GaussianBarnesCanonicalPositiveRelativeLogarithmDerivative.linearData
local notation "Diff" => GaussianNamedDifference.nameF
local notation "dd" => GaussianNamedDifference.data

def quotientF : PR 2 := GaussianNamedDifferenceQuotient.nameF L L

def quotientData (A C B R S : PTm n) : PTm n :=
  GaussianNamedDifferenceQuotient.data L L (ld C B S) (ld A B R) (step A C) B

def quotientNumerator (R H K : PTm n) : PTm n := (two*gain R K)*H

theorem rate (A C B R S H K : PTm n) (h : Γ ⊢[PRAAx] source A C B R H K)
    (hs : Γ ⊢[PRAAx] GaussianBarnesCanonicalPositiveLogarithm.source C B S) :
    Γ ⊢[PRAAx] independentRate (Diff L L) linearF (dd (ld C B S) (ld A B R))
      (linearData A C B R) (numerator R H K) (B*B) := by
  let z := center A B
  let v := step A C
  let d := linearData A C B R
  have hB := h.andE₁.andE₁
  have ha : Γ ⊢[PRAAx] GaussianBarnesCanonicalPositiveLogarithm.source A B R :=
    .andI h.andE₁.andE₂.andE₁ h.andE₂.andE₁.andE₁
  have axis : Γ ⊢[PRAAx] ZT.eq (im v) (ZT.ofNat zero) := ZT.derive (by simp only [v,step,eval_im_code])
  have e := GaussianBarnesCanonicalPositiveLogarithmIncrement.difference_cross A C B R S v
    (.andI (.andI ha hs) (.andI h.andE₂.andE₁ (.andI axis (shifted_center A C B))))
  let c := GaussianRationalHorner.ofGaussian v B
  have reg := GaussianNameArithmetic.multiply_fast GaussianGammaCanonicalExponent.constantF F c (fd A B R)
    (GaussianGammaCanonicalExponent.constant_regular c) (GaussianBarnesCanonicalPositiveFirstLogarithm.regular A B R ha.andE₂)
  exact GaussianNamedRateTransport.transport J linearF (Diff L L) linearF (jd z v R B) d
    (dd (ld C B S) (ld A B R)) d _ _ (positive_product B B hB hB) (RRate A C B R H K h) e
    (cross_refl linearF d reg)

theorem quotient_rate (A C B R S K : PTm n)
    (h : Γ ⊢[PRAAx] source A C B R (GaussianL1.norm1 (step A C)) K)
    (hs : Γ ⊢[PRAAx] GaussianBarnesCanonicalPositiveLogarithm.source C B S)
    (hn : Γ ⊢[PRAAx] le one (normSq (step A C))) :
    Γ ⊢[PRAAx] independentRate quotientF F (quotientData A C B R S) (fd A B R)
      (quotientNumerator R (GaussianL1.norm1 (step A C)) K) B := by
  let H := GaussianL1.norm1 (step A C)
  have hB := h.andE₁.andE₁
  have hD := positive_product B B hB hB
  have hp := GaussianNativeDerivativeQuotientRate.norm1_positive (step A C) hn
  have ha : Γ ⊢[PRAAx] GaussianBarnesCanonicalPositiveLogarithm.source A B R :=
    .andI h.andE₁.andE₂.andE₁ h.andE₂.andE₁.andE₁
  have raw : Γ ⊢[PRAAx] independentRate quotientF F (quotientData A C B R S) (fd A B R)
      ((two*B)*numerator R H K) (H*(B*B)) :=
    GaussianNativeDerivativeQuotientRate.rate L L F (ld C B S) (ld A B R) (fd A B R) (step A C) B
      (numerator R H K) (B*B) (GaussianBarnesCanonicalPositiveLogarithm.regular C B S hs)
      (GaussianBarnesCanonicalPositiveLogarithm.regular A B R ha)
      (GaussianBarnesCanonicalPositiveFirstLogarithm.regular A B R ha.andE₂)
      (.andI hB hn) hD (rate A C B R S H K h hs)
  have fit : Γ ⊢[PRAAx] le (((two*B)*numerator R H K)*B) ((quotientNumerator R H K)*(H*(B*B))) :=
    le_of_eq_add (d := zero) (by
      dsimp only [GaussianBarnesCanonicalPositiveRelativeLogarithmDerivative.numerator,quotientNumerator]
      ipra_ring)
  exact GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ (positive_product _ _ hp hD) hB fit raw

theorem actual_Barnes_positive_logarithm_first_derivative_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (let A := var 0
       let C := var 1
       let B := var 2
       let R := var 3
       let S := var 4
       let K := var 5
       let H := GaussianL1.norm1 (step A C)
       (source A C B R H K ⋏ (GaussianBarnesCanonicalPositiveLogarithm.source C B S ⋏
          le one (normSq (step A C)))) ⟶
         independentRate quotientF F (quotientData A C B R S) (fd A B R) (quotientNumerator R H K) B) :=
  closeUniv 6 (.impI (quotient_rate _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPositiveLogarithmDerivative

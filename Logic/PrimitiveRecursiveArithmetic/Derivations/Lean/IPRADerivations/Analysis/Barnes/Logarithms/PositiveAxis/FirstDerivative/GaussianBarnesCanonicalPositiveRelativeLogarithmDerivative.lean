import IPRADerivations.Analysis.Names.FiniteOperations.Sums.GaussianNamedSumDifference
import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.FirstDerivative.GaussianBarnesCanonicalPositiveHeadLogarithmDerivative
import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.FirstDerivative.GaussianBarnesCanonicalPositiveHeadLogarithmIncrement
import IPRADerivations.Analysis.Barnes.Prefactors.GaussianBarnesCanonicalPrefactorExponentEstimate
import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.Cofinal.GaussianBarnesCanonicalDerivativeTailBinding
import IPRADerivations.Analysis.Barnes.Taylor.RelativeExpansions.GaussianBarnesCanonicalRelativeExponentTaylor

/-! On positive rational steps the existing relative logarithm has the existing full first
logarithmic derivative, with a quadratic error and independent observation precision. -/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPositiveRelativeLogarithmDerivative

open_ipra
open Common
open GaussianBarnesCanonicalThirdLogarithmRows (center)
open GaussianBarnesCanonicalThirdDerivativePositiveMargin (step)
open GaussianBarnesCanonicalLogSchedule (initial initial_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaDigammaTwoShiftNamedSize (constant_product)
open GaussianNamedGammaHalfShift (add_cross constant_sum)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (add_associative distributive)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (ofGaussian qadd qmul positive_product)
open GaussianRationalMetric (qsub)

variable {n : ℕ} {Γ : List (Fm PTm n)}

open GaussianBarnesCanonicalRelativeLogIncrement (nameF data prefactorF prefactorData correctionF correctionData
  headF headData prefixF prefixData tailF tailData)

local notation "C₀" => constantF
local notation "E" => GaussianBarnesCanonicalPrefactorInverse.exponentF
local notation "J" => GaussianBarnesCanonicalHeadRelativeLog.nameF
local notation "D" => GaussianBarnesCanonicalDerivativeCofinal.nameF
local notation "F" => GaussianBarnesCanonicalPositiveFirstLogarithm.nameF
local notation "fd" => GaussianBarnesCanonicalPositiveFirstLogarithm.data
local notation "T" => GaussianBarnesCanonicalDerivativeTail.value
local notation "ld" => GaussianBarnesCanonicalLogCofinal.data

def source (A C B R H K : PTm n) : Fm PTm n :=
  GaussianBarnesCanonicalThirdDerivativePositiveMargin.source A C B H K ⋏
    (GaussianBarnesCanonicalRelativeLogIncrement.source (center A B) (step A C) R B ⋏
      GaussianBarnesCanonicalDerivativeTailBinding.input (center A B) (step A C) R B H)

def linearF : PR 2 := multiplyF C₀ F

def linearData (A C B R : PTm n) : PTm n :=
  multiplyData C₀ F (ofGaussian (step A C) B) (fd A B R)

def gain (R K : PTm n) : PTm n :=
  (GaussianBarnesCanonicalPrefactorExponentEstimate.quadraticErrorGain +
    (initial R*(two*(K*K))+initial R)) + (num 3*R+num 342)

def numerator (R H K : PTm n) : PTm n := gain R K*(H*H)

private theorem add_same_rate (f g u v : PR 2) (x y a b P Q B : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (h₁ : Γ ⊢[PRAAx] independentRate f u x a P B)
    (h₂ : Γ ⊢[PRAAx] independentRate g v y b Q B) :
    Γ ⊢[PRAAx] independentRate (addF f g) (addF u v) (addData x y) (addData a b) (P+Q) B := by
  have hBB := positive_product B B hB hB
  let M := GaussianNamedRateComposition.leadingNumerator P B Q B
  let den := GaussianNamedRateComposition.leadingDenominator B B
  have fit : Γ ⊢[PRAAx] le (M*B) ((P+Q)*den) := le_of_eq_add (d := zero)
    (by dsimp only [M,den,GaussianNamedRateComposition.leadingNumerator,
      GaussianNamedRateComposition.leadingDenominator]; ipra_ring)
  exact GaussianNamedRateRadius.weaken _ _ _ _ M den (P+Q) B hBB hB fit
    (GaussianNamedAddRate.independent_rate _ _ _ _ _ _ _ _ _ _ _ _ hB hB h₁ h₂)

private theorem prefactor_rate (z h B H : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hh : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded h H) :
    Γ ⊢[PRAAx] independentRate prefactorF (multiplyF C₀ E)
      (prefactorData z h B) (multiplyData C₀ E (ofGaussian h B)
        (GaussianBarnesCanonicalPrefactorExponentDerivative.derivativeData z B))
      (GaussianBarnesCanonicalPrefactorExponentEstimate.quadraticErrorGain*(H*H)) (B*B) := by
  open GaussianBarnesCanonicalPrefactorExponentDerivative in
  have e : Γ ⊢[PRAAx] GaussianBarnesCanonicalRelativeExponentTaylor.prefactorQuadratic z h B ≐ incrementData z h B := by
    ipra_congr (exponentOf (var 0) (var 1) : PTm 2) with
      [.eqRefl _, (GaussianBarnesCanonicalRelativeExponentTaylor.square_expansion z h B hB).eqSymm]
      using [GaussianBarnesCanonicalRelativeExponentTaylor.prefactorQuadratic,incrementData]
  let x := GaussianBarnesCanonicalPrefactorExponentDerivative.incrementData z h B
  let y := GaussianBarnesCanonicalPrefactorExponentDerivative.linearData z h B
  let v := multiplyData C₀ E (ofGaussian h B) (GaussianBarnesCanonicalPrefactorExponentDerivative.derivativeData z B)
  have ep := GaussianGammaCompactCutoffAlignment.cross_data_congr prefactorF E _ _ _ x (.eqRefl _) e
    (GaussianBarnesCanonicalRelativeExponentTaylor.prefactor_cross z h B hB)
  have raw := GaussianBarnesCanonicalPrefactorExponentEstimate.rate z h B H hB hh
  have out := GaussianNamedRateTransport.transport E E prefactorF (multiplyF C₀ E) x y
    (prefactorData z h B) v _ _ (positive_product B B hB hB) raw ep
    (GaussianBarnesCanonicalPrefactorExponentDerivative.linear_factor z h B hB)
  exact GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ _ _ (by ipra_ring) (.eqRefl _) out

private theorem correction_rate (z h B N H : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hh : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded h H) :
    Γ ⊢[PRAAx] independentRate correctionF C₀ (correctionData z h B N)
      (GaussianBarnesCanonicalHeadCorrectionDerivative.linear z h B N) (N*(H*H)) (B*B) := by
  let c := GaussianBarnesCanonicalCorrectionShift.total (ComplexLogarithmRemainder.add z h) B N
  let a := GaussianBarnesCanonicalCorrectionShift.total z B N
  let x := qsub c a
  let y := GaussianBarnesCanonicalHeadCorrectionDerivative.linear z h B N
  have hD := positive_product B B hB hB
  have core : Γ ⊢[PRAAx] GaussianRationalMetric.distanceBounded x y (N*(H*H)) (B*B) :=
    GaussianRationalDistanceOrder.distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (GaussianBarnesCanonicalHeadCorrectionDerivative.quadratic_bound z h B N H hB hh)
  exact GaussianNamedRateTransport.transport C₀ C₀ correctionF C₀ x y (correctionData z h B N) y
    _ _ hD (GaussianNamedAddRate.constant_rate x y _ _ hD core)
    (GaussianNamedSumDifference.constant_difference c a x (.eqRefl _)) (cross_refl _ _ (constant_regular y))

private theorem reorganize (f g : PR 2) (s x a b t : PTm n)
    (hx : Γ ⊢[PRAAx] pointCN f x) (ht : Γ ⊢[PRAAx] pointCN g t) :
    let P := multiplyF C₀ f
    let Q := multiplyF C₀ g
    let p := multiplyData C₀ f s x
    let q := multiplyData C₀ g s t
    Γ ⊢[PRAAx] crossEquivalent
      (multiplyF C₀ (addF f (addF C₀ g))) (addF (addF P (addF C₀ C₀)) Q)
      (multiplyData C₀ (addF f (addF C₀ g)) s (addData x (addData (qadd a b) t)))
      (addData (addData p (addData (qmul s a) (qmul s b))) q) := by
  let S := addF C₀ g
  let P := multiplyF C₀ f
  let Q := multiplyF C₀ g
  let P₀ := multiplyF C₀ C₀
  let x₀ := qadd a b
  let u := multiplyData C₀ f s x
  let v := multiplyData C₀ C₀ s x₀
  let w := multiplyData C₀ g s t
  let d := addData (qmul s a) (qmul s b)
  have hs := constant_regular (Γ := Γ) s
  have hc := constant_regular (Γ := Γ) x₀
  have hu := multiply_fast C₀ f s x hs hx
  have hv := multiply_fast C₀ C₀ s x₀ hs hc
  have hw := multiply_fast C₀ g s t hs ht
  have hd := add_fast (Γ := Γ) C₀ C₀ _ _ (constant_regular (qmul s a)) (constant_regular (qmul s b))
  have κ : Γ ⊢[PRAAx] crossEquivalent P₀ (addF C₀ C₀) v d := by
    have he := GaussianRationalCoefficientScaling.qmul_add (Γ := Γ) s a b
    exact cross_trans _ _ _ _ _ _ (constant_product s x₀ _ he)
      (cross_symm _ _ _ _ (constant_sum (qmul s a) (qmul s b) _ (.eqRefl _)))
  have e₁ := distributive C₀ f S s x (addData x₀ t) hs hx (add_fast _ _ _ _ hc ht)
  have e₂ := add_cross P P (multiplyF C₀ S) (addF P₀ Q)
    u u (multiplyData C₀ S s (addData x₀ t)) (addData v w)
    hu hu (multiply_fast _ _ _ _ hs (add_fast _ _ _ _ hc ht)) (add_fast _ _ _ _ hv hw)
    (cross_refl _ _ hu) (distributive C₀ C₀ g s x₀ t hs hc ht)
  have inner := add_cross P₀ (addF C₀ C₀) Q Q v d w w hv hd hw hw κ (cross_refl _ _ hw)
  have e₃ := add_cross P P (addF P₀ Q) (addF (addF C₀ C₀) Q) u u (addData v w) (addData d w)
    hu hu (add_fast _ _ _ _ hv hw) (add_fast _ _ _ _ hd hw) (cross_refl _ _ hu) inner
  exact cross_trans _ _ _ _ _ _ e₁ (cross_trans _ _ _ _ _ _ e₂
    (cross_trans _ _ _ _ _ _ e₃ (cross_symm _ _ _ _ (add_associative P (addF C₀ C₀) Q u d w hu hd hw))))

theorem rate (A C B R H K : PTm n) (h : Γ ⊢[PRAAx] source A C B R H K) :
    Γ ⊢[PRAAx] independentRate nameF linearF (data (center A B) (step A C) R B)
      (linearData A C B R) (numerator R H K) (B*B) := by
  let z := center A B
  let v := step A C
  let N := initial R
  let W := B*B
  let d := ofGaussian v B
  let x := GaussianBarnesCanonicalPositiveFirstLogarithm.prefactorData A B
  let a := GaussianBarnesCanonicalPositiveFirstLogarithmKept.value z B N
  let b := GaussianBarnesCanonicalHeadCorrectionDerivative.slope z B N
  let t := ld z R B
  let P := multiplyF C₀ E
  let Q := multiplyF C₀ D
  let p := multiplyData C₀ E d x
  let q := multiplyData C₀ D d t
  let g₁ := GaussianBarnesCanonicalPrefactorExponentEstimate.quadraticErrorGain*(H*H)
  let g₂ := N*GaussianBarnesCanonicalPositiveHeadLogarithmRowDerivative.numerator K H
  let g₃ := N*(H*H)
  let g₄ := GaussianBarnesCanonicalDerivativeInterval.errorNumerator R H
  have hB := h.andE₁.andE₁
  have ha := h.andE₁.andE₂.andE₁
  have hc := h.andE₁.andE₂.andE₂.andE₁
  have hK := h.andE₁.andE₂.andE₂.andE₂.andE₁
  have hM := h.andE₁.andE₂.andE₂.andE₂.andE₂.andE₁
  have hh := h.andE₁.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂
  have hW := positive_product B B hB hB
  have hz := h.andE₂.andE₁.andE₁
  have hj := h.andE₂.andE₁.andE₂.andE₂
  have r₁ : Γ ⊢[PRAAx] independentRate prefactorF P (prefactorData z v B) p g₁ W :=
    prefactor_rate z v B H hB hh
  have r₂ : Γ ⊢[PRAAx] independentRate J C₀ (GaussianBarnesCanonicalHeadRelativeLog.data z v B N)
      (qmul d a) g₂ W := by
    have raw := GaussianBarnesCanonicalPositiveHeadLogarithmDerivative.rate A C B H K N h.andE₁
    have e := GaussianBarnesCanonicalPositiveHeadLogarithmIncrement.difference_cross A C B N ha hc hB hj
    exact GaussianNamedRateTransport.transport _ _ _ _ _ _ _ _ _ _ hW raw
      (cross_symm _ _ _ _ e) (cross_refl _ _ (constant_regular (qmul d a)))
  have r₃ : Γ ⊢[PRAAx] independentRate correctionF C₀ (correctionData z v B N) (qmul d b) g₃ W :=
    correction_rate z v B N H hB hh
  have r₄ : Γ ⊢[PRAAx] independentRate tailF Q (tailData z v R B) q g₄ W := by
    have wide : Γ ⊢[PRAAx] le (g₄*W) (g₄*(W*N)) :=
      le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul (le_refl (g₄*W)) (initial_positive R))
    exact GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ (positive_product W N hW (initial_positive R)) hW wide
      (GaussianBarnesCanonicalDerivativeTailBinding.rate z v R B H h.andE₂.andE₂)
  have r₂₃ := add_same_rate J correctionF C₀ C₀ _ _ (qmul d a) (qmul d b) g₂ g₃ W hW r₂ r₃
  have r₁₂₃ := add_same_rate prefactorF headF P (addF C₀ C₀) _ _ p _ g₁ (g₂+g₃) W hW r₁ r₂₃
  have all := add_same_rate prefixF tailF (addF P (addF C₀ C₀)) Q
    (prefixData z v R B) (tailData z v R B) _ q (g₁+(g₂+g₃)) g₄ W hW r₁₂₃ r₄
  have hx := GaussianBarnesCanonicalPositiveFirstLogarithm.prefactor_regular (Γ := Γ) A B
  have ht := GaussianBarnesCanonicalDerivativeCofinal.regular z R B hz
  have e := GaussianBarnesCanonicalPositiveFirstLogarithmKept.kept_fold A B N K hB hK hM
  let G := addF (addF P (addF C₀ C₀)) Q
  let y := addData (addData p (addData (qmul d a) (qmul d b))) q
  let model := multiplyData C₀ F d (addData x (addData (qadd a b) t))
  have ed : Γ ⊢[PRAAx] linearData A C B R ≐ model := by
    ipra_congr (multiplyData C₀ F (var 0) (addData (var 1) (addData (var 2) (var 3))) : PTm 4)
      with [.eqRefl d, .eqRefl x, e, .eqRefl t]
      using [linearData,GaussianBarnesCanonicalPositiveFirstLogarithm.data,
        GaussianBarnesCanonicalPositiveFirstLogarithm.seriesData,model]
  have rg : Γ ⊢[PRAAx] crossEquivalent linearF G (linearData A C B R) y :=
    GaussianGammaCompactCutoffAlignment.cross_data_congr linearF G model (linearData A C B R) y y ed.eqSymm (.eqRefl _)
      (reorganize E D d x a b t hx ht)
  have total := GaussianNamedRateTransport.transport nameF G nameF linearF (data z v R B) y
    (data z v R B) (linearData A C B R) _ W hW all
    (cross_refl _ _ (GaussianBarnesCanonicalRelativeLogIncrement.regular z v R B h.andE₂.andE₁)) rg
  exact GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ _ _
    (by dsimp only [g₁,g₂,g₃,g₄,numerator,gain,N,GaussianBarnesCanonicalPositiveHeadLogarithmRowDerivative.numerator,
      GaussianBarnesCanonicalDerivativeInterval.errorNumerator,GaussianBarnesCanonicalDerivativeBinding.boundNumerator]; ipra_ring)
    (.eqRefl _) total

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPositiveRelativeLogarithmDerivative

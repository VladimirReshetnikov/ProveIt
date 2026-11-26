import IPRADerivations.Analysis.Stirling.GaussianStirlingGammaLogarithm
import IPRADerivations.Analysis.Euler.HarmonicLogarithms.GaussianHarmonicLogarithmName
import IPRADerivations.Analysis.SpecialFunctions.DampingPower.GaussianNamedDampingPowerRealSamples
import IPRADerivations.Analysis.Exponential.PositiveAxis.GaussianRealExponentialPositiveIncrement

/-!
# Stirling's (A(x)) on positive rational arguments

The name computes (logGamma(x)-(x-	frac12)log x+x).
The Gamma logarithm reads retimed observations of the original Gamma
at (x), and the rational logarithm uses the original harmonic sampler.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 700000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingNames

open_ipra
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiplyModulus multiply_at multiply_fast)
open GaussianNameRingLaws (negativeF negativeData negative_fast)
open GaussianSignedNameExponentialOrder (realSamples real_sample_at)
open GaussianRationalHorner (canonical canonical_congr qmul qmul_canonical)
open GaussianRationalMetric (qsub qsub_canonical)
open RationalGaussianEmbedding (axis axis_congr embed_axis axis_add axis_negative axis_multiply)
open GaussianPositiveRationalLogarithm (fraction)

export GaussianStirlingGammaLogarithm (source arg gammaData gammaMargin gammaLogMargin gammaRealF
  gammaRetimedF gammaRetimedData logGammaF logGammaData gamma_source gamma_source_at_radius source_shift
  log_gamma_regular gamma_regular gamma_real_cross gamma_retimed_cross log_input)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def logXF : PR 2 := GaussianHarmonicLogarithmName.nameF
def logXData (a b : PTm n) : PTm n := GaussianHarmonicLogarithmName.data a b
def point (a b : PTm n) : PTm n := fraction a b
def offset (a b : PTm n) : PTm n := qsub (point a b) (point one two)
def productF : PR 2 := multiplyF constantF logXF
def productData (a b : PTm n) : PTm n := multiplyData constantF logXF (offset a b) (logXData a b)
def negativeProductF : PR 2 := negativeF productF
def negativeProductData (a b : PTm n) : PTm n := negativeData (productData a b)
def differenceF : PR 2 := addF logGammaF negativeProductF
def differenceData (a b : PTm n) : PTm n := addData (logGammaData a b) (negativeProductData a b)
def nameF : PR 2 := addF differenceF constantF
def nameData (a b : PTm n) : PTm n := addData (differenceData a b) (point a b)

ipra_subst logXData
ipra_subst point
ipra_subst offset [one, two]
ipra_subst productData
ipra_subst negativeProductData
ipra_subst differenceData
ipra_subst nameData

theorem log_x_regular (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] pointCN logXF (logXData a b) :=
  GaussianHarmonicLogarithmName.name_regular a b h

theorem product_regular (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx] pointCN productF (productData a b) :=
  multiply_fast constantF logXF _ _ (constant_regular _) (log_x_regular a b h)

theorem name_regular (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx] pointCN nameF (nameData a b) :=
  add_fast differenceF constantF _ _
    (add_fast logGammaF negativeProductF _ _ (log_gamma_regular a b h)
      (negative_fast productF _ (product_regular a b h))) (constant_regular _)

theorem fraction_axis (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx] axis (point a b) :=
  axis_congr (GaussianEulerDecayOrder.fraction_embedding a b hb) (embed_axis _)

theorem constant_real (x : PTm n) (hc : Γ ⊢[PRAAx] canonical x) (hr : Γ ⊢[PRAAx] axis x) :
    Γ ⊢[PRAAx] realSamples constantF x := by
  refine .allI ?_
  let X := Syn.shift x
  let Δ := Γ.map Fm.shift
  have c : Δ ⊢[PRAAx] canonical X := by simpa [Fm.shift,Syn.shift,X,Δ] using hc.shift
  have r : Δ ⊢[PRAAx] axis X := by simpa [Fm.shift,Syn.shift,X,Δ] using hr.shift
  have e := constant_at (Γ := Δ) (var 0) X
  simpa [realSamples,X,Δ] using Prf.andI (canonical_congr e c) (axis_congr e.eqSymm r)

theorem multiply_real (f g : PR 2) (x y : PTm n)
    (hf : Γ ⊢[PRAAx] realSamples f x) (hg : Γ ⊢[PRAAx] realSamples g y) :
    Γ ⊢[PRAAx] realSamples (multiplyF f g) (multiplyData f g x y) := by
  refine .allI ?_
  let X := Syn.shift x
  let Y := Syn.shift y
  let Δ := Γ.map Fm.shift
  let p : PTm (n+1) := var 0
  let s := GaussianFastValueCut.exponent (multiplyModulus f g X Y) p
  let a := ap2 f s X
  let b := ap2 g s Y
  have hF : Δ ⊢[PRAAx] realSamples f X := by simpa [Fm.shift,Syn.shift,Δ,X] using hf.shift
  have hG : Δ ⊢[PRAAx] realSamples g Y := by simpa [Fm.shift,Syn.shift,Δ,Y] using hg.shift
  have read : Δ ⊢[PRAAx] ap2 (multiplyF f g) p (multiplyData f g X Y) ≐ qmul a b :=
    (multiply_at f g X Y p).eqTrans (GaussianExponentialReference.recode_fixed _ (qmul_canonical _ _))
  have real := axis_congr read.eqSymm (axis_multiply a b
    (real_sample_at f X s hF).andE₂ (real_sample_at g Y s hG).andE₂)
  simpa [realSamples,Syn.shift,Δ,X,Y,p] using Prf.andI (canonical_congr read (qmul_canonical _ _)) real

theorem add_real (f g : PR 2) (x y : PTm n)
    (hf : Γ ⊢[PRAAx] realSamples f x) (hg : Γ ⊢[PRAAx] realSamples g y) :
    Γ ⊢[PRAAx] realSamples (addF f g) (addData x y) := by
  refine .allI ?_
  let X := Syn.shift x
  let Y := Syn.shift y
  let Δ := Γ.map Fm.shift
  have hF : Δ ⊢[PRAAx] realSamples f X := by simpa [Fm.shift,Syn.shift,Δ,X] using hf.shift
  have hG : Δ ⊢[PRAAx] realSamples g Y := by simpa [Fm.shift,Syn.shift,Δ,Y] using hg.shift
  simpa [realSamples,Syn.shift,Δ,X,Y] using
    GaussianRealExponentialPositiveIncrement.sum_real_at f g (var 0) X Y hF hG

theorem positive_log_real (f : PR 2) (x E : PTm n) : Γ ⊢[PRAAx]
    realSamples (GaussianNamedPositiveLogarithm.nameF f) (GaussianNamedPositiveLogarithm.data x E) := by
  refine .allI ?_
  let X := Syn.shift x
  let D := Syn.shift E
  let Δ := Γ.map Fm.shift
  let p : PTm (n+1) := var 0
  let k := GaussianNamedPositiveLogarithm.clock p D
  have read := GaussianNamedPositiveLogarithm.sample_at (Γ := Δ) f p X D
  have c := canonical_congr read (GaussianPositiveRationalLogarithm.sample_canonical (succ p)
    (GaussianNamedPositiveLogarithm.numerator f k X) (GaussianNamedPositiveLogarithm.denominator f k X))
  simpa [realSamples,Syn.shift,Δ,X,D,p] using
    Prf.andI c (GaussianNamedPositiveLogarithm.sample_real f p X D)

theorem log_gamma_real (a b : PTm n) : Γ ⊢[PRAAx] realSamples logGammaF (logGammaData a b) :=
  positive_log_real _ _ _

theorem log_x_real (a b : PTm n) : Γ ⊢[PRAAx] realSamples logXF (logXData a b) :=
  GaussianHarmonicLogarithmName.real_samples a b

theorem name_real (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx] realSamples nameF (nameData a b) := by
  have axisX := fraction_axis a b h.andE₂
  have offsetReal : Γ ⊢[PRAAx] axis (offset a b) := axis_add _ _ axisX
    (axis_negative _ (fraction_axis one two (le_succ_self one)))
  have pr := multiply_real constantF logXF (offset a b) (logXData a b)
    (constant_real _ (qsub_canonical _ _) offsetReal) (log_x_real a b)
  have neg := GaussianNamedDampingPowerRealSamples.negative_real productF (productData a b) pr
  exact add_real differenceF constantF _ _
    (add_real logGammaF negativeProductF _ _ (log_gamma_real a b) neg)
    (constant_real _ (GaussianRationalHorner.ofGaussian_canonical _ _ h.andE₂) axisX)

theorem actual_Stirling_positive_rational_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (source (var 1) (var 0) ⟶
      (pointCN nameF (nameData (var 1) (var 0)) ⋏ realSamples nameF (nameData (var 1) (var 0)))) :=
  closeUniv 2 (.impI (.andI (name_regular _ _ Prf.hyp0) (name_real _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianStirlingNames

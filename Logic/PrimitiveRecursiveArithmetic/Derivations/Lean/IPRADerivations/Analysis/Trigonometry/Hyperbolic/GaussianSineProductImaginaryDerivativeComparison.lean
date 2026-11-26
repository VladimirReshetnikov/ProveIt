import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateComposition
import IPRADerivations.Analysis.Names.Differences.GaussianNamedScaledDerivativeUniqueness
import IPRADerivations.Analysis.Trigonometry.Hyperbolic.GaussianSineProductImaginaryHyperbolicDerivative

/-!
# Comparing the product and exponential derivatives of the original sinh

An internal dyadic sequence provides a common step for the original
hyperbolic and sine-product expressions. Any uniform first-order bound
for the actual product increment on this sequence yields an exact
cross-equivalence of its derivative and the exponential derivative.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianSineProductImaginaryDerivativeComparison

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianBoundedConstantProductName (constantF constant_regular)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaWeierstrassApproximant (constant_data_cross)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameBounds (U U_positive)
open GaussianNameEquivalence (crossEquivalent cross_refl)
open GaussianNamedDifferenceQuotientProperness (difference_proper)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedScaledDerivativeUniqueness (weightedF weightedData)
open GaussianRationalHorner (positive_product)
open GaussianSineProductImaginaryExponentialShift (source)
open GaussianSineProductImaginaryHyperbolic (sinhF sinhData productF productData)
open GaussianSineProductImaginaryHyperbolicDerivative (derivativeF derivativeData derivative_regular error)
open GaussianSineProductImaginaryLogDerivative (rationalReal)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Pi" => GaussianGammaHalfPiName.nameF
local notation "Diff" => GaussianNamedDifference.nameF
local notation "difference" => GaussianNamedDifference.data
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def scale (x s : PTm n) : PTm n := U Pi x*unit s
def fixedDenominator (B x : PTm n) : PTm n := U Pi x*B
def prodIncrementF : PR 2 := Diff productF productF
def prodIncrementData (A B k R x : PTm n) : PTm n :=
  difference (productData (k*A+one) (k*B) R x) (productData A B R x)
def productRate (F : PR 2) (y A B k R x C : PTm n) : Fm PTm n :=
  independentRate prodIncrementF (weightedF F) (prodIncrementData A B k R x)
    (multiplyData constantF F (rationalReal one (k*B)) y) C ((k*B)*(k*B))
def productFamily (F : PR 2) (y A B R x C : PTm n) : Fm PTm n := .all
  (productRate F (Syn.shift y) (Syn.shift A) (Syn.shift B) (scale (Syn.shift x) (var 0))
    (Syn.shift R) (Syn.shift x) (Syn.shift C))

ipra_subst scale

ipra_subst productRate [prodIncrementData, productData, one]

ipra_subst productFamily [Syn.subst_shift, Syn.shift_subst]

theorem family_at (F : PR 2) (y A B R x C s : PTm n) (h : Γ ⊢[PRAAx] productFamily F y A B R x C) :
    Γ ⊢[PRAAx] productRate F y A B (scale x s) R x C := by
  simpa only [productFamily,subst_productRate,subst_scale,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE s

theorem scaled_source (A B R x s : PTm n) (hR : Γ ⊢[PRAAx] le one R) (hB : Γ ⊢[PRAAx] le one B)
    (hA : Γ ⊢[PRAAx] le (A+one) (R*B)) : Γ ⊢[PRAAx] source A B (scale x s) R x := by
  let k := scale x s
  have hk : Γ ⊢[PRAAx] le one k := positive_product _ _ (U_positive Pi x) (unit_positive s)
  have h0 : Γ ⊢[PRAAx] le A (R*B) := le_trans (le_add_right _ _) hA
  have h1 : Γ ⊢[PRAAx] le (k*A+one) (R*(k*B)) := by
    ipra_le 𝔞 k * sl hA + sl hk
  have h2 : Γ ⊢[PRAAx] le (U Pi x) (k*B) :=
    le_congr (one_mul _) (by dsimp only [k,scale]; ipra_ring)
      (le_mul_mono (positive_product _ _ (unit_positive s) hB) (le_refl (U Pi x)))
  exact .andI hR (.andI hB (.andI hk (.andI h0 (.andI h1 h2))))

private theorem eq_step (B x s : PTm n) : Γ ⊢[PRAAx]
    GaussianNamedScaledDerivativeUniqueness.step (fixedDenominator B x) s ≐ rationalReal one (scale x s*B) := by
  have e : Γ ⊢[PRAAx] fixedDenominator B x*unit s ≐ scale x s*B := by
    dsimp only [fixedDenominator,scale]
    ipra_ring
  simpa only [GaussianNamedScaledDerivativeUniqueness.step,GaussianSineProductImaginaryLogDerivative.subst_rationalReal,
    Syn.subst_var,Matrix.cons_val_zero,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
      (Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (rationalReal one (var 0) : PTm 1)
        (σ := ![fixedDenominator B x*unit s]) (σ' := ![scale x s*B]) (fun i => by fin_cases i; exact e))

private theorem normalize_weight (F : PR 2) (y B x s : PTm n) (hy : Γ ⊢[PRAAx] pointCN F y) :
    Γ ⊢[PRAAx] crossEquivalent (weightedF F) (weightedF F) (weightedData F y (fixedDenominator B x) s)
      (multiplyData constantF F (rationalReal one (scale x s*B)) y) := by
  let a := GaussianNamedScaledDerivativeUniqueness.step (fixedDenominator B x) s
  let b := rationalReal one (scale x s*B)
  exact multiply_cross constantF constantF F F a b y y (constant_regular _) (constant_regular _) hy hy
    (constant_data_cross _ _ (eq_step B x s)) (cross_refl _ _ hy)

private theorem product_regular (A B R x : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A (R*B)) :
    Γ ⊢[PRAAx] pointCN productF (productData A B R x) :=
  multiply_fast _ _ _ _ (GaussianPiRationalScale.regular false A B R x hB hA)
    (GaussianSineProductName.name_regular _ _ _ hB (GaussianSineProductImaginaryFirstOrderBound.axis_disk A B R hA))

private theorem sinh_regular (A B R x : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A (R*B)) :
    Γ ⊢[PRAAx] pointCN sinhF (sinhData A B R x) := by
  have h (s : Bool) := GaussianRadiusExponentialName.name_regular _ _ _
    (GaussianPiRationalScale.exponential_input s A B R x hB hA)
  exact multiply_fast _ _ _ _ (constant_regular _) (GaussianNamedDifference.name_regular _ _ _ _ (h true) (h false))

theorem compare_step (F : PR 2) (y A B R x C s : PTm n)
    (hR : Γ ⊢[PRAAx] le one R) (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le (A+one) (R*B))
    (hy : Γ ⊢[PRAAx] pointCN F y) (hp : Γ ⊢[PRAAx] productRate F y A B (scale x s) R x C) :
    Γ ⊢[PRAAx] independentRate (weightedF derivativeF) (weightedF F)
      (weightedData derivativeF (derivativeData A B R x) (fixedDenominator B x) s) (weightedData F y (fixedDenominator B x) s)
      (error A B R x+C) ((fixedDenominator B x*unit s)*(fixedDenominator B x*unit s)) := by
  let k := scale x s
  let E := k*B
  let D := E*E
  let H := GaussianSineProductImaginaryHyperbolicDerivative.incrementF
  let hx := GaussianSineProductImaginaryHyperbolicDerivative.incrementData A B k R x
  let d := derivativeData A B R x
  let dx := GaussianSineProductImaginaryHyperbolicDerivative.weightedData A B k R x
  let dy := multiplyData constantF F (rationalReal one E) y
  have hs := scaled_source A B R x s hR hB hA
  have hk := hs.andE₂.andE₂.andE₁
  have ha := hs.andE₂.andE₂.andE₂.andE₁
  have ht := hs.andE₂.andE₂.andE₂.andE₂.andE₁
  have hE : Γ ⊢[PRAAx] le one E := positive_product _ _ hk hB
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ hE hE
  have hLeft := GaussianSineProductImaginaryHyperbolicDerivative.independent_rate A B k R x hs
  have base := GaussianSineProductImaginaryHyperbolic.sinh_as_product A B R x hR hB ha
  have later := GaussianSineProductImaginaryHyperbolic.sinh_as_product (k*A+one) E R x hR hE ht
  have same := difference_proper sinhF productF sinhF productF _ _ _ _
    (sinh_regular (k*A+one) E R x hE ht) (product_regular (k*A+one) E R x hE ht)
    (sinh_regular A B R x hB ha) (product_regular A B R x hB ha) later base
  have hg := multiply_fast constantF F (rationalReal one E) y (constant_regular _) hy
  have hRight := GaussianNamedRateTransport.transport prodIncrementF (weightedF F) H (weightedF F)
    (prodIncrementData A B k R x) dy hx dy C D hD hp same (cross_refl _ _ hg)
  have reverse := GaussianNamedRateComposition.symmetric H (weightedF derivativeF) hx dx (error A B R x) D hD hLeft
  have both := GaussianNamedRateComposition.same_denominator (weightedF derivativeF) H (weightedF F)
    dx hx dy (error A B R x) D C hD reverse hRight
  have moved := GaussianNamedRateTransport.transport _ _ _ _ dx dy _ _ (error A B R x+C) D hD both
    (normalize_weight derivativeF d B x s (derivative_regular A B R x hB ha)) (normalize_weight F y B x s hy)
  exact GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ _ _ (.eqRefl _)
    (by dsimp only [D,E,k,scale,fixedDenominator]; ipra_ring) moved

theorem equal_derivatives (F : PR 2) (y A B R x C : PTm n) (hR : Γ ⊢[PRAAx] le one R)
    (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le (A+one) (R*B))
    (hy : Γ ⊢[PRAAx] pointCN F y) (hp : Γ ⊢[PRAAx] productFamily F y A B R x C) :
    Γ ⊢[PRAAx] crossEquivalent derivativeF F (derivativeData A B R x) y := by
  have hd := positive_product _ _ (U_positive Pi x) hB
  have hh := derivative_regular A B R x hB (le_trans (le_add_right _ _) hA)
  apply GaussianNamedScaledDerivativeUniqueness.unique _ _ _ _ (fixedDenominator B x) (error A B R x+C) hd hh hy
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let sh (t : PTm n) := Syn.shift t
  have rs : Δ ⊢[PRAAx] le one (sh R) := by simpa [Δ,sh,Fm.shift,Syn.shift,one] using hR.shift
  have bs : Δ ⊢[PRAAx] le one (sh B) := by simpa [Δ,sh,Fm.shift,Syn.shift,one] using hB.shift
  have as' : Δ ⊢[PRAAx] le (sh A+one) (sh R*sh B) := by simpa [Δ,sh,Fm.shift,Syn.shift,one] using hA.shift
  have ys : Δ ⊢[PRAAx] pointCN F (sh y) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hy.shift
  have ps : Δ ⊢[PRAAx] productFamily F (sh y) (sh A) (sh B) (sh R) (sh x) (sh C) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using hp.shift
  simpa only [GaussianNamedScaledDerivativeUniqueness.family,Δ,sh,Syn.shift,derivativeData,
    GaussianSineProductImaginaryHyperbolicDerivative.branchData,GaussianPiRationalScaleFactors.signedData,
    GaussianSineProductImaginaryHyperbolic.expData,GaussianSineProductImaginaryHyperbolicDerivative.negativeHalf,
    GaussianSineProductImaginaryExponentialShift.errorCoefficient,error,fixedDenominator,
    GaussianNameArithmetic.subst_multiplyData,GaussianNamedDifference.subst_data,GaussianRadiusExponentialName.subst_data,
    GaussianPiRationalScale.subst_data,GaussianPiRationalScale.subst_point,GaussianNameBounds.subst_U,PTm.subst_add,PTm.subst_mul,
    one,two,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    compare_step F (sh y) (sh A) (sh B) (sh R) (sh x) (sh C) (var 0) rs bs as' ys
      (family_at F (sh y) (sh A) (sh B) (sh R) (sh x) (sh C) (var 0) ps)

end LeanProofs.IPRA.Analysis.GaussianSineProductImaginaryDerivativeComparison

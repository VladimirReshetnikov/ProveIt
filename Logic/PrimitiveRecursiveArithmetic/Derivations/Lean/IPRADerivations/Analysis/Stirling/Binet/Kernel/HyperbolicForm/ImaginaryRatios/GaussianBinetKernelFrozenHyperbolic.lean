import IPRADerivations.Analysis.Stirling.Binet.Kernel.HyperbolicForm.ImaginaryRatios.GaussianBinetKernelImaginaryRatioCofinal
import IPRADerivations.Analysis.Names.Rates.Scaling.GaussianBoundedConstantProductRate
import IPRADerivations.Analysis.Names.Rates.Perturbations.GaussianNamedDifferenceRate
import IPRADerivations.Analysis.Exponential.Estimates.Lipschitz.GaussianRadiusExponentialLipschitzRate
import IPRADerivations.Analysis.Trigonometry.Pi.GaussianPiRationalScaleRepresentation

/-!
# The original hyperbolic names at a frozen imaginary ratio

Freeze π at the original observation with clock `k` and encode the
positive ratio `(A/B)/(2π_k)`. Multiplication by that same π observation
gives exactly the signed rational time `±A/(2B)`. One radius depending
only on `A` works for both original exponential samplers, and the fixed
hyperbolic names retain the independent dyadic error bound.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBinetKernelFrozenHyperbolic

open_ipra
open ComplexLogarithmRemainder (scale oneCode eval_re_code eval_im_code)
open GaussianBinetKernelImaginaryRatioCofinal (anchored_rate)
open GaussianBinetKernelImaginaryRatioRows (ratioNumerator ratioDenominator ratioRadius ratio_source)
open GaussianBinetKernelPi (sample sample_fraction)
open GaussianBoundedConstantProductName (constantF constant_at constant_regular ordinary_product_identity)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaWeierstrassApproximant (constant_data_cross constant_product_cross)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameBounds (U U_positive)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedRateTransport (transport)
open GaussianPiRationalScale (point native point_bound subst_point)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner
  (canonical_unique ofGaussian_canonical ofGaussian_represents positive_product qmul qmul_canonical
    qmul_represents represents_congr)
open GaussianRationalMetric (bounded)
open GaussianRootAlgebra (equal_of_values re_mul im_mul re_scale im_scale re_one im_one re_neg im_neg)
open GaussianSineProductImaginaryCoshIdentity (coshData coshF cosh_regular)
open GaussianSineProductImaginaryHyperbolic (expF expData sinhF sinhData)
open GaussianSineProductImaginaryLogDerivative (realNumerator)
open GaussianStirlingConstant (piNumerator piDenominator)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Pi" => GaussianGammaHalfPiName.nameF
local notation "Scale" => GaussianPiRationalScale.nameF
local notation "Exp" => GaussianRadiusExponentialName.nameF
local notation "exData" => GaussianRadiusExponentialName.data
local notation "Diff" => GaussianNamedDifference.nameF
local notation "diffData" => GaussianNamedDifference.data

def halfTime (s : Bool) (A B : PTm n) : PTm n := point s A (two*B)
def scaleBudget (A : PTm n) : PTm n := ratioRadius A*(zero+two)
def expRadius (A : PTm n) : PTm n := ratioRadius A*U Pi zero
def expBudget (A : PTm n) : PTm n := GaussianRadiusExponentialLipschitzRate.factor (expRadius A)*scaleBudget A
def hyperbolicBudget (A : PTm n) : PTm n := expBudget A+expBudget A

abbrev fixedExpF : PR 2 := Exp constantF
def fixedExpData (s : Bool) (A B : PTm n) : PTm n := exData (expRadius A) (halfTime s A B)

abbrev fixedSinhF : PR 2 := multiplyF constantF (Diff fixedExpF fixedExpF)
def fixedSinhData (A B : PTm n) : PTm n :=
  multiplyData constantF (Diff fixedExpF fixedExpF) (point true one two)
    (diffData (fixedExpData true A B) (fixedExpData false A B))

abbrev fixedCoshF : PR 2 := multiplyF constantF (addF fixedExpF fixedExpF)
def fixedCoshData (A B : PTm n) : PTm n :=
  multiplyData constantF (addF fixedExpF fixedExpF) (point false one two)
    (addData (fixedExpData true A B) (fixedExpData false A B))

abbrev frozenScaleData (s : Bool) (k A B : PTm n) : PTm n :=
  GaussianPiRationalScale.data s (ratioNumerator k A) (ratioDenominator k B) (ratioRadius A) zero
abbrev frozenExpData (s : Bool) (k A B : PTm n) : PTm n :=
  expData s (ratioNumerator k A) (ratioDenominator k B) (ratioRadius A) zero
abbrev frozenSinhData (k A B : PTm n) : PTm n :=
  sinhData (ratioNumerator k A) (ratioDenominator k B) (ratioRadius A) zero
abbrev frozenCoshData (k A B : PTm n) : PTm n :=
  coshData (ratioNumerator k A) (ratioDenominator k B) (ratioRadius A) zero

ipra_subst halfTime [two, one]
ipra_subst scaleBudget [ratioRadius, two, one]
ipra_subst expRadius [ratioRadius, one]
ipra_subst expBudget
ipra_subst hyperbolicBudget
ipra_subst fixedExpData
ipra_subst fixedSinhData [two, one]
ipra_subst fixedCoshData [two, one]

private theorem point_congr (s : Bool) {a b c d : PTm n}
    (ha : Γ ⊢[PRAAx] a ≐ c) (hb : Γ ⊢[PRAAx] b ≐ d) :
    Γ ⊢[PRAAx] point s a b ≐ point s c d := by
  simpa only [subst_point,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (point s (var 0) (var 1) : PTm 2)
      (σ := ![a,b]) (σ' := ![c,d]) (fun i => by fin_cases i; exact ha; exact hb)

private theorem point_fraction_product (s : Bool) (a b u v : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hv : Γ ⊢[PRAAx] le one v) : Γ ⊢[PRAAx]
    qmul (point s a b) (fraction u v) ≐ point s (a*u) (b*v) := by
  let c := native s a
  let d := scale u oneCode
  let E := b*v
  have he := positive_product (Γ := Γ) _ _ hb hv
  have product := qmul_represents (point s a b) (fraction u v) c d b v hb hv
    (ofGaussian_represents c b hb) (ofGaussian_represents d v hv)
  have value : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (ComplexLogarithmRemainder.mul c d) (native s (a*u)) := by
    cases s <;> apply equal_of_values <;>
      simp only [c,d,native,Bool.false_eq_true,if_false,if_true,realNumerator,
        re_mul,im_mul,re_neg,im_neg,re_scale,im_scale,re_one,im_one,eval_re_code,eval_im_code,ZT.toZ_ofNat] <;>
      ipra_simps <;> ring
  exact canonical_unique _ _ _ E (qmul_canonical _ _) (ofGaussian_canonical _ _ he) he
    (represents_congr (.eqRefl _) value (.eqRefl E) product) (ofGaussian_represents _ _ he)

theorem frozen_product_value (s : Bool) (k A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] qmul (point s (ratioNumerator k A) (ratioDenominator k B)) (sample k) ≐ halfTime s A B := by
  let u := piNumerator k
  let v := piDenominator k
  let a := ratioNumerator k A
  let b := ratioDenominator k B
  have h2 := le_succ_self (Γ := Γ) one
  have hv := GaussianBinetKernelPi.denominator_positive (Γ := Γ) k
  have hu := le_trans (positive_product _ _ h2 hv) (GaussianBinetKernelPi.sample_margins (Γ := Γ) k).andE₁
  have hb := (ratio_source k A B hB).andE₂.andE₁
  have h2B := positive_product _ _ h2 hB
  have hprod := positive_product _ _ hu hv
  have e : Γ ⊢[PRAAx] point s (a*u) (b*v) ≐ point s ((u*v)*A) ((u*v)*(two*B)) :=
    point_congr s (by dsimp only [a,ratioNumerator,u,v]; ipra_ring)
      (by dsimp only [b,ratioDenominator,u,v]; ipra_ring)
  exact (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) (sample_fraction k)).eqTrans
    ((point_fraction_product s a b u v hb hv).eqTrans (e.eqTrans
      (GaussianPiRationalScaleRepresentation.point_rescale s A (two*B) (u*v) h2B hprod)))

private theorem frozen_point_bound (s : Bool) (k A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] bounded (point s (ratioNumerator k A) (ratioDenominator k B)) (ratioRadius A) one := by
  have src := ratio_source k A B hB
  exact point_bound s _ _ _ _ src.andE₂.andE₁ (le_refl one)
    (le_congr (by ipra_ring) (.eqRefl _) (le_trans (le_add_right _ one) src.andE₂.andE₂))

theorem frozen_scale_rate (s : Bool) (k A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] independentRate Scale constantF (frozenScaleData s k A B) (halfTime s A B) (scaleBudget A) (unit k) := by
  let c := point s (ratioNumerator k A) (ratioDenominator k B)
  let z := sample k
  let y := halfTime s A B
  let R := ratioRadius A
  let G := GaussianBoundedConstantProductName.nameF constantF
  let g := GaussianBoundedConstantProductName.data R c z
  have hk := unit_positive (Γ := Γ) k
  have hc := frozen_point_bound s k A B hB
  have same : Γ ⊢[PRAAx] GaussianRationalMetric.distanceBounded (ap2 Pi k zero) (ap2 constantF k z) zero (unit k) :=
    distance_congr (.eqRefl _) (constant_at k z).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianRationalPowerDifference.distance_refl_zero z (unit k) hk)
  have piRate := anchored_rate Pi constantF zero z k zero (GaussianGammaHalfPiName.name_regular zero)
    (constant_regular z) same
  have scaled := GaussianBoundedConstantProductRate.original_rate Pi constantF R c zero z _ _ hk hc piRate
  have ordinary := ordinary_product_identity constantF R c z (.andI (constant_regular z) hc)
  have product := cross_trans _ _ _ _ _ _ (constant_product_cross c z)
    (constant_data_cross (qmul c z) y (frozen_product_value s k A B hB))
  have bind : Γ ⊢[PRAAx] crossEquivalent G constantF g y := cross_trans _ _ _ _ _ _ ordinary product
  have src := ratio_source k A B hB
  have reg := GaussianPiRationalScale.regular s (ratioNumerator k A) (ratioDenominator k B) R zero
    src.andE₂.andE₁ (le_trans (le_add_right _ one) src.andE₂.andE₂)
  exact transport Scale G Scale constantF _ _ _ _ _ _ hk scaled (cross_refl _ _ reg) (cross_symm _ _ _ _ bind)

theorem fixed_exp_input (s : Bool) (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] GaussianRadiusExponentialName.input constantF (expRadius A) (halfTime s A B) := by
  let R := ratioRadius A
  let S := expRadius A
  have h2B := positive_product _ _ (le_succ_self (Γ := Γ) one) hB
  have growth : Γ ⊢[PRAAx] le R S :=
    le_congr (by ipra_ring : Γ ⊢[PRAAx] one*R ≐ R) (by dsimp only [S,expRadius]; ipra_ring)
      (mul_le_mul_right R (U_positive Pi zero))
  have cap : Γ ⊢[PRAAx] le A (S*(two*B)) := le_trans (le_add_right A one) (le_trans growth
    (le_congr (by ipra_ring : Γ ⊢[PRAAx] one*S ≐ S) (by ipra_ring) (mul_le_mul_right S h2B)))
  exact GaussianSignedNameExponentialOrder.constant_input (halfTime s A B) S
    (point_bound s A (two*B) S one h2B (le_refl one) (le_congr (by ipra_ring) (.eqRefl _) cap))

theorem fixed_exp_regular (s : Bool) (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] pointCN fixedExpF (fixedExpData s A B) :=
  GaussianRadiusExponentialName.name_regular _ _ _ (fixed_exp_input s A B hB)

theorem fixed_sinh_regular (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx] pointCN fixedSinhF (fixedSinhData A B) :=
  multiply_fast _ _ _ _ (constant_regular _)
    (GaussianNamedDifference.name_regular _ _ _ _ (fixed_exp_regular true A B hB) (fixed_exp_regular false A B hB))

theorem fixed_cosh_regular (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx] pointCN fixedCoshF (fixedCoshData A B) :=
  multiply_fast _ _ _ _ (constant_regular _)
    (add_fast _ _ _ _ (fixed_exp_regular true A B hB) (fixed_exp_regular false A B hB))

theorem frozen_exp_regular (s : Bool) (k A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] pointCN expF (frozenExpData s k A B) := by
  have src := ratio_source k A B hB
  exact GaussianRadiusExponentialName.name_regular _ _ _
    (GaussianPiRationalScale.exponential_input s _ _ _ zero src.andE₂.andE₁ (le_trans (le_add_right _ one) src.andE₂.andE₂))

theorem frozen_exp_rate (s : Bool) (k A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] independentRate expF fixedExpF (frozenExpData s k A B) (fixedExpData s A B) (expBudget A) (unit k) := by
  have src := ratio_source k A B hB
  have variableInput := GaussianPiRationalScale.exponential_input s _ _ (ratioRadius A) zero src.andE₂.andE₁
    (le_trans (le_add_right _ one) src.andE₂.andE₂)
  exact GaussianRadiusExponentialLipschitzRate.independent_rate Scale constantF (expRadius A)
    (frozenScaleData s k A B) (halfTime s A B) (scaleBudget A) (unit k)
    (.andI (unit_positive k) (.andI variableInput (.andI (fixed_exp_input s A B hB) (frozen_scale_rate s k A B hB))))

private theorem constant_unit_product_rate (F G : PR 2) (c x y A N : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hc : Γ ⊢[PRAAx] bounded c one one)
    (hf : Γ ⊢[PRAAx] pointCN F x) (hg : Γ ⊢[PRAAx] pointCN G y)
    (h : Γ ⊢[PRAAx] independentRate F G x y A N) :
    Γ ⊢[PRAAx] independentRate (multiplyF constantF F) (multiplyF constantF G)
      (multiplyData constantF F c x) (multiplyData constantF G c y) A N := by
  let P := GaussianBoundedConstantProductName.nameF F
  let Q := GaussianBoundedConstantProductName.nameF G
  let u := GaussianBoundedConstantProductName.data one c x
  let v := GaussianBoundedConstantProductName.data one c y
  have p := ordinary_product_identity F one c x (.andI hf hc)
  have q := ordinary_product_identity G one c y (.andI hg hc)
  have old := GaussianBoundedConstantProductRate.original_rate F G one c x y A N hN hc h
  have exactRate := GaussianNamedRateRadius.weaken P Q u v (one*A) N A N hN hN
    (le_of_eq_add (d := zero) (by ipra_ring)) old
  exact transport P Q _ _ u v _ _ A N hN exactRate (cross_symm _ _ _ _ p) (cross_symm _ _ _ _ q)

private theorem common_denominator (F G : PR 2) (x y A N : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (h : Γ ⊢[PRAAx] independentRate F G x y (A*N+A*N) (N*N)) :
    Γ ⊢[PRAAx] independentRate F G x y (A+A) N :=
  GaussianNamedRateRadius.weaken F G x y _ _ _ _ (positive_product _ _ hN hN) hN
    (le_of_eq_add (d := zero) (by ipra_ring)) h

private theorem half_bound (s : Bool) : Γ ⊢[PRAAx] bounded (point s one two : PTm n) one one :=
  point_bound s one two one one (le_succ_self one) (le_refl one) (by ipra_le 1)

theorem frozen_sinh_rate (k A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] independentRate sinhF fixedSinhF (frozenSinhData k A B) (fixedSinhData A B) (hyperbolicBudget A) (unit k) := by
  let l := frozenExpData true k A B
  let r := frozenExpData false k A B
  let u := fixedExpData true A B
  let v := fixedExpData false A B
  let N := unit k
  let E := expBudget A
  have hn := unit_positive (Γ := Γ) k
  have hl := frozen_exp_regular true k A B hB
  have hr := frozen_exp_regular false k A B hB
  have hu := fixed_exp_regular true A B hB
  have hv := fixed_exp_regular false A B hB
  have source : Γ ⊢[PRAAx] GaussianNamedDifferenceRate.source expF expF fixedExpF fixedExpF l r u v E N E N :=
    .andI (.andI hn hn) (.andI (.andI hl hr) (.andI (.andI hu hv)
      (.andI (frozen_exp_rate true k A B hB) (frozen_exp_rate false k A B hB))))
  have dif := GaussianNamedDifferenceRate.original_rate expF expF fixedExpF fixedExpF l r u v E N E N source
  exact constant_unit_product_rate _ _ (point true one two) (diffData l r) (diffData u v) _ N hn (half_bound true)
    (GaussianNamedDifference.name_regular _ _ _ _ hl hr) (GaussianNamedDifference.name_regular _ _ _ _ hu hv)
    (common_denominator _ _ _ _ E N hn dif)

theorem frozen_cosh_rate (k A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] independentRate coshF fixedCoshF (frozenCoshData k A B) (fixedCoshData A B) (hyperbolicBudget A) (unit k) := by
  let l := frozenExpData true k A B
  let r := frozenExpData false k A B
  let u := fixedExpData true A B
  let v := fixedExpData false A B
  let N := unit k
  let E := expBudget A
  have hn := unit_positive (Γ := Γ) k
  have sum := GaussianNamedAddRate.independent_rate expF expF fixedExpF fixedExpF l r u v E N E N hn hn
    (frozen_exp_rate true k A B hB) (frozen_exp_rate false k A B hB)
  exact constant_unit_product_rate _ _ (point false one two) (addData l r) (addData u v) _ N hn (half_bound false)
    (add_fast _ _ _ _ (frozen_exp_regular true k A B hB) (frozen_exp_regular false k A B hB))
    (add_fast _ _ _ _ (fixed_exp_regular true A B hB) (fixed_exp_regular false A B hB))
    (common_denominator _ _ _ _ E N hn sum)

theorem actual_Binet_frozen_hyperbolic_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 2) ⟶
      (independentRate sinhF fixedSinhF (frozenSinhData (var 0) (var 1) (var 2)) (fixedSinhData (var 1) (var 2))
        (hyperbolicBudget (var 1)) (unit (var 0)) ⋏
       independentRate coshF fixedCoshF (frozenCoshData (var 0) (var 1) (var 2)) (fixedCoshData (var 1) (var 2))
        (hyperbolicBudget (var 1)) (unit (var 0)))) :=
  closeUniv 3 (.impI (.andI (frozen_sinh_rate _ _ _ Prf.hyp0) (frozen_cosh_rate _ _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBinetKernelFrozenHyperbolic

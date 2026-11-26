import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerPositivePowerChartLogarithm
import IPRADerivations.Analysis.Euler.Integration.GaussianEulerPowerScalingParameter
import IPRADerivations.Analysis.Euler.GaussianEulerExponentialSubstitutionNamedKernel

/-!
# Pointwise Gamma kernel for the original positive rational power chart

Write Z=z/B, r=e/f, W=Z/r, and v=log(d/h)+r log(t). The actual
chart gives exp(v); cancelling the scale term in the exponent then gives
exp(Z log(t)-exp(v)) = exp(-W log(d/h)) exp(W v-exp(v)).
All sides retain their original named multiplication and exponential
programs, and the chart side uses its original constant clock.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPowerScalingKernel

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerPositivePowerChart (argument)
open GaussianEulerPositivePowerChartLogarithm (logarithmF logarithmData)
open GaussianEulerExponentialSubstitutionNamedKernel (linearF linearData)
open GaussianEulerPowerScalingParameter (scaled)
open GaussianPositiveRationalLogarithm (logF fraction)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaFiniteApproximantName (exponentialInputData exponential_input)
open GaussianNameArithmetic (addF addData add_fast add_equivalent multiplyF multiplyData multiply_fast)
open GaussianNameRingLaws (negativeF negativeData negative_fast zeroF)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans cross_to_diagonal)
open GaussianRationalHorner (ofGaussian qmul)
open GaussianEuclideanDistanceName (pointCN)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (B e f d h Q S E T a b : PTm n) : Fm PTm n :=
  le one B ⋏ GaussianEulerPositivePowerChart.source e f d h Q S E T a b

abbrev scaleF : PR 2 := negativeF (linearF logF)
def scaleData (z B e f d h : PTm n) : PTm n :=
  negativeData (linearData logF (scaled z f) (B*e) (GaussianPositiveRationalLogarithm.data d h))
abbrev scaleExpF : PR 2 := GaussianRadiusExponentialName.nameF scaleF
def scaleExpData (z B e f d h : PTm n) : PTm n :=
  exponentialInputData scaleF (scaleData z B e f d h)

abbrev originalExponentF : PR 2 := addF (linearF logF) (negativeF GaussianEulerPositivePowerChart.nameF)
def originalExponentData (z B e f d h S a b : PTm n) : PTm n :=
  addData (linearData logF z B (GaussianPositiveRationalLogarithm.data a b))
    (negativeData (GaussianEulerPositivePowerChart.data e f d h S a b))
abbrev originalF : PR 2 := GaussianRadiusExponentialName.nameF originalExponentF
def originalData (z B e f d h S a b : PTm n) : PTm n :=
  exponentialInputData originalExponentF (originalExponentData z B e f d h S a b)

abbrev transformedF : PR 2 := GaussianEulerExponentialSubstitutionNamedKernel.nameF logarithmF
def transformedData (z B e f d h a b : PTm n) : PTm n :=
  GaussianEulerExponentialSubstitutionNamedKernel.data logarithmF (scaled z f) (B*e) (logarithmData e f d h a b)
abbrev productF : PR 2 := multiplyF scaleExpF transformedF
def productData (z B e f d h a b : PTm n) : PTm n :=
  multiplyData scaleExpF transformedF (scaleExpData z B e f d h) (transformedData z B e f d h a b)

private theorem sum_congr (f g h k : PR 2) (x y u v : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (hh : Γ ⊢[PRAAx] pointCN h u) (hk : Γ ⊢[PRAAx] pointCN k v)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) (he' : Γ ⊢[PRAAx] crossEquivalent h k u v) :
    Γ ⊢[PRAAx] crossEquivalent (addF f h) (addF g k) (addData x u) (addData y v) :=
  add_equivalent f g h k x y u v hf hg hh hk
    (cross_to_diagonal _ _ _ _ he) (cross_to_diagonal _ _ _ _ he')

private theorem subtract_leading (f g : PR 2) (x y : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) :
    Γ ⊢[PRAAx] crossEquivalent (addF (negativeF f) (addF f g)) g
      (addData (negativeData x) (addData x y)) y := by
  have hn := negative_fast f x hf
  have assoc := GaussianNameRingLaws.add_associative (negativeF f) f g (negativeData x) x y hn hf hg
  have commute := GaussianNameRingLaws.add_commutative (negativeF f) f (negativeData x) x hn hf
  have cancel := cross_trans _ _ _ _ _ _ commute (GaussianNameRingLaws.add_negative f x hf)
  have sameZero : Γ ⊢[PRAAx] crossEquivalent zeroF zeroF x y := by
    apply GaussianNameConjugation.equal_samples_cross _ _ _ _
      (GaussianNameRingLaws.zero_fast x) (GaussianNameRingLaws.zero_fast y)
    refine .allI ?_
    simpa only [GaussianNameConjugation.pointwiseEqual,Syn.shift] using
      (GaussianNameRingLaws.zero_at (Γ := Γ.map Fm.shift) (var 0) (Syn.shift x)).eqTrans
        (GaussianNameRingLaws.zero_at (var 0) (Syn.shift y)).eqSymm
  have cancelAtY := cross_trans _ _ _ _ _ _ cancel sameZero
  have sum := sum_congr _ _ _ _ _ _ _ _
    (add_fast _ _ _ _ hn hf) (GaussianNameRingLaws.zero_fast y) hg hg cancelAtY (cross_refl _ _ hg)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ assoc)
    (cross_trans _ _ _ _ _ _ sum (GaussianNameRingLaws.add_zero_left g y hg))

theorem original_linear_rescaling (z B e f d h Q S E T a b : PTm n)
    (hs : Γ ⊢[PRAAx] source B e f d h Q S E T a b) :
    Γ ⊢[PRAAx] crossEquivalent (linearF logarithmF) (addF (linearF logF) (linearF logF))
      (linearData logarithmF (scaled z f) (B*e) (logarithmData e f d h a b))
      (addData (linearData logF (scaled z f) (B*e) (GaussianPositiveRationalLogarithm.data d h))
        (linearData logF z B (GaussianPositiveRationalLogarithm.data a b))) := by
  let l := GaussianPositiveRationalLogarithm.data d h
  let t := GaussianPositiveRationalLogarithm.data a b
  let p := GaussianEulerIntegrandName.powerExponentData (argument e f) f a b
  let r := GaussianEulerIntegrandName.coefficient (argument e f) f
  let W := ofGaussian (scaled z f) (B*e)
  let Z := ofGaussian z B
  let M := linearF logF
  have he := hs.andE₂.andE₁.andE₁.andE₁
  have hf := hs.andE₂.andE₁.andE₁.andE₂
  have hl := GaussianPositiveRationalLogarithm.name_regular d h hs.andE₂.andE₁.andE₂.andE₁
  have ht := GaussianPositiveRationalLogarithm.name_regular a b hs.andE₂.andE₂.andE₂.andE₁
  have hp : Γ ⊢[PRAAx] pointCN M p := multiply_fast constantF logF r t (constant_regular r) ht
  have hW := constant_regular (Γ := Γ) W
  have hZ := constant_regular (Γ := Γ) Z
  have piece := GaussianNameRingLaws.distributive constantF logF M W l p hW hl hp
  have assoc := GaussianNameRingLaws.multiply_associative constantF constantF logF W r t
    hW (constant_regular r) ht
  have eq := (GaussianRationalSyntheticDivision.qmul_congr (Prf.eqRefl W)
    (GaussianEulerPositivePowerChart.coefficient_exact e f hf)).eqTrans
      (GaussianEulerPowerScalingParameter.rescaled_times_power z B e f hs.andE₁ he hf)
  have constants := cross_trans _ _ _ _ _ _ (GaussianGammaWeierstrassApproximant.constant_product_cross W r)
    (GaussianGammaWeierstrassApproximant.constant_data_cross (qmul W r) Z eq)
  have times := GaussianGammaAdjacentCutoff.multiply_cross (multiplyF constantF constantF) constantF logF logF
    (multiplyData constantF constantF W r) Z t t
    (multiply_fast _ _ _ _ hW (constant_regular r)) hZ ht ht constants (cross_refl _ _ ht)
  have right := cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ assoc) times
  have left := multiply_fast constantF logF W l hW hl
  exact cross_trans _ _ _ _ _ _ piece
    (sum_congr M M (multiplyF constantF M) M (multiplyData constantF logF W l) (multiplyData constantF logF W l)
      (multiplyData constantF M W p) (multiplyData constantF logF Z t) left left
      (multiply_fast _ _ _ _ hW hp) (multiply_fast _ _ _ _ hZ ht) (cross_refl _ _ left) right)

theorem original_transformed_exponent (z B e f d h Q S E T a b : PTm n)
    (hs : Γ ⊢[PRAAx] source B e f d h Q S E T a b) :
    Γ ⊢[PRAAx] crossEquivalent
      (addF scaleF (GaussianEulerExponentialSubstitutionNamedKernel.exponentF logarithmF)) originalExponentF
      (addData (scaleData z B e f d h)
        (GaussianEulerExponentialSubstitutionNamedKernel.exponentData logarithmF (scaled z f) (B*e)
          (logarithmData e f d h a b))) (originalExponentData z B e f d h S a b) := by
  let L := logarithmF
  let M := linearF logF
  let l := linearData logF (scaled z f) (B*e) (GaussianPositiveRationalLogarithm.data d h)
  let t := linearData logF z B (GaussianPositiveRationalLogarithm.data a b)
  let v := logarithmData e f d h a b
  let F := GaussianEulerExponentialSubstitutionNamedKernel.innerF L
  let x := GaussianEulerExponentialSubstitutionNamedKernel.innerData L v
  let C := GaussianEulerPositivePowerChart.nameF
  let c := GaussianEulerPositivePowerChart.data e f d h S a b
  let q := linearData L (scaled z f) (B*e) v
  have hl : Γ ⊢[PRAAx] pointCN M l :=
    GaussianEulerExponentialSubstitutionNamedKernel.linear_regular _ _ _ _
      (GaussianPositiveRationalLogarithm.name_regular d h hs.andE₂.andE₁.andE₂.andE₁)
  have ht : Γ ⊢[PRAAx] pointCN M t :=
    GaussianEulerExponentialSubstitutionNamedKernel.linear_regular _ _ _ _
      (GaussianPositiveRationalLogarithm.name_regular a b hs.andE₂.andE₂.andE₂.andE₁)
  have hv := GaussianEulerPositivePowerChartLogarithm.logarithm_regular e f d h Q S E T a b hs.andE₂
  have hq : Γ ⊢[PRAAx] pointCN (linearF L) q :=
    GaussianEulerExponentialSubstitutionNamedKernel.linear_regular _ _ _ _ hv
  have hF : Γ ⊢[PRAAx] pointCN F x :=
    GaussianEulerExponentialSubstitutionNamedKernel.inner_regular _ _ hv
  have hC := GaussianEulerPositivePowerChart.name_regular e f d h Q S E T a b hs.andE₂
  have chart : Γ ⊢[PRAAx] crossEquivalent F C x c :=
    GaussianEulerPositivePowerChartLogarithm.original_chart e f d h Q S E T a b hs.andE₂
  have neg := GaussianNameRingLaws.negative_equivalent F C x c hF hC (cross_to_diagonal _ _ _ _ chart)
  have hn := negative_fast C c hC
  have lift := sum_congr (linearF L) (addF M M) (negativeF F) (negativeF C) q (addData l t)
    (negativeData x) (negativeData c) hq (add_fast _ _ _ _ hl ht) (negative_fast F x hF) hn
    (original_linear_rescaling z B e f d h Q S E T a b hs) neg
  have assoc := GaussianNameRingLaws.add_associative M M (negativeF C) l t (negativeData c) hl ht hn
  have rearranged := cross_trans _ _ _ _ _ _ lift assoc
  have hTail := add_fast M (negativeF C) t (negativeData c) ht hn
  have leading := negative_fast M l hl
  have sum := sum_congr (negativeF M) (negativeF M) _ _ (negativeData l) (negativeData l) _ _
    leading leading (add_fast _ _ _ _ hq (negative_fast F x hF)) (add_fast _ _ _ _ hl hTail)
    (cross_refl _ _ leading) rearranged
  exact cross_trans _ _ _ _ _ _ sum (subtract_leading M originalExponentF l (addData t (negativeData c)) hl hTail)

theorem original_transformed_kernel (z B e f d h Q S E T a b : PTm n)
    (hs : Γ ⊢[PRAAx] source B e f d h Q S E T a b) :
    Γ ⊢[PRAAx] crossEquivalent productF originalF
      (productData z B e f d h a b) (originalData z B e f d h S a b) := by
  let L := logarithmF
  let v := logarithmData e f d h a b
  let x := scaleData z B e f d h
  let y := GaussianEulerExponentialSubstitutionNamedKernel.exponentData L (scaled z f) (B*e) v
  let u := originalExponentData z B e f d h S a b
  let G := GaussianEulerExponentialSubstitutionNamedKernel.exponentF L
  have hv := GaussianEulerPositivePowerChartLogarithm.logarithm_regular e f d h Q S E T a b hs.andE₂
  have hl := GaussianPositiveRationalLogarithm.name_regular d h hs.andE₂.andE₁.andE₂.andE₁
  have ht := GaussianPositiveRationalLogarithm.name_regular a b hs.andE₂.andE₂.andE₂.andE₁
  have hx : Γ ⊢[PRAAx] pointCN scaleF x := negative_fast _ _
    (GaussianEulerExponentialSubstitutionNamedKernel.linear_regular _ _ _ _ hl)
  have hy : Γ ⊢[PRAAx] pointCN G y :=
    GaussianEulerExponentialSubstitutionNamedKernel.exponent_regular _ _ _ _ hv
  have hu : Γ ⊢[PRAAx] pointCN originalExponentF u := add_fast _ _ _ _
    (GaussianEulerExponentialSubstitutionNamedKernel.linear_regular _ _ _ _ ht)
    (negative_fast _ _ (GaussianEulerPositivePowerChart.name_regular e f d h Q S E T a b hs.andE₂))
  exact GaussianGammaFoldedApproximantBalance.exponential_product_equivalent scaleF G originalExponentF
    (GaussianNameBounds.U scaleF x) (GaussianNameBounds.U G y) (GaussianNameBounds.U originalExponentF u) x y u
    (exponential_input _ _ hx) (exponential_input _ _ hy) (exponential_input _ _ hu)
    (original_transformed_exponent z B e f d h Q S E T a b hs)

theorem actual_original_power_scaling_kernel_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 12
      (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)
        (var 8) (var 9) (var 10) (var 11) ⟶ crossEquivalent productF originalF
        (productData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 10) (var 11))
        (originalData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 7) (var 10) (var 11))) :=
  closeUniv 12 (.impI (original_transformed_kernel _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerPowerScalingKernel

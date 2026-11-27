import IPRADerivations.Analysis.Gamma.Zeta.Dirichlet.GaussianGammaZetaDirichletReciprocalRow
import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.Logarithms.GaussianEulerPowerChartRationalPowers
import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.GaussianEulerPositivePowerChartOrder
import IPRADerivations.Analysis.Gamma.HalfInteger.SquareRoots.GaussianGammaHalfSqrtBrackets
import IPRADerivations.Analysis.Stirling.Expansions.OddSeries.GaussianStirlingOddCoefficients

/-!
# Squared modulus of the Dirichlet row power

The certified parameter z denotes s-1. On reciprocal times in (0,1],
the original power t^(s-1) has squared norm bounded above by t^(2/A)
when Re(s-1) is at least 1/A.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaDirichletPowerOrder

open_ipra
open GaussianEulerLowerPowerCoefficients (realLower amplification)
open GaussianEulerLowerPowerOrder (inputF expF leftData leftExpData radius product_input)
open GaussianEulerUpperPowerCoefficients (realMultiplier real_multiplier_axis)
open GaussianEulerUpperPowerCompatibility (squareF squareData)
open GaussianEulerPositivePowerChart (argument)
open GaussianEulerIntegrandName (coefficient powerF powerData powerExponentF powerExponentData powerRadius)
open GaussianGammaEulerHeadShift (shifted)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm)
open GaussianNamedPositiveExponentialOrder (sampleOrder realOrder)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (ofGaussian qadd)
open GaussianRationalMetric (bounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "S" => GaussianEulerIntegralGammaIdentification.source
local notation "H" => GaussianHarmonicLogarithmName.nameF
local notation "O" => GaussianEulerLowerPowerOrder.source
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

theorem shifted_source (z R B A : PTm n) (h : Γ ⊢[PRAAx] S z R B A) :
    Γ ⊢[PRAAx] S (shifted z B) (R+one) B A := by
  have hB := h.andE₁.andE₂.andE₁.andE₁
  have hA := h.andE₁.andE₁
  have shiftedDisk := GaussianGammaEulerShiftLimit.shifted_bound z R B h.andE₁.andE₂.andE₁.andE₂
  have real := GaussianEulerBetaProductValue.shifted_source z B A
    (.andI hB (.andI hA h.andE₁.andE₂.andE₂))
  exact .andI (.andI hA (.andI (.andI hB shiftedDisk) real.andE₂.andE₂))
    (le_trans h.andE₂ (le_add_right R one))

private theorem coefficient_order (z R B A : PTm n) (h : Γ ⊢[PRAAx] S z R B A) :
    Γ ⊢[PRAAx] RationalArgmin.rationalLE (fstT (fraction one A)) (fstT (coefficient (shifted z B) B)) := by
  have hB := h.andE₁.andE₂.andE₁.andE₁
  have hA := h.andE₁.andE₁
  have e := congrFst (GaussianEulerPositiveScalingConstant.shifted_coefficient z B hB)
  have order := RationalArithmetic.order_of_representations (fstT (fraction one A)) (fstT (ofGaussian z B))
    (ZT.ofNat one) (ComplexLogarithmRemainder.re z) A B
    (GaussianGammaHalfSqrtBrackets.fraction_first_represents one A hA)
    (GaussianRationalHorner.ofGaussian_represents z B hB).andE₁ hA hB
  have margin : Γ ⊢[PRAAx] zle (ZT.ofNat one*ZT.ofNat B) (ComplexLogarithmRemainder.re z*ZT.ofNat A) :=
    PolynomialBisection.zle_congr (by simp only [ZT.toZ_mul,ZT.toZ_ofNat]; ipra_simps; try ring)
      (by simp only [ZT.toZ_mul]; ring) h.andE₁.andE₂.andE₂
  exact RationalArgmin.rationalLE_congr (.eqRefl _) e.eqSymm (order margin)

private theorem ref_multiplier (A : PTm n) (hA : Γ ⊢[PRAAx] le one A) :
    Γ ⊢[PRAAx] realMultiplier (argument one A) A ≐ fraction two A := by
  let q := fraction one A
  have co := GaussianEulerPositivePowerChart.coefficient_exact one A hA
  have qa := (GaussianEulerPositivePowerChartOrder.fraction_positive one A hA).andE₁
  have e := RationalGaussianEmbedding.canonical_axis_roundtrip q
    (GaussianRationalHorner.ofGaussian_canonical _ _ hA) qa
  have fixed := (GaussianRationalConjugation.point_congr e.eqSymm).eqTrans
    ((GaussianRationalConjugation.point_embed (fstT q)).eqTrans e)
  have doubled : Γ ⊢[PRAAx] fraction (one+one) A ≐ fraction two A := by
    simpa only [GaussianPositiveRationalLogarithm.subst_fraction,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      using Prf.eqCongr1 (fraction (var 0) (Syn.shift A)) (by ipra_ring : Γ ⊢[PRAAx] one+one ≐ two)
  exact (GaussianRationalSyntheticDivision.qadd_congr co ((GaussianRationalConjugation.point_congr co).eqTrans fixed)).eqTrans
    ((GaussianStirlingOddCoefficients.fraction_add_same one one A hA).eqTrans doubled)

private def rightData (R A a b : PTm n) : PTm n :=
  GaussianEulerPositivePowerChartOrder.inputData two A (amplification (R+one)) a b

private theorem sample_order_at (p z R B A a b : PTm n) (h : Γ ⊢[PRAAx] S z R B A)
    (ht : Γ ⊢[PRAAx] le a b) :
    Γ ⊢[PRAAx] RationalArgmin.rationalLE
      (fstT (ap2 inputF p (leftData (shifted z B) (R+one) B a b))) (fstT (ap2 inputF p (rightData R A a b))) := by
  let W := amplification (R+one)
  let t := GaussianHarmonicLogarithmName.sample (GaussianBoundedConstantProductName.clock p W) a b
  let c := realMultiplier (shifted z B) B
  let d := fraction two A
  let x := GaussianHarmonicLogarithmName.data a b
  have original := coefficient_order z R B A h
  have ref := GaussianEulerPositivePowerChart.coefficient_exact one A h.andE₁.andE₁
  have coeff := RationalArgmin.rationalLE_congr (congrFst ref).eqSymm (.eqRefl _) original
  have double := GaussianRationalSyntheticBounds.add_monotone _ _ _ _ coeff coeff
  have lhs := (congrFst (ref_multiplier (Γ := Γ) A h.andE₁.andE₁)).eqSymm.eqTrans
    (GaussianEulerUpperPowerCoefficients.real_multiplier_scalar (argument one A) A)
  have rhs := GaussianEulerUpperPowerCoefficients.real_multiplier_scalar (Γ := Γ) (shifted z B) B
  have order := RationalArgmin.rationalLE_congr lhs.eqSymm rhs.eqSymm double
  have scaled := RationalArithmetic.multiply_antitone (fstT t) (fstT d) (fstT c)
    (GaussianEulerLowerPowerCoefficients.harmonic_sample_nonpositive _ a b ht) order
  have axis := (GaussianHarmonicLogarithmName.sample_real (Γ := Γ) (GaussianBoundedConstantProductName.clock p W) a b).andE₂
  have value (u : PTm n) : Γ ⊢[PRAAx]
      fstT (ap2 inputF p (GaussianBoundedConstantProductName.data W u x)) ≐ RationalArithmetic.multiply (fstT t) (fstT u) :=
    (congrFst (GaussianBoundedConstantProductName.sample_at H p W u x)).eqTrans
      ((GaussianPositiveExponentialProduct.real_product u t axis).eqTrans (RationalAlgebra.multiply_commutative _ _))
  exact RationalArgmin.rationalLE_congr (value c).eqSymm (value d).eqSymm scaled

theorem original_square_order (z R B A a b : PTm n) (h : Γ ⊢[PRAAx] S z R B A)
    (hl : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b) (ht : Γ ⊢[PRAAx] le a b) :
    Γ ⊢[PRAAx] realOrder squareF powerF (squareData (shifted z B) B a b) (powerData (argument two A) A a b) := by
  let W := amplification (R+one)
  let X := leftData (shifted z B) (R+one) B a b
  let Y := rightData R A a b
  let E := radius (R+one) b
  have hA := h.andE₁.andE₁
  have left : Γ ⊢[PRAAx] O (shifted z B) (R+one) B A a b :=
    .andI (shifted_source z R B A h).andE₁ (.andI hl ht)
  have hW : Γ ⊢[PRAAx] le two (W*A) := by
    have hM : Γ ⊢[PRAAx] le two W := le_of_eq_add (d := two*(R+two)) (by unfold W amplification; ipra_ring)
    exact le_trans hM (le_congr (one_mul W) (mul_comm A W) (mul_le_mul_right W hA))
  have bound := GaussianEulerPositivePowerChartOrder.coefficient_bound two A W hA hW
  have ix := product_input W (realMultiplier (shifted z B) B) a b left.andE₂
    (GaussianEulerLowerPowerCoefficients.real_multiplier_bound _ _ _ _ left.andE₁)
  have iy := product_input W (fraction two A) a b (.andI hl ht) bound
  have input_order : Γ ⊢[PRAAx] sampleOrder inputF inputF X Y := by
    refine .allI ?_
    let sh (t : PTm n) := Syn.shift t
    have hs : Γ.map Fm.shift ⊢[PRAAx] S (sh z) (sh R) (sh B) (sh A) := by simpa [Fm.shift,sh,Syn.shift] using h.shift
    have tt : Γ.map Fm.shift ⊢[PRAAx] le (sh a) (sh b) := by simpa [Fm.shift,sh,Syn.shift] using ht.shift
    simpa [sampleOrder,X,Y,rightData,sh,Syn.shift,one,two] using
      sample_order_at (var 0) (sh z) (sh R) (sh B) (sh A) (sh a) (sh b) hs tt
  have order := GaussianSignedNameExponentialOrder.original_signed_name_order inputF inputF E X Y ix iy
    (GaussianEulerUpperPowerOrder.product_real_samples W (realMultiplier (shifted z B) B) a b (real_multiplier_axis _ _))
    (GaussianEulerPositivePowerChartOrder.input_real_samples two A W a b hA) input_order
  have right := GaussianExponentialRadiusIndependence.independent_radii_proper inputF powerExponentF E
    (powerRadius (argument two A) A a b) Y (powerExponentData (argument two A) A a b) iy
    (GaussianEulerIntegrandName.power_input _ _ _ _ (.andI hA hl))
    (GaussianEulerPositivePowerChartOrder.input_cross two A W a b hA hW hl)
  exact GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _
    (GaussianEulerLowerPowerComparison.original_power_square _ _ _ _ _ _ left) right order

theorem actual_original_Dirichlet_power_squared_order_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (S (var 0) (var 1) (var 2) (var 3) ⟶ GaussianPositiveRationalLogarithm.source (var 4) (var 5) ⟶
      le (var 4) (var 5) ⟶ realOrder squareF powerF
      (squareData (shifted (var 0) (var 2)) (var 2) (var 4) (var 5))
      (powerData (argument two (var 3)) (var 3) (var 4) (var 5))) :=
  closeUniv 6 (.impI (.impI (.impI (original_square_order _ _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianGammaZetaDirichletPowerOrder

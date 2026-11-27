import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.PowerEstimates.GaussianGaussMultiplicationPowerPerturbation
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Recurrence.GaussianNamedGammaHalfShift
import IPRADerivations.Analysis.Euler.VerticalBounds.GaussianEulerVerticalRealSamples
import IPRADerivations.Analysis.Exponential.Names.Identities.GaussianExponentialRealPart
import IPRADerivations.Analysis.Names.FiniteOperations.Products.Bounds.GaussianNamedBoundedProductObservation

/-!
# The real half-power in the Gauss multiplication formula

The logarithm is the original positive rational logarithm at (1,m).
The half-power uses the conjugate square at the quarter exponent, so
each rational sample is real and nonnegative. Its square is the literal
reciprocal of m, and its product with the original Gauss power has
exponent 1/2 - mz.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGaussMultiplicationHalfPower

open_ipra
open ComplexLogarithmRemainder (oneCode scale)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaEulerShift (constant_sum_cross)
open GaussianGammaFiniteApproximantName (exponential_input exponentialInputData)
open GaussianGaussMultiplicationPowerPerturbation (limitData)
open GaussianGaussMultiplicationPowerRate (powerF limitLogData limit_log_regular limit_power_input multiplier)
open GaussianGammaWeierstrassApproximant (constant_data_cross)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianPositiveRationalLogarithm (logF)
open GaussianRationalHorner (canonical ofGaussian qadd qmul positive_product represents_congr canonical_unique)
open GaussianRationalMetric (qsub)
open GaussianRationalSyntheticDivision (qone qone_canonical qadd_congr qmul_congr)
open GaussianSignedNameExponentialOrder (realSamples)
open RationalGaussianEmbedding (axis)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def exponentF : PR 2 := multiplyF constantF logF
def exponentData (c m : PTm n) : PTm n := multiplyData constantF logF c (limitLogData m)
def ratioPowerF : PR 2 := GaussianRadiusExponentialName.nameF exponentF
def ratioPowerData (c m : PTm n) : PTm n := exponentialInputData exponentF (exponentData c m)

def halfCoefficient : PTm n := ofGaussian oneCode two
def quarterCoefficient : PTm n := ofGaussian oneCode (num 4)
def regroupedCoefficient (z B m : PTm n) : PTm n := qsub (ofGaussian (scale m z) B) halfCoefficient

def halfF : PR 2 := GaussianExponentialRealPart.squareF ratioPowerF
def halfData (m : PTm n) : PTm n := GaussianExponentialRealPart.squareData ratioPowerF (ratioPowerData quarterCoefficient m)
def regroupedData (z B m : PTm n) : PTm n := ratioPowerData (regroupedCoefficient z B m) m

ipra_subst exponentData
ipra_subst ratioPowerData [exponentialInputData]
ipra_subst halfData [quarterCoefficient]
ipra_subst regroupedData [regroupedCoefficient, halfCoefficient]

theorem exponent_regular (c m : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] pointCN exponentF (exponentData c m) :=
  multiply_fast constantF logF c (limitLogData m) (constant_regular c) (limit_log_regular m hm)

theorem ratio_power_regular (c m : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] pointCN ratioPowerF (ratioPowerData c m) :=
  GaussianRadiusExponentialName.name_regular _ _ _ (exponential_input _ _ (exponent_regular c m hm))

theorem coefficient_congr (c d m : PTm n) (hm : Γ ⊢[PRAAx] le one m) (he : Γ ⊢[PRAAx] c ≐ d) :
    Γ ⊢[PRAAx] crossEquivalent ratioPowerF ratioPowerF (ratioPowerData c m) (ratioPowerData d m) := by
  have hl := limit_log_regular m hm
  exact GaussianExponentialRadiusIndependence.independent_radii_proper exponentF exponentF _ _ _ _
    (exponential_input _ _ (exponent_regular c m hm)) (exponential_input _ _ (exponent_regular d m hm))
    (multiply_cross constantF constantF logF logF c d (limitLogData m) (limitLogData m)
      (constant_regular c) (constant_regular d) hl hl (constant_data_cross c d he) (cross_refl _ _ hl))

theorem ratio_power_sum (c d m : PTm n) (hm : Γ ⊢[PRAAx] le one m) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF ratioPowerF ratioPowerF) ratioPowerF
      (multiplyData ratioPowerF ratioPowerF (ratioPowerData c m) (ratioPowerData d m)) (ratioPowerData (qadd c d) m) := by
  let L := limitLogData m
  have hc := constant_regular (Γ := Γ) c
  have hd := constant_regular (Γ := Γ) d
  have hl := limit_log_regular m hm
  have split := GaussianNameRingLaws.right_distributive constantF constantF logF c d L hc hd hl
  have sum := multiply_cross (addF constantF constantF) constantF logF logF (addData c d) (qadd c d) L L
    (add_fast _ _ _ _ hc hd) (constant_regular _) hl hl (constant_sum_cross c d) (cross_refl _ _ hl)
  exact GaussianGammaFoldedApproximantBalance.exponential_product_equivalent exponentF exponentF exponentF _ _ _ _ _ _
    (exponential_input _ _ (exponent_regular c m hm)) (exponential_input _ _ (exponent_regular d m hm))
    (exponential_input _ _ (exponent_regular (qadd c d) m hm))
    (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ split) sum)

private theorem double_reciprocal (D : PTm n) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    qadd (ofGaussian oneCode (D*two)) (ofGaussian oneCode (D*two)) ≐ ofGaussian oneCode D := by
  let E := D*two
  have hE : Γ ⊢[PRAAx] le one E := positive_product _ _ hD RationalAlgebra.two_positive
  have a := GaussianRationalHorner.ofGaussian_represents (Γ := Γ) oneCode E hE
  have b := GaussianRationalHorner.represents_rescale _ oneCode D two
    (GaussianRationalHorner.ofGaussian_represents (Γ := Γ) oneCode D hD)
  have both := GaussianRationalHorner.qadd_represents _ _ oneCode oneCode E hE a a
  have eq : Γ ⊢[PRAAx] GaussianRootAlgebra.equal
      (ComplexLogarithmRemainder.add oneCode oneCode) (scale two oneCode) := by
    apply GaussianRootAlgebra.equal_of_values <;>
      simp only [GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,GaussianRootAlgebra.re_scale,
        GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one] <;> ipra_simps <;> ring
  exact canonical_unique _ _ _ E (GaussianRationalHorner.qadd_canonical _ _)
    (GaussianRationalHorner.ofGaussian_canonical _ _ hD) hE
    (represents_congr (.eqRefl _) eq (.eqRefl _) both) b

private theorem double_quarter : Γ ⊢[PRAAx] qadd (quarterCoefficient : PTm n) quarterCoefficient ≐ halfCoefficient := by
  have e : Γ ⊢[PRAAx] ((two : PTm n)*two) ≐ num 4 := by ipra_ring
  have c : Γ ⊢[PRAAx] ofGaussian oneCode (two*two) ≐ (quarterCoefficient : PTm n) := by
    have raw := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (ofGaussian oneCode (var 0) : PTm 1)
      (σ := ![two*two]) (σ' := ![num 4]) (fun i => by fin_cases i; exact e)
    simpa [quarterCoefficient] using raw
  exact (qadd_congr c.eqSymm c.eqSymm).eqTrans (double_reciprocal two RationalAlgebra.two_positive)

private theorem double_half : Γ ⊢[PRAAx] qadd (halfCoefficient : PTm n) halfCoefficient ≐ qone := by
  have c : Γ ⊢[PRAAx] ofGaussian oneCode (one*two) ≐ (halfCoefficient : PTm n) := by
    have raw := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (ofGaussian oneCode (var 0) : PTm 1)
      (σ := ![one*two]) (σ' := ![two]) (fun i => by fin_cases i; exact one_mul two)
    simpa [halfCoefficient] using raw
  have o : Γ ⊢[PRAAx] (ofGaussian oneCode one : PTm n) ≐ qone := by
    exact canonical_unique _ _ oneCode one (GaussianRationalHorner.ofGaussian_canonical _ _ (le_refl one)) qone_canonical
      (le_refl one) (GaussianRationalHorner.ofGaussian_represents _ _ (le_refl one))
      (represents_congr (.eqRefl _) (by
        apply GaussianRootAlgebra.equal_of_values <;>
          simp only [GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_one,
            GaussianRootAlgebra.im_one] <;> ipra_simps <;> ring)
        (.eqRefl _) (GaussianRationalReciprocal.qone_represents_scaled one))
  exact (qadd_congr c.eqSymm c.eqSymm).eqTrans ((double_reciprocal one (le_refl one)).eqTrans o)

private theorem power_one (m : PTm n) (hm : Γ ⊢[PRAAx] le one m) : Γ ⊢[PRAAx]
    crossEquivalent ratioPowerF GaussianPositiveRationalLogarithm.expF (ratioPowerData qone m)
      (GaussianPositiveRationalLogarithm.expData one m) := by
  have hL := limit_log_regular m hm
  let L := limitLogData m
  let F := GaussianNameRingLaws.oneF
  have c : Γ ⊢[PRAAx] crossEquivalent constantF F qone L := by
    apply GaussianNameConjugation.equal_samples_cross _ _ _ _ (constant_regular _) (GaussianNameRingLaws.one_fast _)
    refine .allI ?_
    simpa only [Syn.shift,GaussianRationalSyntheticDivision.subst_qone] using
      (constant_at (var 0) qone).eqTrans (GaussianNameRingLaws.one_at (var 0) (Syn.shift L)).eqSymm
  have first := multiply_cross constantF F logF logF qone L L L (constant_regular _)
    (GaussianNameRingLaws.one_fast _) hL hL c (cross_refl _ _ hL)
  have eq : Γ ⊢[PRAAx] crossEquivalent exponentF logF (exponentData qone m) L :=
    cross_trans _ _ _ _ _ _ first (GaussianNameRingLaws.multiply_one_left logF L hL)
  exact GaussianExponentialRadiusIndependence.independent_radii_proper exponentF logF _ _ _ _
    (exponential_input _ _ (exponent_regular qone m hm))
    (GaussianPositiveRationalLogarithm.exponential_input one m (.andI (le_refl one) hm)) eq

theorem half_regular (m : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] pointCN halfF (halfData m) :=
  GaussianExponentialRealPart.square_regular _ _ (ratio_power_regular quarterCoefficient m hm)

theorem half_sample_positive (m p : PTm n) :
    Γ ⊢[PRAAx] GaussianPositiveRealArithmetic.positive (ap2 halfF p (halfData m)) :=
  GaussianExponentialRealPart.square_sample_positive _ _ _

theorem half_sample_canonical (m p : PTm n) : Γ ⊢[PRAAx] canonical (ap2 halfF p (halfData m)) :=
  GaussianNameArithmetic.multiply_canonical _ _ _ _ _

theorem half_axis_at (m p : PTm n) : Γ ⊢[PRAAx] axis (ap2 halfF p (halfData m)) :=
  (half_sample_positive m p).andE₁

theorem half_nonnegative_samples (m : PTm n) : Γ ⊢[PRAAx] .all
    (canonical (ap2 halfF (var 0) (Syn.shift (halfData m))) ⋏
      GaussianPositiveRealArithmetic.positive (ap2 halfF (var 0) (Syn.shift (halfData m)))) := by
  refine .allI ?_
  simpa [Syn.shift] using Prf.andI (half_sample_canonical (Γ := Γ.map Fm.shift) (Syn.shift m) (var 0))
    (half_sample_positive (Γ := Γ.map Fm.shift) (Syn.shift m) (var 0))

theorem exponent_real (c m : PTm n) (hc : Γ ⊢[PRAAx] axis c) : Γ ⊢[PRAAx] realSamples exponentF (exponentData c m) := by
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let x := limitLogData (Syn.shift m)
  let p : PTm (n+1) := var 0
  let q := GaussianNamedBoundedProductObservation.clock constantF logF p (Syn.shift c) x
  have h : Δ ⊢[PRAAx] axis (Syn.shift c) := by simpa [Δ,Fm.shift,Syn.shift] using hc.shift
  have eq := (GaussianNamedBoundedProductObservation.name_at (Γ := Δ) constantF logF p (Syn.shift c) x).eqTrans
    (qmul_congr (constant_at q (Syn.shift c)) (.eqRefl _))
  have a := RationalGaussianEmbedding.axis_multiply _ _ h
    (GaussianPositiveRationalLogarithm.sample_axis (Γ := Δ) q one (Syn.shift m))
  simpa [realSamples,Syn.shift,exponentF,exponentData,p,x] using
    Prf.andI (GaussianRationalHorner.canonical_congr eq (GaussianRationalHorner.qmul_canonical _ _))
      (RationalGaussianEmbedding.axis_congr eq.eqSymm a)

theorem half_coefficient_axis : Γ ⊢[PRAAx] axis (halfCoefficient : PTm n) :=
  (GaussianPositiveExponentialTermBound.actual_positive_fraction one two RationalAlgebra.two_positive).andE₁

private theorem quarter_conjugate (m : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] crossEquivalent (GaussianNameConjugation.nameF ratioPowerF) ratioPowerF
      (ratioPowerData quarterCoefficient m) (ratioPowerData quarterCoefficient m) := by
  let x := ratioPowerData quarterCoefficient m
  have reg := ratio_power_regular quarterCoefficient m hm
  have re := GaussianEulerVerticalRealSamples.original_exponential_real_samples (Γ := Γ) exponentF
    (GaussianNameBounds.U exponentF (exponentData quarterCoefficient m)) (exponentData quarterCoefficient m)
    (exponent_real quarterCoefficient m (GaussianPositiveExponentialTermBound.actual_positive_fraction one (num 4) (by ipra_le 3)).andE₁)
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _
    (GaussianNameConjugation.regular _ _ reg) reg
  refine .allI ?_
  let y := Syn.shift x
  have hR : Γ.map Fm.shift ⊢[PRAAx] realSamples ratioPowerF y := by
    simpa [Fm.shift,Syn.shift,x,y,ratioPowerF,ratioPowerData,exponentialInputData,quarterCoefficient] using re.shift
  let a := ap2 ratioPowerF (var 0) y
  have ri := GaussianSignedNameExponentialOrder.real_sample_at ratioPowerF y (var 0) hR
  have e := RationalGaussianEmbedding.canonical_axis_roundtrip a ri.andE₁ ri.andE₂
  exact (GaussianNameConjugation.sample_at ratioPowerF (var 0) y).eqTrans
    ((GaussianRationalConjugation.point_congr e.eqSymm).eqTrans ((GaussianRationalConjugation.point_embed _).eqTrans e))

theorem half_exponential (m : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] crossEquivalent halfF ratioPowerF (halfData m) (ratioPowerData halfCoefficient m) := by
  let x := ratioPowerData quarterCoefficient m
  let F := ratioPowerF
  let C := GaussianNameConjugation.nameF F
  have reg := ratio_power_regular quarterCoefficient m hm
  have first := multiply_cross F F C F x x x x reg reg (GaussianNameConjugation.regular _ _ reg) reg
    (cross_refl _ _ reg) (quarter_conjugate m hm)
  exact cross_trans _ _ _ _ _ _ first (cross_trans _ _ _ _ _ _
    (ratio_power_sum quarterCoefficient quarterCoefficient m hm) (coefficient_congr _ _ m hm double_quarter))

theorem half_square (m : PTm n) (hm : Γ ⊢[PRAAx] le one m) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF halfF halfF) constantF (multiplyData halfF halfF (halfData m) (halfData m))
      (GaussianPositiveRationalLogarithm.fraction one m) := by
  let x := halfData m
  let y := ratioPowerData halfCoefficient m
  have hx := half_regular m hm
  have hy := ratio_power_regular halfCoefficient m hm
  have first := multiply_cross halfF ratioPowerF halfF ratioPowerF x y x y hx hy hx hy
    (half_exponential m hm) (half_exponential m hm)
  exact cross_trans _ _ _ _ _ _ first (cross_trans _ _ _ _ _ _ (ratio_power_sum halfCoefficient halfCoefficient m hm)
    (cross_trans _ _ _ _ _ _ (coefficient_congr _ _ m hm double_half) (cross_trans _ _ _ _ _ _ (power_one m hm)
      (GaussianPositiveRationalLogarithm.exponential_fraction one m (.andI (le_refl one) hm)))))

theorem regrouped_coefficient (z B m : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] qadd (multiplier z B m) halfCoefficient ≐ regroupedCoefficient z B m := by
  let E := B*two
  let Z := scale two (scale m z)
  let C := scale E oneCode
  let H := scale B oneCode
  let x := ofGaussian (scale m z) B
  have hE : Γ ⊢[PRAAx] le one E := positive_product _ _ hB RationalAlgebra.two_positive
  have r := GaussianRationalHorner.represents_rescale x (scale m z) B two
    (GaussianRationalHorner.ofGaussian_represents _ _ hB)
  have q := GaussianRationalReciprocal.qone_represents_scaled (Γ := Γ) E
  have h : Γ ⊢[PRAAx] GaussianRationalHorner.represents halfCoefficient H E :=
    represents_congr (.eqRefl _) (GaussianRootAlgebra.equal_refl _) (mul_comm _ _)
      (GaussianRationalHorner.represents_rescale _ oneCode two B
        (GaussianRationalHorner.ofGaussian_represents _ _ RationalAlgebra.two_positive))
  have l := GaussianRationalHorner.qadd_represents (multiplier z B m) halfCoefficient
    (GaussianRootAlgebra.sub Z C) H E hE (GaussianRationalMetric.qsub_represents x qone Z C E hE r q) h
  have j := GaussianRationalMetric.qsub_represents x halfCoefficient Z H E hE r h
  have e : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (ComplexLogarithmRemainder.add (GaussianRootAlgebra.sub Z C) H)
      (GaussianRootAlgebra.sub Z H) := by
    apply GaussianRootAlgebra.equal_of_values <;>
      simp only [GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,GaussianRootAlgebra.re_sub,
        GaussianRootAlgebra.im_sub,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,
        GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one,C,H,E,IPRA.Q.mk_mul,map_mul] <;> ipra_simps <;> ring
  exact canonical_unique _ _ _ E (GaussianRationalHorner.qadd_canonical _ _) (GaussianRationalMetric.qsub_canonical _ _)
    hE (represents_congr (.eqRefl _) e (.eqRefl _) l) j

theorem original_limit_power (z R B m : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hB : Γ ⊢[PRAAx] le one B) (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) :
    Γ ⊢[PRAAx] crossEquivalent powerF ratioPowerF (limitData z R B m) (ratioPowerData (multiplier z B m) m) :=
  GaussianExponentialRadiusIndependence.independent_radii_proper GaussianGaussMultiplicationPowerRate.exponentF exponentF
    _ _ _ _ (limit_power_input z R B m hm hB hz)
    (exponential_input _ _ (exponent_regular _ _ hm))
    (GaussianBoundedConstantProductName.ordinary_product_identity logF _ _ _
      (.andI (limit_log_regular m hm) (GaussianGaussMultiplicationPowerRate.multiplier_bound z R B m hm hB hz)))

theorem regroup (z R B m : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hB : Γ ⊢[PRAAx] le one B) (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF powerF halfF) ratioPowerF (multiplyData powerF halfF (limitData z R B m) (halfData m))
      (regroupedData z B m) := by
  let c := multiplier z B m
  have w := GaussianRadiusExponentialName.name_regular _ _ _ (limit_power_input z R B m hm hB hz)
  have first := multiply_cross powerF ratioPowerF halfF ratioPowerF (limitData z R B m) (ratioPowerData c m)
    (halfData m) (ratioPowerData halfCoefficient m) w (ratio_power_regular c m hm) (half_regular m hm)
    (ratio_power_regular halfCoefficient m hm) (original_limit_power z R B m hm hB hz) (half_exponential m hm)
  exact cross_trans _ _ _ _ _ _ first (cross_trans _ _ _ _ _ _ (ratio_power_sum c halfCoefficient m hm)
    (coefficient_congr _ _ m hm (regrouped_coefficient z B m hB)))

end LeanProofs.IPRA.Analysis.GaussianGaussMultiplicationHalfPower

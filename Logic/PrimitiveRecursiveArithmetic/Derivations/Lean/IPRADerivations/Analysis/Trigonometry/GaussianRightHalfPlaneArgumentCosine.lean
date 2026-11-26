import IPRADerivations.Analysis.RationalArithmetic.Complex.GaussianRightHalfPlaneArgumentAxis
import IPRADerivations.Analysis.Exponential.RightHalfPlane.GaussianRightHalfPlaneArgumentExponential
import IPRADerivations.Analysis.Exponential.Estimates.GaussianExponentialLinearRemainder
import IPRADerivations.Analysis.RationalArithmetic.Complex.GaussianCoordinateRadius
import IPRADerivations.Analysis.RationalArithmetic.Representations.RationalRepresentedUpper

/-!
# Exact nonnegative cosine observations for the small argument

Every actual arctangent observation in the small chart has modulus at
most one after halving. Its real coordinate is zero. The linear
remainder estimate for the actual exponential polynomial puts its
real coordinate within one of one, with no auxiliary limit error.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneArgumentCosine

open_ipra
open ComplexLogarithmRemainder (oneCode normSq normSq_eval eval_re_code eval_im_code)
open GaussianRationalHorner (qadd qmul_canonical ofGaussian_represents positive_product)
open GaussianRationalMetric (bounded bounded_of_cleared)
open GaussianRationalReciprocal (qone bounded_product bound_congr)
open GaussianRightHalfPlaneArgument (smallF smallData)
open GaussianRightHalfPlaneArgumentAxis (small_axis)
open GaussianRightHalfPlaneArgumentExponential (smallExpData)
open RationalGaussianEmbedding (scalarZero scalarOne scalar_zero_represents)
open RationalValueBounds (upper upper_of_radius)
open RationalRepresentedUpper (left right to_signed from_signed)
open RationalSupMetric (numeratorOf denominatorOf)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "atanF" => GaussianArctangentPartialQuadrature.nameF
local notation "atData" => GaussianArctangentPartialQuadrature.data
local notation "H" => GaussianRightHalfPlaneArgument.half

private theorem half_bound : Γ ⊢[PRAAx] bounded (H : PTm n) one two := by
  have hd : Γ ⊢[PRAAx] le one two := le_succ_self one
  have hn : Γ ⊢[PRAAx] normSq (oneCode : PTm n) ≐ one := by
    apply deriveNat
    rw [normSq_eval]
    simp only [oneCode,eval_re_code,eval_im_code,ZT.toZ_ofNat]
    ipra_simps
    ring
  apply bounded_of_cleared _ _ two one two hd hd (ofGaussian_represents _ _ hd)
  exact le_congr (congrMul (.eqRefl _) hn).eqSymm (by ipra_ring)
    (le_congr (by ipra_ring) (.eqRefl _) (le_refl (two*two)))

theorem small_unit_bound (j A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le B A) :
    Γ ⊢[PRAAx] bounded (ap2 smallF j (smallData A B)) one one := by
  let l := GaussianBoundedConstantProductName.clock j one
  have b := bounded_product H (ap2 atanF l (atData B A)) one two two one
    (le_succ_self one) (le_refl one) half_bound (GaussianArctangentPartialExponential.argument_bound l B A hA hB)
  have e := GaussianBoundedConstantProductName.sample_at (Γ := Γ) atanF j one H (atData B A)
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (positive_product _ _ (le_succ_self one) (le_refl one))
    (le_refl one) (le_of_eq_add (d := zero) (by ipra_ring))
    (bound_congr e.eqSymm (.eqRefl _) (.eqRefl _) b)

private theorem index_positive (p : PTm n) : Γ ⊢[PRAAx] le one (GaussianRadiusExponentialName.index two p) := by
  let K := GaussianRadiusExponentialName.index two p
  let c := GaussianRationalExponentialTail.cutoff two (p+num 4)
  have e : Γ ⊢[PRAAx] succ K ≐ c := GaussianRationalExponentialTail.last_successor two (p+num 4)
  have h : Γ ⊢[PRAAx] le two c := by
    unfold c GaussianRationalExponentialTail.cutoff ExponentialTail.Nt
    ipra_le Groth.ι (Q.mk Γ p)+18
  exact (succ_monus_succ one K).eqSymm.eqTrans (le_congr (.eqRefl two) e.eqSymm h)

private theorem one_real : Γ ⊢[PRAAx] fstT (qone : PTm n) ≐ scalarOne :=
  ((congrFst RationalGaussianEmbedding.embed_one).eqSymm.eqTrans (fst_pair _ _)).eqTrans
    (RationalNormalForm.normalize_fixed_point _ (RationalNormalForm.normalize_well_formed _ _ (le_refl one)))

private theorem first_order_real (q : PTm n) (hq : Γ ⊢[PRAAx] fstT q ≐ scalarZero) :
    Γ ⊢[PRAAx] fstT (qadd qone q) ≐ scalarOne := by
  have eq : Γ ⊢[PRAAx] fstT (qadd qone q) ≐ RationalArithmetic.add (fstT qone) (fstT q) := fst_pair _ _
  have a : Γ ⊢[PRAAx] RationalArithmetic.add (fstT qone) (fstT q) ≐ RationalArithmetic.add scalarOne scalarZero :=
    RationalAlgebra.add_congr one_real hq
  exact eq.eqTrans (a.eqTrans (RationalReciprocalPowerTail.add_zero_right _
    (RationalNormalForm.normalize_well_formed _ _ (le_refl one))))

private theorem remove_one (r : PTm n) (h : Γ ⊢[PRAAx] upper scalarOne r one one) :
    Γ ⊢[PRAAx] upper scalarZero r zero one := by
  let Y := numeratorOf r
  let D := denominatorOf r
  have hr := RationalRepresentations.represents_self (Γ := Γ) r
  have ho : Γ ⊢[PRAAx] RationalArithmetic.represents scalarOne (ZT.ofNat one) one :=
    RationalIntegerNormalization.normalize_preserves_value _ _ (le_refl one)
  have signed := to_signed scalarOne r (ZT.ofNat one) Y one D one one ho hr h
  apply from_signed scalarZero r (ZT.ofNat zero) Y one D zero one (le_refl one)
    (RationalArgmin.denominator_positive r) (scalar_zero_represents one) hr
  have ee := zle_toZ signed
  apply zle_of_toZ (PolynomialBisection.slack (left (ZT.ofNat one) D one) (right Y one D one one))
  simp only [PolynomialBisection.slack,left,right,ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat] at ee ⊢
  ipra_simps
  linear_combination ee

theorem nonnegative_at (p A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le B A) :
    Γ ⊢[PRAAx] upper scalarZero
      (fstT (ap2 (GaussianRadiusExponentialName.nameF smallF) p (smallExpData A B))) zero one := by
  let j := GaussianRadiusExponentialName.inputPrecision two p
  let q := ap2 smallF j (smallData A B)
  let k := GaussianRadiusExponentialName.index two p
  let S := GaussianRationalPolynomialExponential.scalarSum q k
  let l := GaussianBoundedConstantProductName.clock j one
  have read := GaussianBoundedConstantProductName.sample_at (Γ := Γ) atanF j one H (atData B A)
  have can := GaussianRationalHorner.canonical_congr read (qmul_canonical H (ap2 atanF l (atData B A)))
  have dist := GaussianExponentialLinearRemainder.original_finite_linear_remainder q one one k
    (le_refl one) (le_refl one) (small_unit_bound j A B hA hB) can (index_positive p)
  have same : Γ ⊢[PRAAx] GaussianRationalMetric.distanceBounded (qadd qone q) S one one :=
    GaussianRationalDistanceOrder.distance_symmetric _ _ _ _ (le_refl one)
      (GaussianRationalDistanceOrder.distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (by ipra_ring) dist)
  have near := upper_of_radius _ _ _ _ (GaussianCoordinateRadius.coordinates _ _ _ _ (le_refl one) same).andE₁
  have first := RationalValueBounds.upper_congr (first_order_real q (small_axis j A B)) (.eqRefl _) (.eqRefl _) (.eqRefl _) near
  exact RationalValueBounds.upper_congr (.eqRefl _)
    (congrFst (GaussianRadiusExponentialName.sample_at smallF two p (smallData A B))).eqSymm (.eqRefl _) (.eqRefl _)
    (remove_one (fstT S) first)

theorem actual_small_right_half_plane_cosine_nonnegative_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((le one (var 0) ⋏ le (var 1) (var 0)) ⟶ upper scalarZero
      (fstT (ap2 (GaussianRadiusExponentialName.nameF smallF) (var 2) (smallExpData (var 0) (var 1)))) zero one) :=
  closeUniv 3 (.impI (nonnegative_at _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneArgumentCosine

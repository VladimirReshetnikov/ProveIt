import IPRADerivations.Analysis.Trigonometry.Cyclic.GaussianCyclicHalfAngleAgreement
import IPRADerivations.Analysis.Trigonometry.Cyclic.GaussianCyclicChordSquare

/-!
# Positive real cyclic sine observations on the first half-turn

Transport the original arctangent chord lower bound to the full
cyclic half-angle sampler. At an explicit cofinal precision its
embedded real observation is nonnegative.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianCyclicSinePositiveRows

open_ipra
open GaussianArctangentDivisionAngles (source coefficient)
open GaussianArctangentDivisionSinePositive (sine_lower exactSineData)
open GaussianCyclicHalfAngleAgreement (sine_divided_cross)
open GaussianCyclicHalfSineMargin (sineSample)
open GaussianCyclicChordSquare (realSine sine_error)
open GaussianNamedPositiveExponentialOrder (real_order_at)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianCoordinateRadius (coordinates)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (diagonal_at cross_to_diagonal cross_symm)
open GaussianRationalHorner (ofGaussian_represents scalar_congr positive_product)
open GaussianRationalL1 (rawGaussian rawDen raw_den_positive raw_represents)
open GaussianRationalDistanceOrder (distance_triangle_same)
open GaussianRootAlgebra (re_scale re_one)
open ComplexLogarithmRemainder (re)
open RationalGaussianEmbedding (scalarZero scalar_zero_represents)
open RationalValueBounds (upper upper_congr upper_mono upper_of_radius upper_triangle)
open RationalRepresentedUpper (left right to_signed from_signed)
open PolynomialBisection (zle_scale_cancel)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "D" => GaussianArctangentDivisionAngles.nameF

private theorem divided_sine_at (p r m x : PTm n) (h : Γ ⊢[PRAAx] source r m) :
    Γ ⊢[PRAAx] upper (fstT (coefficient r m)) (fstT (sineSample p r m x)) two (unit p) := by
  let a := coefficient r m
  let U := unit p
  let d := exactSineData r m x
  have hp := unit_positive (Γ := Γ) p
  have raw := upper_congr (congrFst (constant_at p a)) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (real_order_at constantF (GaussianNamedSineFromExponential.sineF D) a d p p (sine_lower r m x h))
  exact upper_mono _ _ _ _ _ _ (positive_product _ _ hp hp) raw (le_of_eq_add (d := zero) (by ipra_ring))

theorem first_half_upper (p r m x : PTm n) (h : Γ ⊢[PRAAx] source r m) :
    Γ ⊢[PRAAx] upper (fstT (coefficient r m)) (fstT (realSine p r m x)) (num 14) (unit p) := by
  let t := GaussianCyclicFullHalfAngle.sineSample p r m x
  let U := unit p
  let s := sineSample p r m x
  let q := realSine p r m x
  have hU := unit_positive (Γ := Γ) p
  have eq := cross_symm _ _ _ _ (sine_divided_cross r m x h)
  have near := diagonal_at _ _ _ _ p (cross_to_diagonal _ _ _ _ eq)
  have rest := sine_error p r m x (GaussianCyclicRootHalfAngle.cyclic_source r m h)
  have upper2 := upper_of_radius _ _ _ _ (coordinates s q (two+num 10) U hU
    (distance_triangle_same s t q two (num 10) U hU near rest)).andE₁
  have joined := upper_triangle _ _ _ _ _ _ _ (divided_sine_at p r m x h) upper2
  exact upper_mono _ _ _ _ _ _ (positive_product _ _ hU hU) joined
    (le_of_eq_add (d := zero) (by dsimp only [U]; ipra_ring))

theorem scalar_nonnegative_of_upper (r m q A U : PTm n)
    (hm : Γ ⊢[PRAAx] le one m) (hU : Γ ⊢[PRAAx] le one U)
    (h : Γ ⊢[PRAAx] upper (fstT (coefficient r m)) (fstT q) A U)
    (hEnough : Γ ⊢[PRAAx] le (A*m) ((two*r)*U)) :
    Γ ⊢[PRAAx] RationalArgmin.rationalLE scalarZero (fstT q) := by
  let E := rawDen q
  let b := rawGaussian q
  let z := re b
  let L := left (ZT.ofNat (two*r)) E U
  let R := right z m E A U
  have hE := raw_den_positive (Γ := Γ) q
  have tr : Γ ⊢[PRAAx] RationalArithmetic.represents (fstT (coefficient r m)) (ZT.ofNat (two*r)) m := by
    apply scalar_congr (.eqRefl _) ?_ (.eqRefl _) (ofGaussian_represents _ _ hm).andE₁
    apply ZT.derive
    simp only [re_scale,re_one,ZT.toZ_ofNat,mul_one]
  have sign : Γ ⊢[PRAAx] zle L R :=
    to_signed _ _ _ _ m E A U tr (raw_represents q).andE₁ h
  let d := monus (R.pos+L.neg) (L.pos+R.neg)
  let k := monus ((two*r)*U) (A*m)
  have ans : Γ ⊢[PRAAx] zle (left (ZT.ofNat zero) E one) (right z one E zero one) := by
    apply zle_scale_cancel (c := m*U) (positive_product _ _ hm hU)
    apply zle_of_toZ (d+E*k)
    have hz := zle_toZ sign
    change ZT.toZ Γ L+𝔞 d = ZT.toZ Γ R at hz
    have hk := natEq (eq_add_of_le hEnough)
    change 𝔞 ((two*r)*U) = 𝔞 (A*m+k) at hk
    simp only [left,right,L,R,ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat,IPRA.Q.mk_add,IPRA.Q.mk_mul,map_add,map_mul] at hz hk ⊢
    ipra_simps
    linear_combination hz-𝔞 E*hk
  have hi := from_signed scalarZero (fstT q) _ z one E zero one (le_refl one) hE
    (scalar_zero_represents one) (raw_represents q).andE₁ ans
  unfold RationalArgmin.rationalLE RationalArgmin.left
  exact le_congr (by unfold RationalValueBounds.crossLeft; ipra_ring)
    (by unfold RationalValueBounds.crossLeft; ipra_ring) hi

theorem first_half_nonnegative (p r m x : PTm n) (h : Γ ⊢[PRAAx] source r m)
    (hr : Γ ⊢[PRAAx] le one r) (hp : Γ ⊢[PRAAx] le (num 14*m) (unit p)) :
    Γ ⊢[PRAAx] RationalArgmin.rationalLE scalarZero (fstT (realSine p r m x)) :=
  scalar_nonnegative_of_upper r m _ _ _ h.andE₁ (unit_positive p) (first_half_upper p r m x h)
    (le_trans hp (le_congr (one_mul _) (.eqRefl _) (le_mul_mono
      (le_trans hr (le_of_eq_add (d := r) (by ipra_ring))) (le_refl _))))

end LeanProofs.IPRA.Analysis.GaussianCyclicSinePositiveRows

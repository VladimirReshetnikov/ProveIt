import IPRADerivations.Analysis.Stirling.GaussianStirlingOddReadback
import IPRADerivations.Analysis.Names.GaussianNamedBoundedProductObservation
import IPRADerivations.Analysis.RationalArithmetic.RationalGaussianRealPart

/-!
# The original Stirling difference lies in its finite odd-series interval

The actual normalized arithmetic clocks are used to transfer the
positive-affine map from the logarithm to its named difference.
At arbitrary requested precision the remaining slack is exactly the
name's own dyadic observation error.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingDifferenceBrackets

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (oneCode scale)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianNameArithmetic (multiplyModulus)
open GaussianPositiveRationalLogarithm (logF)
open GaussianRationalHorner (positive_product)
open GaussianRationalSyntheticDivision (qone qadd_congr qmul_congr)
open GaussianStirlingDifference (nameF data logData productF productData name_regular minusOne coefficient)
open GaussianStirlingOddCoefficients (coefficient_denominator_positive)
open GaussianStirlingOddGrid (parameter)
open GaussianStirlingOddLogBrackets (original_log_brackets)
open GaussianStirlingOddReadback (affine affine_congr lower_readback upper_readback)
open GaussianStirlingOddSeries (partialSum tail)
open RationalGaussianEmbedding (embed)
open RationalSupMetric (denominatorOf numeratorOf)
open RationalValueBounds (upper upper_congr upper_mono upper_triangle upper_of_radius radius_symmetric)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

private theorem coefficient_value (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] RationalArithmetic.represents (fstT (coefficient A B)) (ZT.ofNat (parameter A B)) (two*B) := by
  have h := GaussianRationalHorner.ofGaussian_represents (Γ := Γ) (scale (parameter A B) oneCode) (two*B)
    (coefficient_denominator_positive B hB)
  exact GaussianRationalHorner.scalar_congr (.eqRefl _) (by
    apply ZT.derive
    simp only [GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_one,ZT.toZ_ofNat]
    ring) (.eqRefl _) h.andE₁

private theorem minus_value : Γ ⊢[PRAAx] RationalArithmetic.represents (fstT (minusOne : PTm n)) (-ZT.ofNat one) one := by
  have q := GaussianRationalHorner.ofGaussian_represents (Γ := Γ) oneCode one (le_refl one)
  have h := GaussianRationalMetric.qnegative_represents qone oneCode one q
  exact GaussianRationalHorner.scalar_congr (.eqRefl _) (by
    apply ZT.derive
    simp only [GaussianRootAlgebra.re_neg,GaussianRootAlgebra.re_one,ZT.toZ_neg,ZT.toZ_ofNat,Q.mk_one,map_one]) (.eqRefl _) h.andE₁

private def affineNumerator (C E x : PTm n) : ZT n := ZT.ofNat C*numeratorOf x-ZT.ofNat (E*denominatorOf x)

private theorem affine_value (A B x : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] RationalArithmetic.represents (fstT (affine A B (embed x)))
      (affineNumerator (parameter A B) (two*B) x) ((two*B)*denominatorOf x) := by
  let C := parameter A B
  let E := two*B
  let X := denominatorOf x
  let c := fstT (coefficient A B)
  let q := GaussianRationalHorner.qmul (coefficient A B) (embed x)
  have p := RationalRepresentations.represents_multiply c x (ZT.ofNat C) (numeratorOf x) E X
    (coefficient_value A B hB) (RationalRepresentations.represents_self x)
  have v := GaussianRationalHorner.scalar_congr (RationalGaussianRealPart.real_product (coefficient A B) x).eqSymm
    (ZT.derive rfl) (.eqRefl _) p
  have w := RationalRepresentations.represents_add (fstT q) (fstT minusOne) _ _ (E*X) one v minus_value
  exact GaussianRationalHorner.scalar_congr (RationalGaussianRealPart.real_add q minusOne).eqSymm (by
    apply ZT.derive
    simp only [affineNumerator,ZT.toZ_mul,ZT.toZ_add,ZT.toZ_sub,ZT.toZ_neg,ZT.toZ_ofNat,Q.mk_one,map_one,Q.mk_mul,map_mul,C,E,X]
    ring) (by dsimp only [E,X]; ipra_ring) w

private theorem affine_upper (A B x y N D : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] upper x y N D) : Γ ⊢[PRAAx]
    upper (fstT (affine A B (embed x))) (fstT (affine A B (embed y))) (parameter A B*N) ((two*B)*D) := by
  let C := parameter A B
  let E := two*B
  let X := denominatorOf x
  let Y := denominatorOf y
  let u := numeratorOf x
  let v := numeratorOf y
  let left := ZT.ofNat (D*Y)*u
  let right := ZT.ofNat (D*X)*v+ZT.ofNat (N*X*Y)
  have he := coefficient_denominator_positive B hB
  have hx := positive_product _ _ he (RationalArgmin.denominator_positive x)
  have hy := positive_product _ _ he (RationalArgmin.denominator_positive y)
  have old : Γ ⊢[PRAAx] zle left right :=
    RationalUpperRepresentation.upper_from_representations x y X Y N D u v
      (RationalRepresentations.represents_self x) (RationalRepresentations.represents_self y) h
  have gap := zle_toZ old
  apply RationalCubeInfimumIntervals.upper_of_representations _ _ _ _ _ _ _ _ hx hy
    (affine_value A B x hB) (affine_value A B y hB)
  apply zle_of_toZ ((E*E*C)*PolynomialBisection.slack left right)
  simp only [PolynomialBisection.slack,left,right,affineNumerator,ZT.toZ_mul,ZT.toZ_add,ZT.toZ_sub,ZT.toZ_ofNat,
    Q.mk_mul,map_mul,C,E,X,Y,u,v] at gap ⊢
  linear_combination (𝔞 two*𝔞 B)*(𝔞 two*𝔞 B)*𝔞 (parameter A B)*gap

private def logClock (A B p : PTm n) : PTm n :=
  GaussianNamedBoundedProductObservation.clock constantF logF (GaussianFastValueCut.exponent two p) (coefficient A B) (logData A B)

private theorem log_clock_at_least (A B p : PTm n) : Γ ⊢[PRAAx] le p (logClock A B p) := by
  unfold logClock GaussianNamedBoundedProductObservation.clock GaussianFastValueCut.exponent
  exact le_trans (le_add_right _ _) (le_add_right _ _)

private theorem sample_affine (A B p : PTm n) : Γ ⊢[PRAAx] ap2 nameF p (data A B) ≐
    affine A B (embed (fstT (ap2 logF (logClock A B p) (logData A B)))) := by
  let q := GaussianFastValueCut.exponent two p
  let t := logClock A B p
  let x := logData A B
  let c := coefficient A B
  let s := ap2 logF t x
  have read := GaussianExponentialReference.add_sample (Γ := Γ) productF constantF (productData A B) minusOne p
  have prod := (GaussianNamedBoundedProductObservation.name_at (Γ := Γ) constantF logF q c x).eqTrans
    (qmul_congr (constant_at t c) (.eqRefl _))
  have row := read.eqTrans (qadd_congr prod (constant_at q minusOne))
  have canon := GaussianPositiveRationalLogarithm.sample_canonical (Γ := Γ) t (A+B) A
  have axis := GaussianPositiveRationalLogarithm.sample_axis (Γ := Γ) t (A+B) A
  exact row.eqTrans (affine_congr A B (RationalGaussianEmbedding.canonical_axis_roundtrip s canon axis).eqSymm)

private theorem native_brackets (A B K p : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] upper (fstT (partialSum A B K)) (fstT (ap2 nameF p (data A B))) (parameter A B) (unit p) ⋏
      upper (fstT (ap2 nameF p (data A B))) (fstT (GaussianRationalHorner.qadd (partialSum A B K) (tail A B K)))
        (parameter A B) (unit p) := by
  let t := logClock A B p
  let E := two*B
  have hE := coefficient_denominator_positive B hB
  have h := original_log_brackets A B (succ K) t hA
  have a : Γ ⊢[PRAAx] upper (fstT (partialSum A B K)) (fstT (ap2 nameF p (data A B))) (parameter A B) (E*unit t) :=
    upper_congr (congrFst (lower_readback A B K hA hB)) (congrFst (sample_affine A B p)).eqSymm
      (by ipra_ring) (.eqRefl _) (affine_upper A B _ _ _ _ hB h.andE₁)
  have b : Γ ⊢[PRAAx] upper (fstT (ap2 nameF p (data A B)))
      (fstT (GaussianRationalHorner.qadd (partialSum A B K) (tail A B K))) (parameter A B) (E*unit t) :=
    upper_congr (congrFst (sample_affine A B p)).eqSymm (congrFst (upper_readback A B K hA hB))
      (by ipra_ring) (.eqRefl _) (affine_upper A B _ _ _ _ hB h.andE₂)
  have large : Γ ⊢[PRAAx] le (unit p) (E*unit t) := by
    have e : Γ ⊢[PRAAx] le (unit p) (unit t) := GaussianBalancedRadiusArithmetic.unit_monotone _ _ (log_clock_at_least A B p)
    dsimp only [E]
    ipra_le sl e+𝔞 (unit t)*sl hE
  have cost : Γ ⊢[PRAAx] le (parameter A B*unit p) (parameter A B*(E*unit t)) := by
    ipra_le 𝔞 (parameter A B)*sl large
  have den := positive_product (Γ := Γ) _ _ hE (unit_positive t)
  exact .andI (upper_mono _ _ _ _ _ _ den a cost) (upper_mono _ _ _ _ _ _ den b cost)

theorem observation_brackets (A B K p : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] upper (fstT (partialSum A B K)) (fstT (ap2 nameF p (data A B))) one (unit p) ⋏
      upper (fstT (ap2 nameF p (data A B)))
        (fstT (GaussianRationalHorner.qadd (partialSum A B K) (tail A B K))) one (unit p) := by
  let a := fstT (partialSum A B K)
  let b := fstT (GaussianRationalHorner.qadd (partialSum A B K) (tail A B K))
  let x := data A B
  let Q := fstT (ap2 nameF p x)
  let C := parameter A B+one
  have reg := name_regular A B hA hB
  refine .andI ?_ ?_
  · let t := GaussianNamedRealOrderTransport.precision a Q (unit p) C
    have near := native_brackets A B K t hA hB
    have dist := GaussianNameEquivalence.point_at nameF x t p reg
    have den := positive_product (Γ := Γ) _ _ (unit_positive t) (unit_positive p)
    have u := upper_of_radius _ _ _ _ (GaussianNamedPositiveExponentialOrder.scalar_coordinate_distance _ _ _ _ den dist)
    have j := upper_triangle _ _ _ _ _ _ _ near.andE₁ u
    apply GaussianNamedRealOrderTransport.remove_upper_slack a Q one (unit p) C
    exact upper_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive t) den) j
      (le_of_eq_add (d := zero) (by dsimp [C]; ipra_ring))
  · let t := GaussianNamedRealOrderTransport.precision Q b (unit p) C
    have near := native_brackets A B K t hA hB
    have dist := GaussianNameEquivalence.point_at nameF x p t reg
    have den := positive_product (Γ := Γ) _ _ (unit_positive p) (unit_positive t)
    have u := upper_of_radius _ _ _ _ (GaussianNamedPositiveExponentialOrder.scalar_coordinate_distance _ _ _ _ den dist)
    have j := upper_triangle _ _ _ _ _ _ _ u near.andE₂
    apply GaussianNamedRealOrderTransport.remove_upper_slack Q b one (unit p) C
    exact upper_mono _ _ _ _ _ _ (positive_product _ _ den (unit_positive t)) j
      (le_of_eq_add (d := zero) (by dsimp [C]; ipra_ring))

theorem actual_Stirling_difference_odd_brackets_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      ((le one (var 0) ⋏ le one (var 1)) ⟶
        (upper (fstT (partialSum (var 0) (var 1) (var 2))) (fstT (ap2 nameF (var 3) (data (var 0) (var 1)))) one (unit (var 3)) ⋏
          upper (fstT (ap2 nameF (var 3) (data (var 0) (var 1))))
            (fstT (GaussianRationalHorner.qadd (partialSum (var 0) (var 1) (var 2)) (tail (var 0) (var 1) (var 2))))
            one (unit (var 3)))) :=
  closeUniv 4 (.impI (observation_brackets _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianStirlingDifferenceBrackets

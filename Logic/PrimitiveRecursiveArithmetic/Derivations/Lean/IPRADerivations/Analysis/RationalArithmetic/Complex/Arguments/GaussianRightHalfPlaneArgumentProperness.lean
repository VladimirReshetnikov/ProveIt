import IPRADerivations.Analysis.RationalArithmetic.Complex.Arguments.GaussianRightHalfPlaneArgument
import IPRADerivations.Analysis.Trigonometry.Arctangent.PartialSums.GaussianArctangentPartialRepresentation

/-!
# Fraction independence of the right half-plane argument

The chart test is preserved by clearing positive denominators. In the
small chart equal slopes enter the original arctangent fraction
independence theorem. The other chart uses the same result at the
reciprocal ratio. Conjugation preserves the transport for negative
imaginary coordinates.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneArgumentProperness

open_ipra
open GaussianArctangentQuarterExponential (quarterF quarter_regular)
open GaussianBoundedConstantProductName (constantF constant_regular ordinary_product_identity)
open GaussianNameArithmetic (multiply_equivalent add_equivalent)
open GaussianNameEquivalence (diagonal_refl crossEquivalent cross_trans cross_symm cross_to_diagonal)
open GaussianNameRingLaws (negativeF negativeData negative_fast negative_equivalent)
open GaussianRightHalfPlaneArgument
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "atanF" => GaussianArctangentPartialQuadrature.nameF
local notation "atData" => GaussianArctangentPartialQuadrature.data

/-- Two equal slopes lie on the same side of the unit chart boundary. -/
private theorem small_order (A B C D : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (h : Γ ⊢[PRAAx] B*C ≐ D*A) (hB : Γ ⊢[PRAAx] le B A) :
    Γ ⊢[PRAAx] le D C := by
  have a := RationalIntegerNormalization.positive_form hA
  have first : Γ ⊢[PRAAx] le (B*C) (A*C) := le_mul_mono hB (le_refl C)
  have e : Γ ⊢[PRAAx] A*D ≐ B*C := (by ipra_ring : Γ ⊢[PRAAx] A*D ≐ D*A).eqTrans h.eqSymm
  have next := le_congr e.eqSymm (.eqRefl _) first
  exact mul_le_cancel_at a next

private theorem large_order (A B C D : PTm n) (hC : Γ ⊢[PRAAx] le one C)
    (h : Γ ⊢[PRAAx] B*C ≐ D*A) (hB : Γ ⊢[PRAAx] lt A B) :
    Γ ⊢[PRAAx] lt C D := by
  refine .orE (lt_or_le C D) (.hyp0) ?_
  have hit := small_order C D A B hC.wk h.eqSymm.wk Prf.hyp0
  exact le_lt_absurd _ hit hB.wk

theorem small_cross (A B C D : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hC : Γ ⊢[PRAAx] le one C) (hB : Γ ⊢[PRAAx] le B A) (hD : Γ ⊢[PRAAx] le D C)
    (h : Γ ⊢[PRAAx] B*C ≐ D*A) :
    Γ ⊢[PRAAx] crossEquivalent smallF smallF (smallData A B) (smallData C D) := by
  have p := GaussianArctangentPartialQuadrature.name_regular B A hA hB
  have q := GaussianArctangentPartialQuadrature.name_regular D C hC hD
  have a := constant_regular (Γ := Γ) (GaussianRightHalfPlaneArgument.half : PTm n)
  have left := ordinary_product_identity atanF one GaussianRightHalfPlaneArgument.half (atData B A) (.andI p half_bounded)
  have right := ordinary_product_identity atanF one GaussianRightHalfPlaneArgument.half (atData D C) (.andI q half_bounded)
  have slopes := GaussianArctangentPartialRepresentation.representation_cross B A D C hA hC hB h
  have center := multiply_equivalent constantF constantF atanF atanF GaussianRightHalfPlaneArgument.half GaussianRightHalfPlaneArgument.half (atData B A) (atData D C)
    a a p q (diagonal_refl constantF GaussianRightHalfPlaneArgument.half) (cross_to_diagonal _ _ _ _ slopes)
  exact cross_trans _ _ _ _ _ _ left (cross_trans _ _ _ _ _ _ center (cross_symm _ _ _ _ right))

theorem large_cross (A B C D : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hC : Γ ⊢[PRAAx] le one C) (hB : Γ ⊢[PRAAx] lt A B) (hD : Γ ⊢[PRAAx] lt C D)
    (h : Γ ⊢[PRAAx] B*C ≐ D*A) :
    Γ ⊢[PRAAx] crossEquivalent largeF largeF (largeData A B) (largeData C D) := by
  have b := le_trans hA (le_of_lt hB)
  have d := le_trans hC (le_of_lt hD)
  have e : Γ ⊢[PRAAx] A*D ≐ C*B :=
    (by ipra_ring : Γ ⊢[PRAAx] A*D ≐ D*A).eqTrans
      (h.eqSymm.eqTrans (by ipra_ring))
  have left := small_regular B A b (le_of_lt hB)
  have right := small_regular D C d (le_of_lt hD)
  have q := quarter_regular (Γ := Γ) (zero : PTm n)
  have neg := negative_equivalent smallF smallF (smallData B A) (smallData D C) left right
    (cross_to_diagonal _ _ _ _ (small_cross B A D C b d (le_of_lt hB) (le_of_lt hD) e))
  exact add_equivalent quarterF quarterF (negativeF smallF) (negativeF smallF)
    zero zero (negativeData (smallData B A)) (negativeData (smallData D C))
    q q (negative_fast _ _ left) (negative_fast _ _ right)
    (diagonal_refl quarterF zero) (cross_to_diagonal _ _ _ _ neg)

theorem unsigned_cross (A B C D : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hC : Γ ⊢[PRAAx] le one C) (h : Γ ⊢[PRAAx] B*C ≐ D*A) :
    Γ ⊢[PRAAx] crossEquivalent unsignedF unsignedF (unsignedData A B) (unsignedData C D) := by
  refine .orE (lt_or_le A B) ?_ ?_
  · have hd := large_order A B C D hC.wk h.wk Prf.hyp0
    exact cross_trans _ _ _ _ _ _ (unsigned_large A B hA.wk Prf.hyp0)
      (cross_trans _ _ _ _ _ _ (large_cross A B C D hA.wk hC.wk Prf.hyp0 hd h.wk)
        (cross_symm _ _ _ _ (unsigned_large C D hC.wk hd)))
  · have hd := small_order A B C D hA.wk h.wk Prf.hyp0
    exact cross_trans _ _ _ _ _ _ (unsigned_small A B hA.wk Prf.hyp0)
      (cross_trans _ _ _ _ _ _ (small_cross A B C D hA.wk hC.wk Prf.hyp0 hd h.wk)
        (cross_symm _ _ _ _ (unsigned_small C D hC.wk hd)))

theorem equal_ratio (A B C D neg : PTm n) (hA : Γ ⊢[PRAAx] source A neg)
    (hC : Γ ⊢[PRAAx] le one C) (h : Γ ⊢[PRAAx] B*C ≐ D*A) :
    Γ ⊢[PRAAx] crossEquivalent nameF nameF (data A B neg) (data C D neg) := by
  have ratio := unsigned_cross A B C D hA.andE₁ hC h
  refine .orE hA.andE₂ ?_ ?_
  · exact cross_trans _ _ _ _ _ _ (positive_sign A B neg hA.andE₁.wk Prf.hyp0)
      (cross_trans _ _ _ _ _ _ ratio.wk (cross_symm _ _ _ _ (positive_sign C D neg hC.wk Prf.hyp0)))
  · have hneg := GaussianNameConjugation.conjugate_cross unsignedF unsignedF
      (unsignedData A B) (unsignedData C D) ratio
    exact cross_trans _ _ _ _ _ _ (negative_sign A B neg hA.andE₁.wk Prf.hyp0)
      (cross_trans _ _ _ _ _ _ hneg.wk (cross_symm _ _ _ _ (negative_sign C D neg hC.wk Prf.hyp0)))

theorem actual_right_half_plane_argument_fraction_independence_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      ((source (var 0) (var 4) ⋏ le one (var 2) ⋏ (var 1*var 2 ≐ var 3*var 0)) ⟶
        crossEquivalent nameF nameF (data (var 0) (var 1) (var 4)) (data (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (equal_ratio _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneArgumentProperness

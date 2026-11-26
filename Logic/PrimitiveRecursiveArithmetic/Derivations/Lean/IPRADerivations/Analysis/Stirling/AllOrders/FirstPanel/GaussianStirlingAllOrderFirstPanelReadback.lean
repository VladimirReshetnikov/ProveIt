import IPRADerivations.Analysis.Stirling.AllOrders.FirstPanel.GaussianStirlingAllOrderFirstPanelError
import IPRADerivations.Analysis.Stirling.Expansions.GaussianStirlingOddReadback
import IPRADerivations.Analysis.Names.RationalGaussianNameEmbedding
import IPRADerivations.Analysis.RationalArithmetic.Representations.RationalRepresentedUpper

/-!
# Gaussian readback of the first periodic panel

Halving the literal sampled panel compares it to the original Stirling
affine map on a harmonic observation, with the exact propagated
inverse-square error.
-/

set_option autoImplicit false
set_option maxHeartbeats 350000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderFirstPanelReadback

open_ipra
open GaussianStirlingAllOrderFirstPanelError (reference logPart panel_error)
open GaussianStirlingAllOrderFirstPanelSquareError (squareError)
open GaussianStirlingAllOrderPanelTail (panel)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianRationalHorner (positive_product)
open GaussianRationalL1 (nonnegative_of_representation)
open RationalNonnegativePowers (fraction_multiply)
open RationalArithmetic (add multiply negative)
open RationalAlgebra (add_congr add_commutative add_associative multiply_congr multiply_associative multiply_add
  multiply_negative negative_congr negative_minus_multiply)
open RationalArgmin (rationalLE rationalLE_congr denominator_positive)
open RationalValueBounds (upper radius radius_of_upper upper_of_order)
open PolynomialBisection (zle_scale_cancel)
open RationalSupMetric (numeratorOf denominatorOf)
open RationalGaussianEmbedding (embed embed_add embed_multiply embed_negative embed_one)
open RationalGaussianRealPart (embed_congr)
open GaussianRationalMetric (distanceBounded qnegative)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr)
open GaussianStirlingOddReadback (affine)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

theorem upper_of_add_order (a b A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] rationalLE a (add b (fraction A B))) : Γ ⊢[PRAAx] upper a b A B := by
  let P := denominatorOf a
  let Q := denominatorOf b
  let c := add b (fraction A B)
  let C := denominatorOf c
  let x := numeratorOf a
  let y := numeratorOf b
  let u := numeratorOf c
  have ha := RationalRepresentations.represents_self (Γ := Γ) a
  have hb := RationalRepresentations.represents_self (Γ := Γ) b
  have ep := ZT.toZ_eq (RationalRepresentations.represents_add b (fraction A B) y (ZT.ofNat A) Q B hb
    (fraction_represents _ _ hB))
  have eo := natEq (eq_add_of_le h)
  apply RationalRepresentedUpper.from_signed _ _ _ _ P Q _ _ (denominator_positive a) (denominator_positive b) ha hb
  apply zle_scale_cancel (c := C) (denominator_positive c)
  apply zle_of_toZ (Q*B*monus (RationalArgmin.left c a) (RationalArgmin.left a c))
  simp only [RationalRepresentedUpper.left,RationalRepresentedUpper.right,ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat] at ep ⊢
  unfold RationalArgmin.left at eo ⊢
  simp only [ZT.toZ] at ep ⊢
  dsimp only [P,Q,x,y,u,C,c] at ep ⊢
  ipra_simps
  linear_combination -𝔞(P)*ep-𝔞(Q)*𝔞(B)*eo

private theorem add_units : Γ ⊢[PRAAx] add (fraction one one) (fraction one one) ≐ fraction two one := by
  have hd : Γ ⊢[PRAAx] le one (one*one : PTm n) := by ipra_le 0
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _
    (RationalArithmetic.add_guard _ _) (RationalNormalForm.normalize_well_formed _ _ (le_refl one))
    (RationalRepresentations.represents_add _ _ _ _ _ _ (fraction_represents one one (le_refl one))
      (fraction_represents one one (le_refl one))) (fraction_represents _ _ (le_refl one)) hd (le_refl one)
  apply ZT.derive
  ipra_simps
  ring

private theorem negative_add (a b : PTm n) : Γ ⊢[PRAAx] negative (add a b) ≐ add (negative a) (negative b) :=
  (negative_minus_multiply _).eqTrans ((multiply_add _ _ _).eqTrans
    (add_congr (negative_minus_multiply _).eqSymm (negative_minus_multiply _).eqSymm))

private theorem half_twice : Γ ⊢[PRAAx] multiply (fraction one two : PTm n) (fraction two one) ≐ fraction one one := by
  have h₂ : Γ ⊢[PRAAx] le one (two : PTm n) := by ipra_le 1
  refine (fraction_multiply one two two one h₂ (le_refl one)).eqTrans ?_
  have hd := positive_product _ _ h₂ (le_refl one)
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _
    (RationalNormalForm.normalize_well_formed _ _ hd) (RationalNormalForm.normalize_well_formed _ _ (le_refl one))
    (fraction_represents _ _ hd) (fraction_represents _ _ (le_refl one)) hd (le_refl one)
  apply ZT.derive
  ipra_simps
  ring

private theorem half_coefficient (U B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] multiply (fraction one two) (fraction (two*U+B) B) ≐ fraction (two*U+B) (two*B) :=
  (fraction_multiply one two (two*U+B) B (by ipra_le 1) hB).eqTrans
    (RationalNonnegativePowers.fraction_congr (one_mul _) (.eqRefl _))

theorem halve_reference (U B Q : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] embed (multiply (fraction one two) (reference U B Q)) ≐
      affine U B (embed (RationalHarmonicInterval.interval (U+B) U Q)) := by
  let h := RationalHarmonicInterval.interval (U+B) U Q
  let c : PTm n := fraction one two
  let z := negative (fraction one one : PTm n)
  have eq : Γ ⊢[PRAAx] reference U B Q ≐ add (logPart U B Q) (negative (fraction two one)) :=
    (add_congr (add_commutative z (logPart U B Q)) (.eqRefl _)).eqTrans
      ((add_associative _ _ _).eqTrans (add_congr (.eqRefl _)
        ((negative_add _ _).eqSymm.eqTrans (negative_congr add_units))))
  have em : Γ ⊢[PRAAx] multiply c (reference U B Q) ≐
      add (multiply (fraction (two*U+B) (two*B)) h) (negative (fraction one one)) :=
    (multiply_congr (.eqRefl _) eq).eqTrans
      ((multiply_add _ _ _).eqTrans (add_congr
        ((multiply_associative _ _ _).eqSymm.eqTrans (multiply_congr (half_coefficient U B hB) (.eqRefl _)))
        ((multiply_negative _ _).eqTrans (negative_congr half_twice))))
  have hb := positive_product _ _ (by ipra_le 1 : Γ ⊢[PRAAx] le one two) hB
  have ec : Γ ⊢[PRAAx] embed (fraction (two*U+B) (two*B)) ≐ GaussianStirlingDifference.coefficient U B :=
    GaussianEulerDecayOrder.fraction_embedding _ _ hb
  have eh : Γ ⊢[PRAAx] embed (multiply (fraction (two*U+B) (two*B)) h) ≐
      GaussianRationalHorner.qmul (GaussianStirlingDifference.coefficient U B) (embed h) :=
    (embed_multiply _ _).eqTrans (qmul_congr ec (.eqRefl _))
  have en : Γ ⊢[PRAAx] embed (negative (fraction one one : PTm n)) ≐ GaussianStirlingDifference.minusOne :=
    (embed_negative _).eqTrans (RationalGaussianEmbedding.negative_congr embed_one)
  exact (embed_congr em).eqTrans ((embed_add _ _).eqTrans (qadd_congr eh en))

def halfPanel (A B Q k : PTm n) : PTm n :=
  embed (multiply (fraction one two) (panel 0 one A B (B*Q) k))

theorem harmonic_distance (A B Q k : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) (hQ : Γ ⊢[PRAAx] le one Q) :
    Γ ⊢[PRAAx] distanceBounded (halfPanel A B Q k)
      (affine (A+B*k) B (embed (RationalHarmonicInterval.interval ((A+B*k)+B) (A+B*k) Q)))
      ((A+B*k)+B) (two*(B*succ (Q*(A+B*k)))) := by
  let U := A+B*k
  let c : PTm n := fraction one two
  let p := panel 0 one A B (B*Q) k
  let r := reference U B Q
  let D := B*succ (Q*U)
  let N := U+B
  let p' := multiply c p
  let r' := multiply c r
  have hD := positive_product _ _ hB (zero_lt_succ (Q*U))
  have h₂ : Γ ⊢[PRAAx] le one (two : PTm n) := by ipra_le 1
  have hh := positive_product _ _ h₂ hD
  have hc := nonnegative_of_representation c one two h₂ (fraction_represents one two h₂)
  have hp := panel_error A B Q k hA hB hQ
  have up := RationalArithmetic.multiply_monotone c p (add r (squareError U B Q)) hc hp.andE₂
  have down := RationalArithmetic.multiply_monotone c r p hc hp.andE₁
  have ef : Γ ⊢[PRAAx] multiply c (squareError U B Q) ≐ fraction N (two*D) :=
    (fraction_multiply one two N D h₂ hD).eqTrans (RationalNonnegativePowers.fraction_congr (one_mul _) (.eqRefl _))
  have upper := upper_of_add_order p' r' N (two*D) hh
    (rationalLE_congr (.eqRefl _) ((multiply_add _ _ _).eqTrans (add_congr (.eqRefl _) ef)) up)
  have lower := upper_of_order r' p' N (two*D) down
  exact GaussianRationalDistanceOrder.distance_congr (.eqRefl _) (halve_reference U B Q hB) (.eqRefl _) (.eqRefl _)
    (RationalGaussianNameEmbedding.distance_from_radius _ _ _ _ hh (radius_of_upper _ _ _ _ upper lower))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderFirstPanelReadback

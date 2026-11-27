import IPRADerivations.Analysis.Stirling.AllOrders.FirstPanel.GaussianStirlingAllOrderFirstPanelSquareError

/-!
# The first periodic panel against the original finite logarithm

The genuine sampled panel lies between twice the Stirling difference
evaluated on the original harmonic observation and that value plus the
explicit one-sided inverse-square error.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderFirstPanelError

open_ipra
open GaussianStirlingAllOrderFirstPanelGridTerms (linearCoefficient squareCoefficient)
open GaussianStirlingAllOrderFirstPanelSum (panelValue actual_panel)
open GaussianStirlingAllOrderPanelTail (panel)
open GaussianStirlingAllOrderFirstPanelSquareError (weight squareContribution squareError square_contribution_error)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianRationalHorner (positive_product)
open RationalNonnegativePowers (fraction_multiply fraction_congr)
open RationalArithmetic (add multiply negative)
open RationalAlgebra (add_congr add_associative add_commutative multiply_congr multiply_associative multiply_add
  multiply_negative negative_congr negative_minus_multiply negative_antitone)
open RationalArgmin (rationalLE rationalLE_congr reflexive)
open GaussianRationalSyntheticBounds (add_monotone)
open RationalHalfNinthProductLower (add_negative_cancel)
open RationalReciprocalPowerTail (tail)
open RationalAlgebra (negative_add)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def logPart (U B Q : PTm n) : PTm n :=
  multiply (fraction (two*U+B) B) (RationalHarmonicInterval.interval (U+B) U Q)

def reference (U B Q : PTm n) : PTm n :=
  add (add (negative (fraction one one)) (logPart U B Q)) (negative (fraction one one))

private theorem divide_coefficients (C B Q : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hQ : Γ ⊢[PRAAx] le one Q) :
    Γ ⊢[PRAAx] multiply (fraction one (B*Q)) (fraction (C*Q) one) ≐ fraction C B := by
  have hM := positive_product _ _ hB hQ
  refine (fraction_multiply one (B*Q) (C*Q) one hM (le_refl one)).eqTrans ?_
  have hD := positive_product _ _ hM (le_refl one)
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _
    (RationalNormalForm.normalize_well_formed _ _ hD) (RationalNormalForm.normalize_well_formed _ _ hB)
    (fraction_represents _ _ hD) (fraction_represents _ _ hB) hD hB
  apply ZT.derive
  ipra_simps
  ring

theorem normalized_panel (U B Q : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hQ : Γ ⊢[PRAAx] le one Q) :
    Γ ⊢[PRAAx] panelValue U B Q ≐
      add (add (negative (fraction one one)) (logPart U B Q)) (negative (squareContribution U B Q)) := by
  let v := fraction one (B*Q)
  let H := RationalHarmonicInterval.interval (U+B) U Q
  let S := tail two (Q*U) (B*Q)
  let C := fraction (linearCoefficient U B Q) one
  let E := fraction (squareCoefficient U B Q) one
  let z := negative (fraction (B*Q) one)
  have e₀ : Γ ⊢[PRAAx] multiply v z ≐ negative (fraction one one) := by
    refine (multiply_negative _ _).eqTrans (negative_congr ?_)
    let M := B*Q
    have hM := positive_product _ _ hB hQ
    refine (fraction_multiply one M M one hM (le_refl one)).eqTrans ?_
    have hD := positive_product _ _ hM (le_refl one)
    apply RationalFiniteSum.canonical_equal _ _ _ _ _ _
      (RationalNormalForm.normalize_well_formed _ _ hD) (RationalNormalForm.normalize_well_formed _ _ (le_refl one))
      (fraction_represents _ _ hD) (fraction_represents _ _ (le_refl one)) hD (le_refl one)
    apply ZT.derive
    dsimp only [M]
    ipra_simps
    ring
  have e₁ : Γ ⊢[PRAAx] multiply v (multiply C H) ≐ logPart U B Q :=
    (multiply_associative _ _ _).eqSymm.eqTrans (multiply_congr (divide_coefficients _ _ _ hB hQ) (.eqRefl _))
  have eC : Γ ⊢[PRAAx] multiply v E ≐ weight U B Q :=
    (multiply_congr (.eqRefl _) (fraction_congr (by dsimp [squareCoefficient]; ipra_ring) (.eqRefl one))).eqTrans
      (divide_coefficients (U*(U+B)*Q) B Q hB hQ)
  have e₂ : Γ ⊢[PRAAx] multiply v (negative (multiply E S)) ≐ negative (squareContribution U B Q) :=
    (multiply_negative _ _).eqTrans (negative_congr ((multiply_associative _ _ _).eqSymm.eqTrans
      (multiply_congr eC (.eqRefl _))))
  exact (multiply_add _ _ _).eqTrans
    ((add_congr e₀ ((multiply_add _ _ _).eqTrans (add_congr e₁ e₂))).eqTrans
      (add_associative _ _ _).eqSymm)

theorem panel_error (A B Q k : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hB : Γ ⊢[PRAAx] le one B) (hQ : Γ ⊢[PRAAx] le one Q) :
    Γ ⊢[PRAAx] rationalLE (reference (A+B*k) B Q) (panel 0 one A B (B*Q) k) ⋏
      rationalLE (panel 0 one A B (B*Q) k) (add (reference (A+B*k) B Q) (squareError (A+B*k) B Q)) := by
  let U := A+B*k
  let W := squareContribution U B Q
  let E := squareError U B Q
  let c : PTm n := fraction one one
  let z := add (negative c) (logPart U B Q)
  have e : Γ ⊢[PRAAx] panel 0 one A B (B*Q) k ≐ add z (negative W) :=
    (actual_panel A B Q k hA hB hQ).eqTrans (normalized_panel U B Q hB hQ)
  have hw := square_contribution_error U B Q (le_trans hA (le_add_right A (B*k))) hB hQ
  have lo := negative_antitone W c hw.andE₁
  have hi := negative_antitone c (add W E) hw.andE₂
  have h := add_monotone _ _ _ _ (rationalLE_congr (negative_add W E) (.eqRefl _) hi) (reflexive E)
  have cancel : Γ ⊢[PRAAx] add (add (negative W) (negative E)) E ≐ negative W :=
    (add_congr (add_congr (.eqRefl _) (.eqRefl _)) (.eqRefl _)).eqTrans
      ((add_associative _ _ _).eqTrans
        ((add_congr (.eqRefl _) (add_commutative _ _)).eqTrans
          ((add_associative _ _ _).eqSymm.eqTrans (add_negative_cancel _ E (RationalArithmetic.negative_guard _)))))
  have hi' := add_monotone z z _ _ (reflexive _) (rationalLE_congr cancel (.eqRefl _) h)
  exact .andI (rationalLE_congr (.eqRefl _) e.eqSymm (add_monotone _ _ _ _ (reflexive z) lo))
    (rationalLE_congr e.eqSymm (add_associative _ _ _).eqSymm hi')

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderFirstPanelError

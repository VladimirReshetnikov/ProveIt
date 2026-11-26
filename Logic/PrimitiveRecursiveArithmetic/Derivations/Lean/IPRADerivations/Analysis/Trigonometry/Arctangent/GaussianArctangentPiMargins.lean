import IPRADerivations.Analysis.Stirling.GaussianGammaHalfWallisConvergence
import IPRADerivations.Analysis.RationalArithmetic.RationalRepresentedUpper

/-!
# Strict rational margins for the original arctangent π name

The actual fifth Wallis enclosure has center 131072/43659. Its one-sided
rate gives the lower margin 1501/500 and upper margin 7/2 for the original
arctangent π name, with only the observation's own dyadic error.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianArctangentPiMargins

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaHalfWallisConvergence (twiceWallis original_Wallis_rate)
open GaussianGammaHalfWallisRate (pairOdd evenSquare df_positive)
open GaussianGammaHalfSqrtBrackets (fraction_first_represents)
open GaussianGammaHalfPiName (nameF)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (comparison_of_cleared)
open RationalArgmin (rationalLE)
open RationalRepresentedUpper (to_signed from_signed left right)
open RationalSupMetric (numeratorOf denominatorOf)
open RationalValueBounds (upper upper_order_left upper_order_right)
open GaussianCoefficientNameBounds (unit)
open PolynomialBisection (zle_congr zle_scale_cancel)
open WallisFinite (da db da_zero da_succ db_zero db_succ)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def lowerDen : PTm n := num 5*num 10*num 10
def lowerNum : PTm n := num 3*lowerDen+one
def lower : PTm n := fstT (fraction lowerNum lowerDen)
def upperPoint : PTm n := fstT (fraction (num 7) two)

private def oddProduct : ℕ → PTm n
  | 0 => one
  | k+1 => oddProduct k*num (2*k+1)

private def evenProduct : ℕ → PTm n
  | 0 => one
  | k+1 => evenProduct k*num (2*(k+1))

private theorem odd_literal (k : ℕ) : Γ ⊢[PRAAx] da (num k) ≐ oddProduct k := by
  induction k with
  | zero => exact da_zero
  | succ k ih =>
    refine (da_succ (num k)).eqTrans (congrMul ih ?_)
    apply deriveNat
    ipra_simps
    push_cast
    ring

private theorem even_literal (k : ℕ) : Γ ⊢[PRAAx] db (num k) ≐ evenProduct k := by
  induction k with
  | zero => exact db_zero
  | succ k ih =>
    refine (db_succ (num k)).eqTrans (congrMul ih ?_)
    apply deriveNat
    ipra_simps
    push_cast
    ring

private theorem lower_clear : Γ ⊢[PRAAx] le (pairOdd (num 5)*lowerNum) ((two*evenSquare (num 5))*lowerDen) := by
  have d5 := natEq (odd_literal (Γ := Γ) 5)
  have d6 := natEq (show Γ ⊢[PRAAx] da (succ (num 5)) ≐ oddProduct 6 from odd_literal 6)
  have e5 := natEq (even_literal (Γ := Γ) 5)
  apply le_of_eq_add (d := num 15*num 15*(num 38*num 10*num 10+num 41))
  apply deriveNat
  unfold pairOdd evenSquare lowerNum lowerDen
  ipra_simps
  rw [d5,d6,e5]
  simp only [oddProduct,evenProduct]
  ipra_simps
  ring

private theorem upper_clear : Γ ⊢[PRAAx] le (num 10*(two*evenSquare (num 5))) (num 31*pairOdd (num 5)) := by
  have d5 := natEq (odd_literal (Γ := Γ) 5)
  have d6 := natEq (show Γ ⊢[PRAAx] da (succ (num 5)) ≐ oddProduct 6 from odd_literal 6)
  have e5 := natEq (even_literal (Γ := Γ) 5)
  apply le_of_eq_add (d := num 15*num 15*(num 42*num 10*num 10*num 10+num 7*num 10*num 10+num 9))
  apply deriveNat
  unfold pairOdd evenSquare
  ipra_simps
  rw [d5,d6,e5]
  simp only [oddProduct,evenProduct]
  ipra_simps
  ring

private def ceilingReference : PTm n := fstT (fraction (num 31) (num 10))

theorem wallis_comparison : Γ ⊢[PRAAx] rationalLE lower (fstT (twiceWallis (num 5))) ⋏
    rationalLE (fstT (twiceWallis (num 5))) ceilingReference := by
  have hl : Γ ⊢[PRAAx] le one (lowerDen : PTm n) := by unfold lowerDen; ipra_le 499
  have hh : Γ ⊢[PRAAx] le one (num 10 : PTm n) := by ipra_le 9
  have hw := positive_product (Γ := Γ) _ _ (df_positive (num 5)) (df_positive (succ (num 5)))
  have wr := fraction_first_represents (two*evenSquare (num 5)) (pairOdd (num 5)) hw
  exact .andI (comparison_of_cleared _ _ _ _ _ _ hl hw (fraction_first_represents lowerNum lowerDen hl) wr lower_clear)
    (comparison_of_cleared _ _ _ _ _ _ hw hh wr (fraction_first_represents (num 31) (num 10) hh) upper_clear)

theorem named_margins (p x : PTm n) : Γ ⊢[PRAAx]
    upper lower (fstT (ap2 nameF p x)) one (unit p) ⋏ upper (fstT (ap2 nameF p x)) upperPoint one (unit p) := by
  let P := fstT (ap2 nameF p x)
  let U := unit p
  let E := denominatorOf P
  let a := numeratorOf P
  have comparison := wallis_comparison (Γ := Γ)
  have named := original_Wallis_rate (Γ := Γ) (num 4) p x
  have lo : Γ ⊢[PRAAx] upper lower P one U := upper_order_left _ _ _ _ _ comparison.andE₁ named.andE₁
  have hi : Γ ⊢[PRAAx] upper P ceilingReference (two*U+num 5) (num 5*U) :=
    upper_order_right _ _ _ _ _ named.andE₂ comparison.andE₂
  have hE := RationalArgmin.denominator_positive (Γ := Γ) P
  have ten : Γ ⊢[PRAAx] le one (num 10 : PTm n) := by ipra_le 9
  have signed := to_signed P ceilingReference a (ZT.ofNat (num 31)) E (num 10) (two*U+num 5) (num 5*U)
    (RationalRepresentations.represents_self P) (fraction_first_represents (num 31) (num 10) ten) hi
  refine .andI lo (from_signed P upperPoint a (ZT.ofNat (num 7)) E two one U hE (le_succ_self one)
    (RationalRepresentations.represents_self P) (fraction_first_represents (num 7) two (le_succ_self one)) ?_)
  apply zle_scale_cancel (c := num 25) (by ipra_le 24)
  exact zle_congr (by unfold left; ipra_simps; ring) (by unfold right; ipra_simps; ring) signed

theorem actual_original_pi_named_margins_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (upper lower (fstT (ap2 nameF (var 0) (var 1))) one (unit (var 0)) ⋏
      upper (fstT (ap2 nameF (var 0) (var 1))) upperPoint one (unit (var 0))) :=
  closeUniv 2 (named_margins _ _)

end LeanProofs.IPRA.Analysis.GaussianArctangentPiMargins

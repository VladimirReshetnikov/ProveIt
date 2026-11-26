import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.ImageGrids.GaussianEulerPositivePowerChartCorrectedImage
import IPRADerivations.Analysis.Euler.Integration.Decay.GaussianEulerDecayOrder

/-!
# Exact Stirling and Robbins telescopers for rational arguments

At x=a/b the upper telescoper is 1/(12x) and the lower one is
1/(12x+1). Their finite endpoint differences and the two sharp local
margins are exact fractions. The lower margin is positive for x≥1.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingRationalTelescopers

open_ipra
open ComplexLogarithmRemainder (oneCode scale)
open GaussianEulerPositivePowerChartCorrectedImage (fraction_sum)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qadd positive_product canonical_unique represents_rescale represents_congr
  ofGaussian_canonical ofGaussian_represents)
open GaussianRationalSyntheticDivision (qadd_congr)
open GaussianRootAlgebra (equal equal_of_values re_scale im_scale re_one im_one)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def numeratorSquare (b : PTm n) : PTm n := b*b
def gap (a b : PTm n) : PTm n := num 4*a*(a+b)
def denominatorSquare (a b : PTm n) : PTm n := (two*a+b)*(two*a+b)

ipra_subst numeratorSquare
ipra_subst gap [num]
ipra_subst denominatorSquare [two, one]

theorem square_split (a b : PTm n) :
    Γ ⊢[PRAAx] denominatorSquare a b ≐ gap a b+numeratorSquare b := by
  unfold denominatorSquare gap numeratorSquare
  ipra_ring

theorem small_numeral_positive (k : ℕ) : Γ ⊢[PRAAx] le one (num (k+1) : PTm n) := by
  exact zero_lt_succ (num k)

theorem gap_positive (a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) : Γ ⊢[PRAAx] le one (gap a b) :=
  positive_product _ _ (positive_product _ _ (small_numeral_positive 3) ha)
    (le_trans ha (le_add_right a b))

theorem square_positive (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] le one (denominatorSquare a b) := by
  have h := le_trans hb (le_add_left b (two*a))
  exact positive_product _ _ h h

/-- Equality of embedded natural fractions, with no reliance on a
particular denominator or reduction path. -/
theorem fraction_same (a b c d : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hd : Γ ⊢[PRAAx] le one d) (h : Γ ⊢[PRAAx] a*d ≐ c*b) :
    Γ ⊢[PRAAx] fraction a b ≐ fraction c d := by
  have hA := represents_rescale (fraction a b) (scale a oneCode) b d (ofGaussian_represents _ _ hb)
  have hC := represents_rescale (fraction c d) (scale c oneCode) d b (ofGaussian_represents _ _ hd)
  have e := natEq h
  have coefficients : Γ ⊢[PRAAx] equal (scale d (scale a oneCode)) (scale b (scale c oneCode)) := by
    refine equal_of_values ?_ ?_
    · simp only [re_scale,re_one]
      ipra_simps
      linear_combination e
    · simp only [im_scale,im_one]
      ring
  exact canonical_unique _ _ _ (d*b) (ofGaussian_canonical _ _ hb) (ofGaussian_canonical _ _ hd)
    (positive_product _ _ hd hb) (represents_congr (.eqRefl _) coefficients (mul_comm b d) hA) hC

def upperValue (a b : PTm n) : PTm n := fraction b (num 12*a)
def lowerValue (a b : PTm n) : PTm n := fraction b (num 12*a+b)
def upperDifference (a b t : PTm n) : PTm n := fraction (b*b*t) (num 12*a*(a+b*t))
def lowerDifference (a b t : PTm n) : PTm n := fraction (num 12*b*b*t) ((num 12*a+b)*(num 12*(a+b*t)+b))
def firstTerm (a b : PTm n) : PTm n := fraction (b*b) (num 3*denominatorSquare a b)
def geometricMain (a b : PTm n) : PTm n := fraction (b*b) (num 3*gap a b)
def upperMargin (a b : PTm n) : PTm n := fraction (two*(b*b)*(b*b)) (num 15*denominatorSquare a b*denominatorSquare a b)
def lowerMargin (a b : PTm n) : PTm n :=
  fraction (b*b*b*monus (num 24*a) (num 23*b))
    (num 3*denominatorSquare a b*(num 12*a+b)*(num 12*a+num 13*b))

ipra_subst upperValue [num]
ipra_subst lowerValue [num]
ipra_subst upperDifference [num]
ipra_subst lowerDifference [num]
ipra_subst firstTerm [num]
ipra_subst geometricMain [num]
ipra_subst upperMargin [num, two, one]
ipra_subst lowerMargin [num]

theorem upper_den_positive (a : PTm n) (ha : Γ ⊢[PRAAx] le one a) : Γ ⊢[PRAAx] le one (num 12*a) :=
  positive_product _ _ (small_numeral_positive 11) ha

theorem lower_den_positive (a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] le one (num 12*a+b) :=
  le_trans (upper_den_positive a ha) (le_add_right _ _)

theorem upper_telescope (a b t : PTm n) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] qadd (upperValue (a+b*t) b) (upperDifference a b t) ≐ upperValue a b := by
  let c := a+b*t
  have hc := le_trans ha (le_add_right a (b*t))
  have h₁ := upper_den_positive c hc
  have h₂ := positive_product _ _ (upper_den_positive a ha) hc
  exact (fraction_sum b (num 12*c) (b*b*t) (num 12*a*c) h₁ h₂).eqTrans
    (fraction_same _ _ _ _ (positive_product _ _ h₁ h₂) (upper_den_positive a ha) (by dsimp [c]; ipra_ring))

theorem lower_telescope (a b t : PTm n) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] qadd (lowerValue (a+b*t) b) (lowerDifference a b t) ≐ lowerValue a b := by
  let c := a+b*t
  have hc := le_trans ha (le_add_right a (b*t))
  have h₁ := lower_den_positive c b hc
  have h₂ := positive_product _ _ (lower_den_positive a b ha) h₁
  exact (fraction_sum b (num 12*c+b) (num 12*b*b*t) ((num 12*a+b)*(num 12*c+b)) h₁ h₂).eqTrans
    (fraction_same _ _ _ _ (positive_product _ _ h₁ h₂) (lower_den_positive a b ha) (by dsimp [c]; ipra_ring))

theorem upper_cell (a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] qadd (upperValue (a+b) b) (geometricMain a b) ≐ upperValue a b := by
  have e : Γ ⊢[PRAAx] geometricMain a b ≐ upperDifference a b one := by
    apply GaussianCompactRiemannName.fraction_congr
    · ipra_ring
    · unfold gap; ipra_ring
  have later : Γ ⊢[PRAAx] upperValue (a+b) b ≐ upperValue (a+b*one) b :=
    GaussianCompactRiemannName.fraction_congr _ _ _ _ (.eqRefl _) (by ipra_ring)
  exact (qadd_congr later e).eqTrans (upper_telescope a b one ha)

theorem lower_cell_margin (a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (hba : Γ ⊢[PRAAx] le b a) :
    Γ ⊢[PRAAx] qadd (lowerDifference a b one) (lowerMargin a b) ≐ firstTerm a b := by
  let w := denominatorSquare a b
  let l := num 12*a+b
  let m := num 12*a+num 13*b
  let r := monus (num 24*a) (num 23*b)
  have h₁ := lower_den_positive a b ha
  have h₂ : Γ ⊢[PRAAx] le one m := le_trans (upper_den_positive a ha) (le_add_right _ _)
  have hw := positive_product _ _ (small_numeral_positive 2) (square_positive a b hb)
  have h₃ := positive_product _ _ h₁ h₂
  have h₄ := positive_product _ _ (positive_product _ _ hw h₁) h₂
  have e : Γ ⊢[PRAAx] lowerDifference a b one ≐ fraction (num 12*b*b) (l*m) :=
    GaussianCompactRiemannName.fraction_congr _ _ _ _ (by ipra_ring) (by unfold l m; ipra_ring)
  have lower : Γ ⊢[PRAAx] le (num 23*b) (num 24*a) := by
    ipra_le 23*sl hba+𝔞 a
  have residue : Γ ⊢[PRAAx] num 24*a ≐ num 23*b+r := eq_add_of_le lower
  have he := natEq residue
  exact (qadd_congr e (.eqRefl _)).eqTrans
    ((fraction_sum (num 12*b*b) (l*m) (b*b*b*r) (num 3*w*l*m) h₃ h₄).eqTrans
      (fraction_same _ _ _ _ (positive_product _ _ h₃ h₄) hw (by
        unfold w denominatorSquare l m
        apply deriveNat
        ipra_simps
        linear_combination -(3*(2*𝔞 a+𝔞 b)^2*(12*𝔞 a+𝔞 b)*(12*𝔞 a+13*𝔞 b)*(𝔞 b)^3)*he)))

theorem lower_margin_numerator_positive (a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hba : Γ ⊢[PRAAx] le b a) :
    Γ ⊢[PRAAx] le one (monus (num 24*a) (num 23*b)) := by
  have h : Γ ⊢[PRAAx] le (num 23*b+one) (num 24*a) := by ipra_le 23*sl hba+sl ha
  have k := le_trans (le_add_right (num 23*b) one) h
  exact le_of_add_le_add_right (c := num 23*b)
    (le_congr (add_comm _ _) ((eq_add_of_le k).eqTrans (add_comm _ _)) h)

end LeanProofs.IPRA.Analysis.GaussianStirlingRationalTelescopers

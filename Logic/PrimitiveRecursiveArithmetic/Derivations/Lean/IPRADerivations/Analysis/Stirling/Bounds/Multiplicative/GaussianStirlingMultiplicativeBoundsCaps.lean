import IPRADerivations.Analysis.Stirling.Bounds.Multiplicative.GaussianStirlingMultiplicativeBounds

/-!
# Strict rational barriers for the Stirling quotient

The lower comparison uses a rational factor strictly above one. The
upper square barrier has an exact positive rational gap to
12a/(12a-b), so the strict relative-error inequality follows internally.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingMultiplicativeBoundsCaps

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianEulerPowerChartTimeOrder (order_trans)
open GaussianNamedPositiveExponentialOrder (realOrder real_order_at)
open GaussianNamedRealOrderTransport (precision upperSlack remove_upper_slack)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (positive_product)
open GaussianStirlingMultiplicative (quotientF quotientData)
open GaussianStirlingMultiplicativeAlgebra (remainderF remainderData)
open GaussianStirlingMultiplicativeBounds (upperBase upperDen upperFactor lowerFactor conventionalUpper
  relative_interval threshold_positive weak_lower_log)
open GaussianStirlingMultiplicativeBoundsLog (constant_order fractions_order)
open GaussianStirlingMultiplicativeBoundsOrder (fraction_real_part)
open GaussianStirlingNames (source)
open GaussianStirlingRationalTelescopers (denominatorSquare square_positive lower_den_positive small_numeral_positive)
open RationalArgmin (rationalLE rationalLE_congr)
open RationalValueBounds (upper upper_mono upper_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

private theorem constant_order_exact (a b : PTm n) (h : Γ ⊢[PRAAx] realOrder constantF constantF a b) :
    Γ ⊢[PRAAx] rationalLE (fstT a) (fstT b) := by
  let x := fstT a
  let y := fstT b
  let p := precision x y one two
  have hp := unit_positive (Γ := Γ) p
  have first := upper_congr (congrFst (constant_at p a)) (congrFst (constant_at p b))
    (.eqRefl _) (.eqRefl _) (real_order_at constantF constantF a b p p h)
  have slack : Γ ⊢[PRAAx] upperSlack x y zero one two p := by
    unfold upperSlack
    exact RationalValueBounds.upper_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (one_mul _).eqSymm
      (RationalValueBounds.upper_two_errors_same hp first)
  have exactBound := remove_upper_slack x y zero one two slack
  exact le_congr (by unfold RationalValueBounds.crossLeft RationalArgmin.left; ipra_ring)
    (by unfold RationalValueBounds.crossLeft RationalArgmin.left; ipra_ring) exactBound

theorem strict_fractions (a b c d : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] lt (d*a) (c*b)) :
    Γ ⊢[PRAAx] neg (realOrder constantF constantF (fraction c d) (fraction a b)) := by
  refine .impI ?_
  let Δ := realOrder constantF constantF (fraction c d) (fraction a b) :: Γ
  have exactOrder := constant_order_exact (Γ := Δ) (fraction c d) (fraction a b) Prf.hyp0
  have natRat := rationalLE_congr (fraction_real_part c d hd.wk) (fraction_real_part a b hb.wk) exactOrder
  have clear := GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _
    (GaussianEuclideanDistanceName.fraction_represents c d hd.wk)
    (GaussianEuclideanDistanceName.fraction_represents a b hb.wk) natRat
  exact lt_irrefl _ _ (lt_of_lt_of_le h.wk (le_congr (mul_comm _ _) (mul_comm _ _) clear))

theorem cap_denominator (a b : PTm n) (_hs : Γ ⊢[PRAAx] source a b) (hba : Γ ⊢[PRAAx] le b a) :
    Γ ⊢[PRAAx] le (num 6*a) (monus (upperDen a) b) ⋏
      (monus (upperDen a) b+b ≐ upperDen a) := by
  have far : Γ ⊢[PRAAx] le (num 6*a+b) (upperDen a) := by unfold upperDen; ipra_le sl hba+5*𝔞 a
  have e := (eq_add_of_le (le_trans (le_add_left _ _) far)).eqTrans (add_comm _ _)
  exact .andI (le_of_add_le_add_right (c := b) (le_congr (.eqRefl _) e far)) e.eqSymm

theorem cap_strict (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hba : Γ ⊢[PRAAx] le b a) :
    Γ ⊢[PRAAx] realOrder constantF constantF (upperFactor a b) (conventionalUpper a b) ⋏
      neg (realOrder constantF constantF (conventionalUpper a b) (upperFactor a b)) := by
  let t := upperBase a b
  let s := monus (upperDen a) b
  let D := upperDen a
  let X := (t+b)*(t+b)
  let Y := t*t
  have e := threshold_positive a b hs hba
  have e' := cap_denominator a b hs hba
  have hY := positive_product _ _ e.andE₁ e.andE₁
  have hS := le_trans (positive_product _ _ (small_numeral_positive 5) hs.andE₁) e'.andE₁
  have hD := GaussianStirlingRationalTelescopers.upper_den_positive a hs.andE₁
  have diff : Γ ⊢[PRAAx] s*X+D*b*b ≐ D*Y := by
    have ht := natEq e.andE₂
    have hu := natEq e'.andE₂
    change 𝔞 (t+b) = 𝔞 (two*D) at ht
    change 𝔞 (s+b) = 𝔞 D at hu
    have tVal : 𝔞 t = 2*𝔞 D-𝔞 b := by ipra_simps; linear_combination ht
    have sVal : 𝔞 s = 𝔞 D-𝔞 b := by ipra_simps; linear_combination hu
    apply deriveNat
    dsimp only [X,Y]
    ipra_simps
    rw [tVal,sVal]
    ring
  have positive : Γ ⊢[PRAAx] le one (D*b*b) :=
    positive_product _ _ (positive_product _ _ hD hs.andE₂) hs.andE₂
  have clear : Γ ⊢[PRAAx] lt (s*X) (D*Y) :=
    le_congr (succ_eq_add_one (s*X)).eqSymm diff
      (by ipra_le sl positive)
  exact .andI (constant_order _ _ (fractions_order X Y D s hY hS (le_of_lt clear)))
    (strict_fractions X Y D s hY hS clear)

theorem conventional_le_factor (a b k : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hba : Γ ⊢[PRAAx] le b a)
    (hk : Γ ⊢[PRAAx] le one k) (hK : Γ ⊢[PRAAx] le k (monus (upperDen a) b)) :
    Γ ⊢[PRAAx] realOrder constantF constantF (conventionalUpper a b) (fraction (k+b) k) := by
  let s := monus (upperDen a) b
  have e := cap_denominator a b hs hba
  have hS := le_trans hk hK
  have h : Γ ⊢[PRAAx] le (k*upperDen a) ((k+b)*s) :=
    le_congr (congrMul (.eqRefl k) e.andE₂) (.eqRefl _) (by ipra_le 𝔞 b*sl hK)
  exact constant_order _ _ (fractions_order _ _ _ _ hS hk h)

theorem strict_lower_order (f : PR 2) (y m d : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hd : Γ ⊢[PRAAx] le one d) (lo : Γ ⊢[PRAAx] realOrder constantF f (lowerFactor m d) y) :
    Γ ⊢[PRAAx] realOrder constantF f (fraction one one) y ⋏ neg (realOrder f constantF y (fraction one one)) := by
  have sep : Γ ⊢[PRAAx] lt (d*one) ((d+m)*one) := by
    change Γ ⊢[PRAAx] le (succ (d*one)) ((d+m)*one)
    ipra_le sl hm
  have first := constant_order (Γ := Γ) _ _ (fractions_order one one (d+m) d (le_refl one) hd (le_of_lt sep))
  have strict := strict_fractions one one (d+m) d (le_refl one) hd sep
  refine .andI (order_trans _ _ _ _ _ _ first lo) (.impI ?_)
  exact strict.wk.impE (order_trans _ _ _ _ _ _ lo.wk Prf.hyp0)

theorem strict_upper_order (f : PR 2) (y a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hba : Γ ⊢[PRAAx] le b a)
    (hi : Γ ⊢[PRAAx] realOrder f constantF y (upperFactor a b)) :
    Γ ⊢[PRAAx] realOrder f constantF y (conventionalUpper a b) ⋏
      neg (realOrder constantF f (conventionalUpper a b) y) := by
  have cap := cap_strict a b hs hba
  refine .andI (order_trans _ _ _ _ _ _ hi cap.andE₁) (.impI ?_)
  exact cap.andE₂.wk.impE (order_trans _ _ _ _ _ _ Prf.hyp0 hi.wk)

def interval (f : PR 2) (a b y : PTm n) : Fm PTm n :=
  (realOrder constantF f (fraction one one) y ⋏ neg (realOrder f constantF y (fraction one one))) ⋏
  (realOrder f constantF y (conventionalUpper a b) ⋏ neg (realOrder constantF f (conventionalUpper a b) y))

theorem strict_interval (f : PR 2) (a b y m d : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hba : Γ ⊢[PRAAx] le b a)
    (hm : Γ ⊢[PRAAx] le one m) (hd : Γ ⊢[PRAAx] le one d)
    (lo : Γ ⊢[PRAAx] realOrder constantF f (lowerFactor m d) y)
    (hi : Γ ⊢[PRAAx] realOrder f constantF y (upperFactor a b)) : Γ ⊢[PRAAx] interval f a b y :=
  .andI (strict_lower_order _ _ _ _ hm hd lo) (strict_upper_order _ _ _ _ hs hba hi)

theorem integer_interval (i x : PTm n) (hi : Γ ⊢[PRAAx] le one i) :
    Γ ⊢[PRAAx] interval quotientF i one (quotientData i one x) := by
  let y := remainderData i one x
  let d := upperDen i+one
  have hs : Γ ⊢[PRAAx] source i one := .andI hi (le_refl one)
  have bounds := GaussianStirlingRobbins.integer_bounds i x hi
  have lo := order_trans constantF constantF remainderF _ _ y (weak_lower_log i one hs) bounds.andE₁
  have hd := lower_den_positive i one hi
  have pair := relative_interval i one x one d hs hi hd lo bounds.andE₂
  exact strict_interval _ _ _ _ _ _ hs hi (le_refl one) hd pair.andE₁ pair.andE₂

theorem rational_interval (a b x : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hba : Γ ⊢[PRAAx] le b a)
    (bounds : Γ ⊢[PRAAx] GaussianStirlingGlobalBounds.firstOrderBounds remainderF a b (remainderData a b x)) :
    Γ ⊢[PRAAx] interval quotientF a b (quotientData a b x) ⋏
      realOrder quotientF constantF (quotientData a b x) (fraction (num 6*a+b) (num 6*a)) := by
  let d := num 3*denominatorSquare a b
  have hd := positive_product _ _ (small_numeral_positive 2) (square_positive a b hs.andE₂)
  have pair := relative_interval a b x (b*b) d hs hba hd bounds.andE₁ bounds.andE₂
  have ival := strict_interval _ _ _ _ _ _ hs hba (positive_product _ _ hs.andE₂ hs.andE₂) hd pair.andE₁ pair.andE₂
  exact .andI ival (order_trans _ _ _ _ _ _ ival.andE₂.andE₁
    (conventional_le_factor a b (num 6*a) hs hba (positive_product _ _ (small_numeral_positive 5) hs.andE₁)
      (cap_denominator a b hs hba).andE₁))

end LeanProofs.IPRA.Analysis.GaussianStirlingMultiplicativeBoundsCaps

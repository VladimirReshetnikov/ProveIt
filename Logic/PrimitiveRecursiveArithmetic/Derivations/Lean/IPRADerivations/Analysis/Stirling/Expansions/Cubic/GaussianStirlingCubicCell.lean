import IPRADerivations.Analysis.Stirling.Telescoping.GaussianStirlingDifferenceBounds
import IPRADerivations.Analysis.Stirling.Bounds.Logarithmic.GaussianStirlingGlobalBoundsFinite

/-!
# The strict cubic correction on a single Stirling cell

Write u=b², w=(2a+b)² and g=4a(a+b), so w=g+u.
Subtracting the elementary upper-cell contribution from the first two
odd-series terms and the difference of the cubic correction leaves
u³(5g²+22gu+8u²)/(45g³w²). The numerator has positive coefficients.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingCubicCell

open_ipra
open GaussianCoefficientNameBounds (unit)
open GaussianEulerPositivePowerChartCorrectedImage (fraction_sum)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (canonical ofGaussian_canonical qadd qadd_canonical qzero positive_product)
open GaussianRationalMetric (qsub qsub_canonical)
open GaussianRationalSyntheticDivision (qadd_congr qsub_congr qzero_add)
open GaussianStirlingDifferenceBrackets (observation_brackets)
open GaussianStirlingNames (source)
open GaussianStirlingOddSeries (partialSum partial_zero partial_succ term degree baseDenominator)
open GaussianStirlingRationalTelescopers (firstTerm geometricMain gap denominatorSquare numeratorSquare
  fraction_same square_split gap_positive square_positive small_numeral_positive upperValue upper_den_positive)
open GaussianStirlingTailComparison (point_add_order point_order_refl)
open RationalArgmin (rationalLE rationalLE_congr)
open RationalValueBounds (upper upper_congr upper_order_left)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "D" => GaussianStirlingDifference.nameF
local notation "DD" => GaussianStirlingDifference.data

def cube (a : PTm n) : PTm n := a*a*a
def fourth (a : PTm n) : PTm n := a*a*a*a
def secondTerm (a b : PTm n) : PTm n := fraction (fourth b) (num 5*(denominatorSquare a b*denominatorSquare a b))
def cubicValue (a b : PTm n) : PTm n := fraction (cube b) (num 360*cube a)
def cellCorrection (a b : PTm n) : PTm n :=
  fraction (two*fourth b*(num 3*denominatorSquare a b+numeratorSquare b)) (num 45*cube (gap a b))
def correctedCell (a b : PTm n) : PTm n := qsub (geometricMain a b) (cellCorrection a b)
def marginNumerator (a b : PTm n) : PTm n :=
  let g := gap a b
  let u := numeratorSquare b
  cube u*(num 5*g*g+num 22*g*u+num 8*u*u)
def marginDenominator (a b : PTm n) : PTm n :=
  num 45*cube (gap a b)*denominatorSquare a b*denominatorSquare a b
def margin (a b : PTm n) : PTm n := fraction (marginNumerator a b) (marginDenominator a b)

ipra_subst cube
ipra_subst fourth
ipra_subst cubicValue
ipra_subst correctedCell [cellCorrection, num, two, one]
ipra_subst margin [marginNumerator, marginDenominator, num]

theorem cube_positive (a : PTm n) (h : Γ ⊢[PRAAx] le one a) : Γ ⊢[PRAAx] le one (cube a) :=
  positive_product _ _ (positive_product _ _ h h) h

private theorem raise (a : PTm n) : Γ ⊢[PRAAx] pw a (num 4) ≐ fourth a := by
  have square : Γ ⊢[PRAAx] pw a two ≐ a*a :=
    (pw_succ a one).eqTrans (congrMul (pw_one a) (.eqRefl a))
  have cubic := (pw_succ a two).eqTrans (congrMul square (.eqRefl a))
  exact (pw_succ a (num 3)).eqTrans (congrMul cubic (.eqRefl a))

private theorem partial_two (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] partialSum a b two ≐ qadd (firstTerm a b) (secondTerm a b) := by
  let t := two*a+b
  let w := denominatorSquare a b
  have hw := square_positive a b hb
  have e0 : Γ ⊢[PRAAx] term a b zero ≐ firstTerm a b := by
    unfold term firstTerm
    have degree0 : Γ ⊢[PRAAx] degree (zero : PTm n) ≐ two := by unfold degree; ipra_ring
    have sq (x : PTm n) : Γ ⊢[PRAAx] pw x two ≐ x*x :=
      (pw_succ x one).eqTrans (congrMul (pw_one x) (.eqRefl x))
    exact GaussianCompactRiemannName.fraction_congr _ _ _ _
      ((congrAp2 powF degree0 (.eqRefl b)).eqTrans (sq b))
      (congrMul (congrSucc degree0) ((congrAp2 powF degree0 (.eqRefl t)).eqTrans (sq t)))
  have e1 : Γ ⊢[PRAAx] term a b one ≐ secondTerm a b := by
    unfold term secondTerm
    have degree1 : Γ ⊢[PRAAx] degree (one : PTm n) ≐ num 4 := by unfold degree; ipra_ring
    exact GaussianCompactRiemannName.fraction_congr _ _ _ _
      ((congrAp2 powF degree1 (.eqRefl b)).eqTrans (raise b))
      (congrMul (congrSucc degree1) ((congrAp2 powF degree1 (.eqRefl t)).eqTrans
        ((raise t).eqTrans (by dsimp [t,denominatorSquare,fourth]; ipra_ring))))
  have first := (partial_succ a b zero).eqTrans
    ((qadd_congr (partial_zero a b) e0).eqTrans (qzero_add _
      (ofGaussian_canonical _ _ (positive_product _ _ (small_numeral_positive 2) hw))))
  exact (partial_succ a b one).eqTrans (qadd_congr first e1)

theorem cubic_den_positive (a : PTm n) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] le one (num 360*cube a) :=
  positive_product _ _ (small_numeral_positive 359) (cube_positive a ha)

theorem margin_den_positive (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] le one (marginDenominator a b) := by
  have hw := square_positive a b hs.andE₂
  exact positive_product _ _ (positive_product _ _ (positive_product _ _ (small_numeral_positive 44)
    (cube_positive _ (gap_positive a b hs.andE₁))) hw) hw

theorem margin_num_positive (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] le one (marginNumerator a b) := by
  let u := numeratorSquare b
  let g := gap a b
  have hu := positive_product _ _ hs.andE₂ hs.andE₂
  have hg := gap_positive a b hs.andE₁
  have hp : Γ ⊢[PRAAx] le one (num 5*g*g) :=
    positive_product _ _ (positive_product _ _ (small_numeral_positive 4) hg) hg
  exact positive_product _ _ (cube_positive u hu)
    (le_trans (le_trans hp (le_add_right _ _)) (le_add_right _ _))

theorem cubic_telescope_cell (a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] qadd (cubicValue (a+b) b) (cellCorrection a b) ≐ cubicValue a b := by
  let w := denominatorSquare a b
  let u := numeratorSquare b
  let g := gap a b
  let E := num 360*cube (a+b)
  let F := num 45*cube g
  let J := two*fourth b*(num 3*w+u)
  have hE : Γ ⊢[PRAAx] le one E := cubic_den_positive _ (le_trans ha (le_add_right _ _))
  have hF : Γ ⊢[PRAAx] le one F :=
    positive_product _ _ (small_numeral_positive 44) (cube_positive _ (gap_positive a b ha))
  exact (fraction_sum (cube b) E J F hE hF).eqTrans
    (fraction_same _ _ _ _ (positive_product _ _ hE hF) (cubic_den_positive a ha)
      (by dsimp [E,F,J,cube,fourth,w,u,g,gap,denominatorSquare,numeratorSquare]; ipra_ring))

/-- Exact certificate before subtraction. All four operands are positive fractions. -/
theorem margin_balance (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] qadd (geometricMain a b) (margin a b) ≐
      qadd (partialSum a b two) (cellCorrection a b) := by
  let w := denominatorSquare a b
  let u := numeratorSquare b
  let g := gap a b
  let k := num 45*cube g
  let j := two*fourth b*(num 3*w+u)
  let l := num 3*w
  let m := num 5*(w*w)
  let e := marginDenominator a b
  have hw := square_positive a b hs.andE₂
  have hg := gap_positive a b hs.andE₁
  have hk : Γ ⊢[PRAAx] le one k := positive_product _ _ (small_numeral_positive 44) (cube_positive g hg)
  have hl : Γ ⊢[PRAAx] le one l := positive_product _ _ (small_numeral_positive 2) hw
  have hm : Γ ⊢[PRAAx] le one m :=
    positive_product _ _ (small_numeral_positive 4) (positive_product _ _ hw hw)
  have hn := positive_product _ _ hl hm
  have hG := positive_product _ _ (small_numeral_positive 2) hg
  have he := margin_den_positive a b hs
  have poly := (fraction_sum u l (fourth b) m hl hm)
  have left := fraction_sum u (num 3*g) (marginNumerator a b) e hG he
  have right := fraction_sum (u*m+fourth b*l) (l*m) j k hn hk
  have value := fraction_same (u*e+marginNumerator a b*(num 3*g)) ((num 3*g)*e)
    ((u*m+fourth b*l)*k+j*(l*m)) ((l*m)*k) (positive_product _ _ hG he) (positive_product _ _ hn hk)
    (by
      have h := natEq (square_split (Γ := Γ) a b)
      dsimp [l,m,k,j,e,marginDenominator,marginNumerator,cube,fourth,w,u,g] at h ⊢
      apply deriveNat
      ipra_simps
      rw [h]
      dsimp [numeratorSquare]
      ipra_simps
      ring)
  exact left.eqTrans (value.eqTrans (right.eqSymm.eqTrans
    (qadd_congr (poly.eqSymm.eqTrans (partial_two a b hs.andE₂).eqSymm) (.eqRefl _))))

theorem corrected_cell_margin (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] qadd (correctedCell a b) (margin a b) ≐ partialSum a b two := by
  let u := geometricMain a b
  let m := margin a b
  let c := cellCorrection a b
  let r := partialSum a b two
  have reorder : Γ ⊢[PRAAx] qadd (qsub u c) m ≐ qsub (qadd u m) c := by
    change Γ ⊢[PRAAx] qadd (qadd u (GaussianRationalMetric.qnegative c)) m ≐
      qadd (qadd u m) (GaussianRationalMetric.qnegative c)
    exact GaussianStirlingGlobalBoundsFinite.swap_suffix _ _ _
  exact reorder.eqTrans ((qsub_congr (margin_balance a b hs) (.eqRefl _)).eqTrans
    (GaussianReciprocalHorner.qsub_add_cancel r c (GaussianStirlingOddSeries.partial_canonical _ _ _)))

theorem cell_observation (p a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] upper (fstT (qadd (correctedCell a b) (margin a b))) (fstT (ap2 D p (DD a b))) one (unit p) :=
  upper_congr (congrFst (corrected_cell_margin a b hs).eqSymm) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (observation_brackets a b two p hs.andE₁ hs.andE₂).andE₁

end LeanProofs.IPRA.Analysis.GaussianStirlingCubicCell

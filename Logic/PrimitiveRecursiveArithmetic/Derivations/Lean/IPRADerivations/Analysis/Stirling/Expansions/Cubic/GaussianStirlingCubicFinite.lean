import IPRADerivations.Analysis.Stirling.Expansions.Cubic.GaussianStirlingCubicCell

/-!
# Finite telescoping of the signed cubic Stirling comparison

Keep the first positive cell margin. Sum the weak cell inequalities
after that, leaving the cubic contribution on the right so that the
finite caps themselves use natural fractions.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingCubicFinite

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEulerPositivePowerChartCorrectedImage (fraction_sum)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (canonical qadd qadd_canonical positive_product ofGaussian_canonical qzero)
open GaussianRationalSyntheticDivision (qadd_congr qsub_congr)
open GaussianRationalSumAlgebra (qadd_associative)
open GaussianReciprocalHorner (qadd_commutative qsub_add_cancel qadd_zero_right)
open GaussianStirlingCubicCell (cube cubicValue cubic_den_positive cellCorrection cubic_telescope_cell margin
  margin_den_positive margin_balance)
open GaussianStirlingDifferenceBrackets (observation_brackets)
open GaussianStirlingGlobalBoundsFinite (swap_suffix raw_first raw_step)
open GaussianStirlingNames (source)
open GaussianStirlingRationalTelescopers (geometricMain upperValue upperDifference upper_telescope upper_cell
  upper_den_positive fraction_same small_numeral_positive)
open GaussianStirlingTailComparison (point_add_order point_add_upper_same point_order_refl)
open GaussianStirlingTelescope (shifted shifted_source rawSum)
open RationalArgmin (rationalLE rationalLE_congr)
open RationalValueBounds (upper upper_congr upper_of_order upper_order_left)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "D" => GaussianStirlingDifference.nameF
local notation "DD" => GaussianStirlingDifference.data

def cubicDifference (N a b : PTm n) : PTm n :=
  let e := b*N
  let Y := shifted a b N
  fraction (cube b*e*(num 3*a*a+num 3*a*e+e*e)) (num 360*cube a*cube Y)

ipra_subst cubicDifference

theorem cubic_diff_den_positive (N a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] le one (num 360*cube a*cube (shifted a b N)) :=
  positive_product _ _ (cubic_den_positive _ hs.andE₁)
    (GaussianStirlingCubicCell.cube_positive _ (shifted_source a b N hs).andE₁)

theorem cubic_telescope (N a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] qadd (cubicValue (shifted a b N) b) (cubicDifference N a b) ≐ cubicValue a b := by
  let e := b*N
  let Y := shifted a b N
  let K := cube b*e*(num 3*a*a+num 3*a*e+e*e)
  let M := num 360*cube a*cube Y
  let R := num 360*cube Y
  have hR : Γ ⊢[PRAAx] le one R := cubic_den_positive _ (shifted_source a b N hs).andE₁
  have hM : Γ ⊢[PRAAx] le one M := cubic_diff_den_positive N a b hs
  exact (fraction_sum (cube b) R K M hR hM).eqTrans
    (fraction_same _ _ _ _ (positive_product _ _ hR hM) (cubic_den_positive a hs.andE₁)
      (by dsimp [e,Y,K,M,R,cube,shifted]; ipra_ring))

private theorem extend (d c e x y z : PTm n)
    (h0 : Γ ⊢[PRAAx] qadd y d ≐ x) (h1 : Γ ⊢[PRAAx] qadd z c ≐ y)
    (h2 : Γ ⊢[PRAAx] qadd z e ≐ x) (he : Γ ⊢[PRAAx] canonical e) :
    Γ ⊢[PRAAx] qadd d c ≐ e := by
  have h : Γ ⊢[PRAAx] qadd (qadd d c) z ≐ qadd e z :=
    (qadd_associative d c z).eqTrans
      ((qadd_congr (.eqRefl d) ((qadd_commutative c z).eqTrans h1)).eqTrans
        ((qadd_commutative d y).eqTrans (h0.eqTrans (h2.eqSymm.eqTrans (qadd_commutative z e)))))
  exact (qsub_add_cancel _ _ (qadd_canonical _ _)).eqSymm.eqTrans
    ((qsub_congr h (.eqRefl _)).eqTrans (qsub_add_cancel e z he))

private theorem shift_succ (N a b : PTm n) :
    Γ ⊢[PRAAx] shifted a b (succ N) ≐ shifted a b N+b := by unfold shifted; ipra_ring

private theorem cube_fraction_congr (a c b : PTm n) (h : Γ ⊢[PRAAx] a ≐ c) :
    Γ ⊢[PRAAx] cubicValue a b ≐ cubicValue c b := by
  unfold cubicValue cube
  exact GaussianCompactRiemannName.fraction_congr _ _ _ _ (.eqRefl _)
    (congrMul (.eqRefl _) (congrMul (congrMul h h) h))

theorem cubic_step (N a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] qadd (cubicDifference N a b) (cellCorrection (shifted a b N) b) ≐ cubicDifference (succ N) a b := by
  let correction := cellCorrection (shifted a b N) b
  have h := qadd_congr (Γ := Γ) (cube_fraction_congr _ _ b (shift_succ N a b)) (.eqRefl correction)
  exact extend _ _ _ _ _ _ (cubic_telescope N a b hs)
    (h.eqTrans (cubic_telescope_cell _ _ (shifted_source a b N hs).andE₁))
    (cubic_telescope (succ N) a b hs) (ofGaussian_canonical _ _ (cubic_diff_den_positive (succ N) a b hs))

private theorem upper_diff_canonical (N a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] canonical (upperDifference a b N) :=
  ofGaussian_canonical _ _ (positive_product _ _ (upper_den_positive _ hs.andE₁) (shifted_source a b N hs).andE₁)

theorem upper_step (N a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] qadd (upperDifference a b N) (geometricMain (shifted a b N) b) ≐ upperDifference a b (succ N) := by
  let mainTerm := geometricMain (shifted a b N) b
  have h := qadd_congr (Γ := Γ) (GaussianCompactRiemannName.fraction_congr _ _ _ _ (.eqRefl b)
    (congrMul (.eqRefl (num 12)) (shift_succ N a b))) (.eqRefl mainTerm)
  exact extend _ _ _ _ _ _ (upper_telescope a b N hs.andE₁)
    (h.eqTrans (upper_cell _ _ (shifted_source a b N hs).andE₁))
    (upper_telescope a b (succ N) hs.andE₁) (upper_diff_canonical (succ N) a b hs)

private theorem cubic_first (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] cubicDifference one a b ≐ cellCorrection a b := by
  have shifted_one : Γ ⊢[PRAAx] shifted a b one ≐ a+b := by unfold shifted; ipra_ring
  have e := qadd_congr (cube_fraction_congr _ _ b shifted_one) (.eqRefl (cubicDifference one a b))
  have both := e.eqSymm.eqTrans ((cubic_telescope one a b hs).eqTrans (cubic_telescope_cell a b hs.andE₁).eqSymm)
  have h := (qadd_commutative _ _).eqTrans (both.eqTrans (qadd_commutative _ _))
  have hc : Γ ⊢[PRAAx] canonical (cellCorrection a b) :=
    ofGaussian_canonical _ _ (positive_product _ _ (small_numeral_positive 44)
      (GaussianStirlingCubicCell.cube_positive _ (GaussianStirlingRationalTelescopers.gap_positive a b hs.andE₁)))
  exact (qsub_add_cancel _ _ (ofGaussian_canonical _ _ (cubic_diff_den_positive one a b hs))).eqSymm.eqTrans
    ((qsub_congr h (.eqRefl _)).eqTrans (qsub_add_cancel _ _ hc))

private theorem upper_first (a b : PTm n) :
    Γ ⊢[PRAAx] upperDifference a b one ≐ geometricMain a b := by
  apply GaussianCompactRiemannName.fraction_congr
  · ipra_ring
  · unfold GaussianStirlingRationalTelescopers.gap
    ipra_ring

theorem strong_cell (p a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] upper (fstT (qadd (geometricMain a b) (margin a b)))
      (fstT (qadd (ap2 D p (DD a b)) (cellCorrection a b))) one (unit p) := by
  let J := cellCorrection a b
  have h := (observation_brackets a b two p hs.andE₁ hs.andE₂).andE₁
  have same := upper_of_order (Γ := Γ) _ _ zero (unit p) (point_order_refl J)
  exact upper_congr (congrFst (margin_balance a b hs).eqSymm) (.eqRefl _) (add_zero one) (.eqRefl _)
    (point_add_upper_same _ _ _ _ _ _ _ (unit_positive p) h same)

private theorem weak_cell (p a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] upper (fstT (geometricMain a b))
      (fstT (qadd (ap2 D p (DD a b)) (cellCorrection a b))) one (unit p) := by
  let L := geometricMain a b
  have c : Γ ⊢[PRAAx] canonical L := ofGaussian_canonical _ _
    (positive_product _ _ (small_numeral_positive 2) (GaussianStirlingRationalTelescopers.gap_positive a b hs.andE₁))
  have h := (GaussianRationalNonnegativeFractions.fraction_nonnegative (GaussianStirlingCubicCell.marginNumerator a b)
    _ (margin_den_positive a b hs)).andE₁
  have z := rationalLE_congr RationalGaussianRealPart.real_zero.eqSymm (.eqRefl _) h
  have le := point_add_order L L qzero (margin a b) (point_order_refl L) z
  exact upper_order_left _ _ _ _ _
    (rationalLE_congr (congrFst (qadd_zero_right L c)) (.eqRefl _) le) (strong_cell p a b hs)

def rawLower (p N a b : PTm n) : Fm PTm n :=
  upper (fstT (qadd (upperDifference a b (succ N)) (margin a b)))
    (fstT (qadd (rawSum p (succ N) a b) (cubicDifference (succ N) a b))) (succ N) (unit p)

ipra_subst rawLower

private theorem raw_succ (p N a b : PTm n) (hs : Γ ⊢[PRAAx] source a b)
    (h : Γ ⊢[PRAAx] rawLower p N a b) : Γ ⊢[PRAAx] rawLower p (succ N) a b := by
  let t := succ N
  let c := shifted a b t
  let X := upperDifference a b t
  let Y := rawSum p t a b
  let J := cubicDifference t a b
  let G := geometricMain c b
  let K := cellCorrection c b
  let P := ap2 D p (DD c b)
  let M := margin a b
  have next := weak_cell p c b (shifted_source a b t hs)
  have both := point_add_upper_same (qadd X M) (qadd Y J) G (qadd P K) t one (unit p) (unit_positive p) h next
  have L := (swap_suffix X M G).eqTrans (qadd_congr (upper_step t a b hs) (.eqRefl M))
  have R := (GaussianRationalFiniteSum.add_shuffle Y J P K).eqTrans
    (qadd_congr (raw_step p t a b).eqSymm (cubic_step t a b hs))
  exact upper_congr (congrFst L) (congrFst R) (succ_eq_add_one t).eqSymm (.eqRefl _) both

theorem raw_lower (p N a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx] rawLower p N a b := by
  let sh (x : PTm n) := Syn.shift x
  have hall : Γ ⊢[PRAAx] .all (rawLower (sh p) (var 0) (sh a) (sh b)) := by
    ipra_qfind (le_QF _ _) [subst_rawLower, sh]
    · exact upper_congr (congrFst (qadd_congr (upper_first a b).eqSymm (.eqRefl _)))
        (congrFst (qadd_congr (raw_first p a b).eqSymm (cubic_first a b hs).eqSymm))
        (.eqRefl _) (.eqRefl _) (strong_cell p a b hs)
    · let Δ := rawLower (sh p) (var 0) (sh a) (sh b) :: Γ.map Fm.shift
      have hs' : Δ ⊢[PRAAx] source (sh a) (sh b) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hs.shift.wk
      exact raw_succ _ _ _ _ hs' Prf.hyp0
  simpa only [subst_rawLower,sh,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using hall.allE N

end LeanProofs.IPRA.Analysis.GaussianStirlingCubicFinite

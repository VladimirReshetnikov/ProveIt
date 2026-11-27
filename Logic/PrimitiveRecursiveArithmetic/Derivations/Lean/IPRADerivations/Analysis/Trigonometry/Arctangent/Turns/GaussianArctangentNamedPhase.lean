import IPRADerivations.Analysis.Trigonometry.Arctangent.Turns.GaussianArctangentExponentialPeriod
import IPRADerivations.Analysis.Names.RightHalfPlane.GaussianNamedRightHalfPlane
import IPRADerivations.Analysis.Names.Scaling.GaussianNaturalScaleProductName

/-!
# Natural and quarter arguments of the literal full turn

The angle program multiplies the original imaginary full turn by the
argument name. On constant natural and quarter inputs it agrees with the
original capped natural scaling and the literal arctangent quarter turn.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianArctangentNamedPhase

open_ipra
open ComplexLogarithmRemainder (oneCode add mul scale)
open GaussianArctangentQuarterExponential (quarterF quarter_regular)
open GaussianArctangentExponentialPeriod (twiceF twiceData fullTurnF fullTurnData fullTurnRadius original_full_turn_input)
open GaussianCoefficientNameBounds (unit)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (addF addData add_at multiplyF multiplyData multiplyModulus multiply_at multiply_fast recode_congr)
open GaussianNameEquivalence (crossEquivalent cross_symm point_at)
open GaussianRationalDistanceOrder (distance_congr distance_at_earlier_precisions)
open GaussianRationalHorner (qadd qmul positive_product canonical canonical_unique qadd_represents qmul_represents
  qadd_canonical ofGaussian_represents represents_congr represents_rescale)
open GaussianRationalL1 (rawDen rawGaussian raw_den_positive raw_represents)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr)
open GaussianRootAlgebra (equal equal_of_values re_add im_add re_mul im_mul re_scale im_scale re_one im_one)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def angleF (f : PR 2) : PR 2 := multiplyF fullTurnF f
def angleData (f : PR 2) (z x : PTm n) : PTm n := multiplyData fullTurnF f (fullTurnData z) x
def quarterPoint : PTm n := GaussianNamedRightHalfPlane.marginPoint (num 4)

ipra_subst angleData [fullTurnData, twiceData]

ipra_subst quarterPoint

theorem angle_regular (f : PR 2) (z x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] pointCN (angleF f) (angleData f z x) :=
  multiply_fast _ _ _ _ (original_full_turn_input z).andE₁ hf

theorem natural_angle_cross (E z : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent (angleF constantF) (GaussianNamedNaturalScale.nameF fullTurnF)
      (angleData constantF z (naturalPoint E)) (GaussianNamedNaturalScale.data E E (fullTurnData z)) := by
  have h := original_full_turn_input (Γ := Γ) z
  exact GaussianNameEquivalence.cross_trans _ _ _ _ _ _
    (GaussianNameRingLaws.multiply_commutative _ _ _ _ h.andE₁ (constant_regular _))
    (cross_symm _ _ _ _ (GaussianNaturalScaleProductName.scale_product_cross fullTurnF E E fullTurnRadius
      (fullTurnData z) h (le_refl E)))

private theorem quarter_canonical (p z : PTm n) :
    Γ ⊢[PRAAx] canonical (ap2 quarterF p z) :=
  GaussianRationalHorner.canonical_congr (GaussianArctangentQuarterExponential.sample_at p z)
    (GaussianRationalHorner.qmul_canonical _ _)

private theorem fourfold_over_four (q : PTm n) (hq : Γ ⊢[PRAAx] canonical q) :
    Γ ⊢[PRAAx] qmul (qadd (qadd q q) (qadd q q)) quarterPoint ≐ q := by
  let a := rawGaussian q
  let d := rawDen q
  let b := add a a
  let c := add b b
  have hd := raw_den_positive (Γ := Γ) q
  have h4 : Γ ⊢[PRAAx] le one (num 4 : PTm n) := by ipra_le 3
  have hb := qadd_represents q q a a d hd (raw_represents q) (raw_represents q)
  have hc := qadd_represents (qadd q q) (qadd q q) b b d hd hb hb
  have rep := qmul_represents _ quarterPoint c oneCode d (num 4) hd h4 hc (ofGaussian_represents _ _ h4)
  have e : Γ ⊢[PRAAx] equal (mul c oneCode) (scale (num 4) a) := by
    dsimp only [c, b]
    apply equal_of_values <;>
      simp only [re_add, im_add, re_mul, im_mul, re_scale, im_scale, re_one, im_one] <;>
      ipra_simps <;> ring
  exact canonical_unique _ _ _ (d*num 4) (GaussianRationalHorner.qmul_canonical _ _) hq
    (positive_product _ _ hd h4) (represents_congr (.eqRefl _) e (.eqRefl _) rep)
    (represents_rescale _ _ _ _ (raw_represents q))

private theorem double_at (f : PR 2) (p x : PTm n) :
    Γ ⊢[PRAAx] ap2 (addF f f) p (addData x x) ≐
      qadd (ap2 f (GaussianFastValueCut.exponent two p) x) (ap2 f (GaussianFastValueCut.exponent two p) x) :=
  (add_at f f x x p).eqTrans (GaussianExponentialReference.recode_fixed _ (qadd_canonical _ _))

private def quarterClock (p z : PTm n) : PTm n :=
  let t := GaussianFastValueCut.exponent (multiplyModulus fullTurnF constantF (fullTurnData z) quarterPoint) p
  GaussianFastValueCut.exponent two (GaussianFastValueCut.exponent two t)

private theorem quarter_angle_at (p z : PTm n) :
    Γ ⊢[PRAAx] ap2 (angleF constantF) p (angleData constantF z quarterPoint) ≐ ap2 quarterF (quarterClock p z) z := by
  let t := GaussianFastValueCut.exponent (multiplyModulus fullTurnF constantF (fullTurnData z) quarterPoint) p
  let s := GaussianFastValueCut.exponent two t
  let q := ap2 quarterF (quarterClock p z) z
  have dt : Γ ⊢[PRAAx] ap2 fullTurnF t (fullTurnData z) ≐
      qadd (ap2 twiceF s (twiceData z)) (ap2 twiceF s (twiceData z)) :=
    double_at twiceF t (twiceData z)
  have ds : Γ ⊢[PRAAx] ap2 twiceF s (twiceData z) ≐ qadd q q := double_at quarterF s z
  have eq := (qmul_congr (dt.eqTrans (qadd_congr ds ds)) (constant_at t quarterPoint)).eqTrans
    (fourfold_over_four q (quarter_canonical _ _))
  exact (multiply_at fullTurnF constantF (fullTurnData z) quarterPoint p).eqTrans
    ((recode_congr eq).eqTrans (GaussianExponentialReference.recode_fixed _ (quarter_canonical _ _)))

private theorem quarter_angle_distance (p q z : PTm n) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (angleF constantF) p (angleData constantF z quarterPoint))
      (ap2 quarterF q z) (unit p+unit q) (unit p*unit q) := by
  let k := quarterClock p z
  have hk : Γ ⊢[PRAAx] le p k := le_trans (le_add_right _ _)
    (le_trans (le_add_right _ _) (le_add_right _ _))
  have bound := distance_at_earlier_precisions p q k q hk (le_refl q)
    (point_at quarterF z k q (quarter_regular z))
  exact distance_congr (quarter_angle_at p z).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) bound

theorem quarter_angle_cross (z : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent (angleF constantF) quarterF (angleData constantF z quarterPoint) z := by
  refine .allI (.allI ?_)
  simpa only [crossEquivalent, Syn.shift, subst_angleData, subst_quarterPoint, unit, GaussianEuclideanPointDistance.unit] using
    quarter_angle_distance (Γ := (Γ.map Fm.shift).map Fm.shift) (var 1) (var 0) (Syn.shift (Syn.shift z))

theorem actual_original_natural_phase_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (crossEquivalent (angleF constantF) (GaussianNamedNaturalScale.nameF fullTurnF)
      (angleData constantF (var 1) (naturalPoint (var 0)))
      (GaussianNamedNaturalScale.data (var 0) (var 0) (fullTurnData (var 1)))) :=
  closeUniv 2 (natural_angle_cross _ _)

theorem actual_original_quarter_phase_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (crossEquivalent (angleF constantF) quarterF (angleData constantF (var 0) quarterPoint) (var 0)) :=
  closeUniv 1 (quarter_angle_cross _)

end LeanProofs.IPRA.Analysis.GaussianArctangentNamedPhase

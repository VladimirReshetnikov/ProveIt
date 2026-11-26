import IPRADerivations.Analysis.Stirling.GaussianStirlingFiniteBounds
import IPRADerivations.Analysis.RationalArithmetic.OrderBounds.RationalUpperAddition

/-!
# The exact analytic tail and the finite Stirling bounds

The analytic remainder bound has its actual odd denominator, whereas
the cleared Horner estimate uses the larger geometric tail with
denominator three. Both are compared at the original finite sum.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingTailComparison

open_ipra
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qadd positive_product qadd_canonical)
open GaussianRationalMetric (qsub qnegative)
open GaussianRationalSyntheticDivision (qadd_sub_cancel qsub_congr)
open GaussianStirlingFiniteBounds (geometricTail fraction_order sharp_upper)
open GaussianStirlingOddSeries (tail partialSum)
open GaussianStirlingRationalTelescopers
  (fraction_same numeratorSquare denominatorSquare gap gap_positive square_positive upperMargin geometricMain
   small_numeral_positive)
open RationalArgmin (rationalLE rationalLE_congr)
open RationalValueBounds (upper upper_congr upper_order_right upper_of_order)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def sharpUpperValue (a b : PTm n) : PTm n := qsub (geometricMain a b) (upperMargin a b)

ipra_subst sharpUpperValue

private theorem square_power (x K : PTm n) : Γ ⊢[PRAAx] pw x (two*K) ≐ pw (x*x) K :=
  (congrAp2 powF (by ipra_ring) (.eqRefl _)).eqTrans (AnalyticNumberTheory.EnergyWitness.pw_sq x K).eqSymm

theorem tail_value (a b K : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    tail a b K ≐ fraction (pw (numeratorSquare b) (succ K))
      (succ (two*succ K)*pw (denominatorSquare a b) K*gap a b) := by
  let u := numeratorSquare b
  let w := denominatorSquare a b
  let v := gap a b
  let J := succ (two*succ K)
  have hw := square_positive a b hb
  have hv := gap_positive a b ha
  have hJ := zero_lt_succ (Γ := Γ) (two*succ K)
  have hd (k : PTm n) : Γ ⊢[PRAAx] le one (J*pw w k*v) :=
    positive_product _ _ (positive_product _ _ hJ (GaussianFactorBudget.power_positive w k hw)) hv
  have syntactic : Γ ⊢[PRAAx] tail a b K ≐ fraction (pw u (succ K)*w) (J*pw w (succ K)*v) :=
    GaussianCompactRiemannName.fraction_congr _ _ _ _
      (congrMul (square_power b (succ K)) (.eqRefl _))
      (congrMul (congrMul (.eqRefl _) (square_power (two*a+b) (succ K))) (.eqRefl _))
  refine syntactic.eqTrans (fraction_same (pw u (succ K)*w) (J*pw w (succ K)*v) (pw u (succ K)) (J*pw w K*v)
    (hd (succ K)) (hd K) ?_)
  have e := natEq (pw_succ (Γ := Γ) w K)
  apply deriveNat
  ipra_simps
  rw [e]
  ring

theorem tail_le_geometric (a b K : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] rationalLE (fstT (tail a b K)) (fstT (geometricTail a b K)) := by
  let U := pw (numeratorSquare b) (succ K)
  let P := pw (denominatorSquare a b) K
  let V := gap a b
  let J := succ (two*succ K)
  have hP := GaussianFactorBudget.power_positive (denominatorSquare a b) K (square_positive a b hb)
  have hv := gap_positive a b ha
  have hJ := zero_lt_succ (Γ := Γ) (two*succ K)
  have h3 := small_numeral_positive (Γ := Γ) 2
  have cmp : Γ ⊢[PRAAx] le (num 3*V*P*U) (U*(J*P*V)) :=
    le_of_eq_add (d := two*K*U*P*V) (by dsimp [J]; ipra_ring)
  exact rationalLE_congr (congrFst (tail_value a b K ha hb).eqSymm) (.eqRefl _)
    (fraction_order U (J*P*V) U (num 3*V*P)
      (positive_product _ _ (positive_product _ _ hJ hP) hv)
      (positive_product _ _ (positive_product _ _ h3 hv) hP) cmp)

theorem point_order_refl (a : PTm n) : Γ ⊢[PRAAx] rationalLE (fstT a) (fstT a) :=
  le_refl _

theorem point_add_order (a b c d : PTm n)
    (h : Γ ⊢[PRAAx] rationalLE (fstT a) (fstT b)) (k : Γ ⊢[PRAAx] rationalLE (fstT c) (fstT d)) :
    Γ ⊢[PRAAx] rationalLE (fstT (qadd a c)) (fstT (qadd b d)) :=
  rationalLE_congr (RationalGaussianRealPart.real_add a c).eqSymm (RationalGaussianRealPart.real_add b d).eqSymm
    (GaussianRationalSyntheticBounds.add_monotone _ _ _ _ h k)

theorem point_add_upper_same (a b c d E F P : PTm n) (hP : Γ ⊢[PRAAx] le one P)
    (h : Γ ⊢[PRAAx] upper (fstT a) (fstT b) E P) (k : Γ ⊢[PRAAx] upper (fstT c) (fstT d) F P) :
    Γ ⊢[PRAAx] upper (fstT (qadd a c)) (fstT (qadd b d)) (E+F) P := by
  have h' := RationalUpperAddition.add_upper _ _ _ _ _ _ _ _ h k
  exact upper_congr (RationalGaussianRealPart.real_add a c).eqSymm (RationalGaussianRealPart.real_add b d).eqSymm
    (.eqRefl _) (.eqRefl _)
    (RationalValueBounds.upper_mono _ _ _ _ _ _ (positive_product _ _ hP hP) h' (le_of_eq_add (d := zero) (by ipra_ring)))

theorem sharp_partial_order (a b L k : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (hL : Γ ⊢[PRAAx] le (succ (two*succ (succ k))) L) :
    Γ ⊢[PRAAx] rationalLE (fstT (qadd (partialSum a b (succ (succ k))) (tail a b (succ (succ k)))))
      (fstT (sharpUpperValue a b)) := by
  let K := succ (succ k)
  let S := partialSum a b K
  let T := tail a b K
  let G := geometricTail a b K
  let M := upperMargin a b
  let H := geometricMain a b
  have base := sharp_upper a b L k ha hb hL
  have sharp := point_add_order (qadd (qadd S G) M) H (qnegative M) (qnegative M) base (point_order_refl _)
  have cancel := (qsub_congr (GaussianReciprocalHorner.qadd_commutative (Γ := Γ) (qadd S G) M) (.eqRefl M)).eqTrans
    (qadd_sub_cancel M (qadd S G) (qadd_canonical _ _))
  have clean := rationalLE_congr (congrFst cancel) (.eqRefl _) sharp
  have replace := point_add_order S S T G (point_order_refl S) (tail_le_geometric a b K ha hb)
  exact RationalArgmin.transitive replace clean

end LeanProofs.IPRA.Analysis.GaussianStirlingTailComparison

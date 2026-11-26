import IPRADerivations.Analysis.Gamma.CriticalPoints.NegativeIntervals.GaussianGammaNegativeCriticalPositiveWindow
import IPRADerivations.Analysis.Gamma.Digamma.CriticalPoints.GaussianGammaDigammaDyadicMesh
import IPRADerivations.Analysis.Gamma.Digamma.CriticalPoints.GaussianGammaDigammaGridSign

/-!
# Opposite endpoint signs for the shifted digamma on every negative interval

The two literal reciprocal corrections have magnitude at least six
with opposite signs. The original positive digamma contributes at
most one in either direction. A common dyadic observation clock
therefore supplies the strict rational signs used by bounded search.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeCriticalSigns

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaDigammaCriticalSigns (quarter negativeQuarter)
open GaussianGammaDigammaDyadicMesh (clock grid grid_threshold)
open GaussianGammaDigammaGridSign (negative_from_upper nonnegative_from_upper)
open GaussianGammaNegativeCriticalEndpoints
  (mesh rightNumerator leftCap rightFloor nameF nameData mesh_minimum left_guard right_guard
   left_correction_upper right_correction_lower)
open GaussianGammaNegativeCriticalPositiveWindow (positiveOne negativeOne window)
open GaussianGammaEulerRationalLogOrder (add_order)
open GaussianEulerPowerChartTimeOrder (order_trans)
open GaussianNameArithmetic (addF addData)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNamedPositiveExponentialOrder (realOrder real_order_at)
open GaussianNamedRealOrderTransport (transport)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianPositiveRealArithmetic (sign)
open GaussianRationalHorner (qadd qzero scalar_congr)
open GaussianRationalMetric (qnegative qnegative_canonical qsub)
open GaussianRationalSyntheticDivision (qzero_add qsub_congr)
open GaussianStirlingMultiplicativeBoundsLog (constant_order fractions_order)
open RationalArithmetic (represents)
open RationalArgmin (rationalLE rationalLE_congr)
open RationalValueBounds (upper_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (monus num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "DF" => GaussianGammaDigammaNative.nameF
local notation "dd" => GaussianGammaDigammaNative.data
local notation "CF" => constantF
local notation "corr" => GaussianGammaNegativeCriticalCorrection.correction

def leftData (N : PTm n) : PTm n := nameData one (mesh N) N
def rightData (N : PTm n) : PTm n := nameData (rightNumerator N) (mesh N) N

@[simp] theorem subst_leftData {k : ℕ} (σ : Fin n → PTm k) (N : PTm n) :
    Syn.subst σ (leftData N) = leftData (Syn.subst σ N) := by simp [leftData]
@[simp] theorem subst_rightData {k : ℕ} (σ : Fin n → PTm k) (N : PTm n) :
    Syn.subst σ (rightData N) = rightData (Syn.subst σ N) := by simp [rightData]

private theorem negative_order (a b : PTm n)
    (h : Γ ⊢[PRAAx] rationalLE (fstT a) (fstT b)) :
    Γ ⊢[PRAAx] rationalLE (fstT (qnegative b)) (fstT (qnegative a)) :=
  rationalLE_congr (fst_pair _ _).eqSymm (fst_pair _ _).eqSymm (RationalAlgebra.negative_antitone _ _ h)

private theorem sub_zero (a : PTm n) : Γ ⊢[PRAAx] qsub qzero a ≐ qnegative a :=
  qzero_add _ (qnegative_canonical a)

private theorem negate_congr {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] qnegative a ≐ qnegative b :=
  (sub_zero a).eqSymm.eqTrans ((qsub_congr (.eqRefl _) h).eqTrans (sub_zero b))

private theorem constant_sum_as (a b : PTm n) {c : PTm n} (e : Γ ⊢[PRAAx] qadd a b ≐ c) :
    Γ ⊢[PRAAx] crossEquivalent (addF CF CF) CF (addData a b) c :=
  cross_trans _ _ _ _ _ _ (GaussianGammaEulerShift.constant_sum_cross a b)
    (GaussianSignedNameExponentialOrder.constant_equal_cross _ _ e)

private theorem six_minus_one :
    Γ ⊢[PRAAx] qsub (fraction (num 6) one : PTm n) positiveOne ≐ fraction (num 5) one :=
  (GaussianEulerPositivePowerChartImageWeights.fraction_difference one (num 6) one (le_refl _) (by ipra_le 5)).eqTrans
    (GaussianCompactRiemannName.fraction_congr _ _ _ _
      ((congrMonus (show Γ ⊢[PRAAx] (num 6 : PTm n) ≐ num 5+one from by ipra_ring) (.eqRefl _)).eqTrans
        (add_monus _ _)) (.eqRefl _))

theorem left_named_margin (N : PTm n) : Γ ⊢[PRAAx]
    realOrder nameF CF (leftData N) (qnegative (fraction (num 5) one)) := by
  let B := mesh N
  let c := corr one B N
  let S : PTm n := fraction (num 6) one
  have g := left_guard (Γ := Γ) N
  have hb := le_trans g.andE₁ (le_of_lt g.andE₂)
  have base := (window one B hb hb).andE₂
  have cap : Γ ⊢[PRAAx] rationalLE (fstT (qnegative (fraction (two*succ (succ (succ N))) one)))
      (fstT (qnegative S)) :=
    negative_order _ _ (fractions_order (num 6) (one : PTm n) (two*succ (succ (succ N))) one (le_refl _) (le_refl _)
      (by ipra_le 2*𝔞(N)))
  have h := constant_order c (qnegative S) (RationalArgmin.transitive (left_correction_upper N) cap)
  have total := add_order DF CF CF CF (dd (B+one) B) positiveOne c (qnegative S) base h
  have e := (GaussianRationalDistanceOrder.reversed_difference S (positiveOne : PTm n)).eqSymm.eqTrans
    (negate_congr (six_minus_one (Γ := Γ)))
  exact transport nameF nameF (addF CF CF) CF (leftData N) (leftData N) (addData positiveOne (qnegative S))
    (qnegative (fraction (num 5) one))
    (cross_refl _ _ (GaussianGammaNegativeCriticalEndpoints.name_regular one B N g))
    (constant_sum_as positiveOne (qnegative S) e) total

theorem right_named_margin (N : PTm n) : Γ ⊢[PRAAx]
    realOrder CF nameF (fraction (num 5) one) (rightData N) := by
  let B := mesh N
  let A := rightNumerator N
  let c := corr A B N
  let S : PTm n := fraction (num 6) one
  have g := right_guard (Γ := Γ) N
  have hb := le_trans g.andE₁ (le_of_lt g.andE₂)
  have base := (window A B hb (le_of_lt g.andE₂)).andE₁
  have h2 : Γ ⊢[PRAAx] le two B := le_trans (by ipra_le 6) (mesh_minimum N)
  have e := natEq (eq_add_of_le h2)
  have floor : Γ ⊢[PRAAx] rationalLE (fstT S) (fstT (rightFloor N)) :=
    fractions_order (num 6) one (monus B two) one (le_refl _) (le_refl _)
      (by ipra_le sl (mesh_minimum N) with -e)
  have h := constant_order S c (RationalArgmin.transitive floor (right_correction_lower N))
  have total := add_order CF DF CF CF negativeOne (dd (B+A) B) S c base h
  have sum : Γ ⊢[PRAAx] qadd negativeOne S ≐ fraction (num 5) one :=
    (GaussianRationalSyntheticDivision.qadd_congr (sub_zero positiveOne) (.eqRefl _)).eqTrans
      ((GaussianReciprocalHorner.qadd_commutative _ _).eqTrans six_minus_one)
  exact transport CF (addF CF CF) nameF nameF (fraction (num 5) one) (addData negativeOne S) (rightData N)
    (rightData N) (cross_symm _ _ _ _ (constant_sum_as negativeOne S sum))
    (cross_refl _ _ (GaussianGammaNegativeCriticalEndpoints.name_regular A B N g)) total

private theorem quarter_represents :
    Γ ⊢[PRAAx] represents (fstT (quarter : PTm n)) (ZT.ofNat one) (num 4) :=
  GaussianGammaDigammaHarmonicCells.point_fraction_represents one (num 4) (by ipra_le 3)

private theorem negative_quarter_represents :
    Γ ⊢[PRAAx] represents (fstT (negativeQuarter : PTm n)) (-ZT.ofNat one) (num 4) :=
  scalar_congr ((congrFst (sub_zero quarter)).eqTrans (fst_pair _ _)).eqSymm (.eqRefl _) (.eqRefl _)
    (RationalRepresentations.represents_negative _ _ _ quarter_represents)

theorem endpoint_signs (p N : PTm n) : Γ ⊢[PRAAx]
    neg (sign (fstT (ap2 nameF (clock p) (leftData N)))) ⋏
      sign (fstT (ap2 nameF (clock p) (rightData N))) := by
  let P : PTm n := fraction (num 5) one
  let t := clock p
  have h : Γ ⊢[PRAAx] rationalLE (fstT (quarter : PTm n)) (fstT P) :=
    fractions_order one (num 4) (num 5) one (by ipra_le 3) (le_refl _) (by ipra_le 19)
  have l := constant_order (qnegative P) negativeQuarter
    (rationalLE_congr (.eqRefl _) (congrFst (sub_zero quarter)).eqSymm (negative_order _ _ h))
  have r := constant_order quarter P h
  have lq := real_order_at nameF CF (leftData N) negativeQuarter t t
    (order_trans _ _ _ _ _ _ (left_named_margin N) l)
  have rq := real_order_at CF nameF quarter (rightData N) t t
    (order_trans _ _ _ _ _ _ r (right_named_margin N))
  exact .andI
    (negative_from_upper _ _ (grid p) (grid_threshold p) negative_quarter_represents
      (upper_congr (.eqRefl _) (congrFst (constant_at t negativeQuarter)) (.eqRefl _) (.eqRefl _) lq))
    (nonnegative_from_upper _ _ (grid p) (grid_threshold p) quarter_represents
      (upper_congr (congrFst (constant_at t quarter)) (.eqRefl _) (.eqRefl _) (.eqRefl _) rq))

theorem original_shifted_negative_digamma_grid_endpoint_signs_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (neg (sign (fstT (ap2 nameF (clock (var 0)) (leftData (var 1))))) ⋏
        sign (fstT (ap2 nameF (clock (var 0)) (rightData (var 1))))) :=
  closeUniv 2 (endpoint_signs _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeCriticalSigns

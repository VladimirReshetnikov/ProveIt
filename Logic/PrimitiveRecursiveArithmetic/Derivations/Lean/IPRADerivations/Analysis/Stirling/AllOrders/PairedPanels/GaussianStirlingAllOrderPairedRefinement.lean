import IPRADerivations.Analysis.Stirling.AllOrders.PairedPanels.GaussianStirlingAllOrderPairedWeight
import IPRADerivations.Analysis.Optimization.Convexity.RationalConvexClockRescale
import IPRADerivations.Analysis.RationalArithmetic.Powers.RationalReciprocalPowerTail

/-!
# Uniform strict separation of the reflected Stirling weights

The positive gap at the rational centers 1/8 and 3/8 is unchanged
under mesh refinement. Monotonicity keeps that same rational gap
on the two associated boxes of refined mesh points.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPairedRefinement

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.LocalFactor (pw_mul_base)
open GaussianEuclideanDistanceName (fraction fraction_order)
open GaussianRationalHorner (positive_product)
open GaussianStirlingAllOrderPowerGap (low base gap)
open GaussianStirlingAllOrderPairedWeight
  (pairWeight pairGap pair_gap gapFraction gapNumerator gapDenominator gap_denominator_positive gap_numerator_positive)
open RationalArgmin (rationalLE rationalLE_congr transitive)
open RationalArithmetic (add)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ zero)
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private def fourth (t : PTm n) : PTm n := (t*t)*(t*t)
private def cube (t : PTm n) : PTm n := t*t*t

private theorem power_cube (S q : PTm n) : Γ ⊢[PRAAx] pw (cube S) q ≐ cube (pw S q) :=
  (pw_mul_base (S*S) S q).eqTrans (congrMul (pw_mul_base S S q) (.eqRefl _))

private theorem power_fourth (S q : PTm n) : Γ ⊢[PRAAx] pw (fourth S) q ≐ fourth (pw S q) :=
  (pw_mul_base (S*S) (S*S) q).eqTrans (congrMul (pw_mul_base S S q) (pw_mul_base S S q))

private theorem scaled_denominator (q M a d h : PTm n) :
    Γ ⊢[PRAAx] gapDenominator q (M*a) (M*d) (M*h) ≐ gapDenominator q a d h*fourth (pw M (succ q)) := by
  let k := succ q
  let D := (a*(a+d))*((a+h)*(a+h+d))
  have e : Γ ⊢[PRAAx] ((M*a)*(M*a+M*d))*((M*a+M*h)*(M*a+M*h+M*d)) ≐ D*fourth M := by
    dsimp [D,fourth]
    ipra_ring
  exact (congrAp2 powF (.eqRefl k) e).eqTrans
    ((pw_mul_base D (fourth M) k).eqTrans (congrMul (.eqRefl _) (power_fourth M k)))

private theorem scaled_base (a d h M : PTm n) : Γ ⊢[PRAAx]
    base (M*a) (M*a+M*h) (M*d) (M*h) ≐ base a (a+h) d h*cube M := by
  unfold base low cube
  ipra_ring

private theorem scaled_numerator (q M a d h S : PTm n) :
    Γ ⊢[PRAAx] gapNumerator q (S*M) (S*a) (S*d) (S*h) ≐
      gapNumerator q M a d h*fourth (pw S (succ q)) := by
  let b := a+h
  let P := base a b d h
  have pS := natEq (pw_mul_base (Γ := Γ) S M (succ q))
  have pP := natEq ((congrAp2 powF (.eqRefl q) (scaled_base (Γ := Γ) a d h S)).eqTrans
    ((pw_mul_base P (cube S) q).eqTrans (congrMul (.eqRefl _) (power_cube S q))))
  have u := natEq (pw_succ (Γ := Γ) S q)
  unfold gapNumerator gap fourth
  apply deriveNat
  ipra_simps
  rw [pS,pP,u]
  dsimp [cube] at *
  ipra_simps
  ring

theorem gap_refinement (q M a d h S : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hS : Γ ⊢[PRAAx] le one S) :
    Γ ⊢[PRAAx] gapFraction q (S*M) (S*a) (S*d) (S*h) ≐ gapFraction q M a d h := by
  let r := pw S (succ q)
  have hp := GaussianFactorBudget.power_positive (Γ := Γ) S (succ q) hS
  have hr : Γ ⊢[PRAAx] le one (fourth r) :=
    positive_product _ _ (positive_product _ _ hp hp) (positive_product _ _ hp hp)
  exact (RationalNonnegativePowers.fraction_congr (scaled_numerator q M a d h S) (scaled_denominator q S a d h)).eqTrans
    (RationalConvexClockRescale.fraction_rescale (gapNumerator q M a d h) (gapDenominator q a d h) (fourth r)
      (gap_denominator_positive q a d h ha) hr)

theorem pair_monotone (q M A u v : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (huv : Γ ⊢[PRAAx] le u v) (hM : Γ ⊢[PRAAx] le (two*v) M) :
    Γ ⊢[PRAAx] rationalLE (pairWeight q M A v) (pairWeight q M A u) := by
  let D := gapDenominator q (A+u) (monus v u) (monus M (u+v))
  let G := gapNumerator q M (A+u) (monus v u) (monus M (u+v))
  let F := pairWeight q M A v
  have hp := gap_denominator_positive q (A+u) (monus v u) (monus M (u+v)) (le_trans hA (le_add_right A u))
  have hn := fraction_order zero one G D (le_refl one) hp (by
    exact le_congr (mul_zero _).eqSymm (by ipra_ring) (zero_le G))
  have order := GaussianRationalSyntheticBounds.add_monotone F F (fraction zero one) (pairGap q M A u v) (le_refl _) hn
  have recode : Γ ⊢[PRAAx] add F (fraction zero one) ≐ F :=
    RationalReciprocalPowerTail.add_zero_right F (RationalArithmetic.add_guard _ _)
  exact transitive (rationalLE_congr recode (.eqRefl _) order) (pair_gap q M A u v hA huv hM)

def mesh (B S : PTm n) : PTm n := S*(num 8*B)
def start (A S : PTm n) : PTm n := S*(num 8*A)
def lowerCenter (B S : PTm n) : PTm n := S*B
def upperCenter (B S : PTm n) : PTm n := S*(num 3*B)
def centerGap (q A B : PTm n) : PTm n := gapFraction q (num 8*B) (num 8*A+B) (two*B) (num 4*B)

private theorem center_refinement (q A B S : PTm n) (ha : Γ ⊢[PRAAx] le one A) (hS : Γ ⊢[PRAAx] le one S) :
    Γ ⊢[PRAAx] pairGap q (mesh B S) (start A S) (lowerCenter B S) (upperCenter B S) ≐ centerGap q A B := by
  let a := num 8*A+B
  have ha₀ : Γ ⊢[PRAAx] le one (num 8*A) := positive_product _ _ (by ipra_le 7) ha
  have ha' : Γ ⊢[PRAAx] le one a := le_trans ha₀ (le_add_right _ _)
  have eA : Γ ⊢[PRAAx] start A S+lowerCenter B S ≐ S*a := by unfold start lowerCenter a; ipra_ring
  have eD : Γ ⊢[PRAAx] monus (upperCenter B S) (lowerCenter B S) ≐ S*(two*B) := by
    have e : Γ ⊢[PRAAx] upperCenter B S ≐ S*(two*B)+lowerCenter B S := by unfold upperCenter lowerCenter; ipra_ring
    exact (congrMonus e (.eqRefl _)).eqTrans (add_monus _ _)
  have eH : Γ ⊢[PRAAx] monus (mesh B S) (lowerCenter B S+upperCenter B S) ≐ S*(num 4*B) := by
    have e : Γ ⊢[PRAAx] mesh B S ≐ S*(num 4*B)+(lowerCenter B S+upperCenter B S) := by
      unfold mesh lowerCenter upperCenter
      ipra_ring
    exact (congrMonus e (.eqRefl _)).eqTrans (add_monus _ _)
  have reform : Γ ⊢[PRAAx] pairGap q (mesh B S) (start A S) (lowerCenter B S) (upperCenter B S) ≐
      gapFraction q (mesh B S) (S*a) (S*(two*B)) (S*(num 4*B)) := by
    simpa only [pairGap,GaussianStirlingAllOrderPairedWeight.subst_gapNumerator,
      GaussianStirlingAllOrderPairedWeight.subst_gapDenominator,gapFraction,fraction,
      RationalIntegerNormalization.subst_normalize,ZT.subst_ofNat,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
      Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] using
      (Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (gapFraction (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
        (σ := ![q,mesh B S,start A S+lowerCenter B S,monus (upperCenter B S) (lowerCenter B S),
          monus (mesh B S) (lowerCenter B S+upperCenter B S)])
        (σ' := ![q,mesh B S,S*a,S*(two*B),S*(num 4*B)]) (fun i => by fin_cases i <;> first | exact .eqRefl _ | exact eA | exact eD | exact eH))
  exact reform.eqTrans (gap_refinement q (num 8*B) a (two*B) (num 4*B) S ha' hS)

theorem separated_grid_gap (q A B S u v : PTm n) (ha : Γ ⊢[PRAAx] le one A) (hS : Γ ⊢[PRAAx] le one S)
    (hu : Γ ⊢[PRAAx] le u (lowerCenter B S)) (hv : Γ ⊢[PRAAx] le (upperCenter B S) v)
    (hvM : Γ ⊢[PRAAx] le (two*v) (mesh B S)) :
    Γ ⊢[PRAAx] rationalLE (add (pairWeight q (mesh B S) (start A S) v) (centerGap q A B))
      (pairWeight q (mesh B S) (start A S) u) := by
  let M := mesh B S
  let Q := start A S
  let l := lowerCenter B S
  let r := upperCenter B S
  have hQ : Γ ⊢[PRAAx] le one Q := positive_product _ _ hS (positive_product _ _ (by ipra_le 7) ha)
  have hlr : Γ ⊢[PRAAx] le l r := by unfold l r lowerCenter upperCenter; ipra_le 2*Groth.ι (IPRA.Q.mk Γ S)*Groth.ι (IPRA.Q.mk Γ B)
  have hrM : Γ ⊢[PRAAx] le (two*r) M := le_trans (le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right two hv)) hvM
  have hlM : Γ ⊢[PRAAx] le (two*l) M := le_trans (le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right two hlr)) hrM
  have lo := pair_monotone q M Q u l hQ hu hlM
  have hi := pair_monotone q M Q r v hQ hv hvM
  have exactCenter := pair_gap q M Q l r hQ hlr hrM
  have middle := rationalLE_congr (RationalAlgebra.add_congr (.eqRefl _) (center_refinement q A B S ha hS)) (.eqRefl _) exactCenter
  have hgap : Γ ⊢[PRAAx] rationalLE (centerGap q A B) (centerGap q A B) := le_refl _
  have sealed := GaussianRationalSyntheticBounds.add_monotone _ _ _ _ hi hgap
  exact transitive sealed (transitive middle lo)

theorem center_gap_positive (q A B : PTm n) (ha : Γ ⊢[PRAAx] le one A) (hb : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] rationalLE (fraction one (gapDenominator q (num 8*A+B) (two*B) (num 4*B))) (centerGap q A B) := by
  let a := num 8*A+B
  let D := gapDenominator q a (two*B) (num 4*B)
  have hp : Γ ⊢[PRAAx] le one a := le_trans (positive_product _ _ (by ipra_le 7) ha) (le_add_right _ _)
  have hD := gap_denominator_positive q a (two*B) (num 4*B) hp
  have numPositive := gap_numerator_positive q (num 8*B) a (two*B) (num 4*B)
    (positive_product _ _ (by ipra_le 7) hb) hp (positive_product _ _ (le_succ_self one) hb)
    (positive_product _ _ (by ipra_le 3) hb)
  exact fraction_order _ _ _ _ hD hD
    (le_congr (by ipra_ring) (.eqRefl _) (mul_le_mul_right D numPositive))

theorem actual_Stirling_separated_reflected_weight_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((le one (var 1) ⋏ (le one (var 3) ⋏ (le (var 4) (lowerCenter (var 2) (var 3)) ⋏
      (le (upperCenter (var 2) (var 3)) (var 5) ⋏ le (two*var 5) (mesh (var 2) (var 3)))))) ⟶
      rationalLE (add (pairWeight (var 0) (mesh (var 2) (var 3)) (start (var 1) (var 3)) (var 5))
        (centerGap (var 0) (var 1) (var 2))) (pairWeight (var 0) (mesh (var 2) (var 3)) (start (var 1) (var 3)) (var 4))) :=
  closeUniv 6 (.impI (separated_grid_gap _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPairedRefinement

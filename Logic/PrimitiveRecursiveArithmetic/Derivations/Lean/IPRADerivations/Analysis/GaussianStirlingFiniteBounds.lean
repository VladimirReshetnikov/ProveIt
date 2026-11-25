import IPRADerivations.Analysis.GaussianStirlingFiniteSeries
import IPRADerivations.Analysis.GaussianGammaHalfSqrtBrackets

/-!
# Sharp rational comparison of the finite Stirling difference series

The actual finite sum is at least its first term. The sum together
with the geometric tail envelope and the positive upper correction
is at most the telescoping main term, at arbitrary internal cutoff.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingFiniteBounds

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerPositivePowerChartCorrectedImage (fraction_sum)
open GaussianGammaHalfSqrtBrackets (fraction_first_represents)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qadd positive_product)
open GaussianRationalSyntheticDivision (qadd_congr)
open GaussianStirlingFiniteSeries (folded denominator denominator_positive partial_equals_fold)
open GaussianStirlingOddSeries (partialSum)
open GaussianStirlingRationalTelescopers
  (fraction_same numeratorSquare denominatorSquare gap square_split square_positive gap_positive
   small_numeral_positive firstTerm geometricMain upperMargin)
open StirlingRationalSeries (fold upper_at_base upperWithBase)
open Products (fact)
open RationalArgmin (rationalLE)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

theorem fraction_order (A B C D : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] le (D*A) (C*B)) : Γ ⊢[PRAAx] rationalLE (fstT (fraction A B)) (fstT (fraction C D)) :=
  GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _ hB hD
    (fraction_first_represents _ _ hB) (fraction_first_represents _ _ hD) h

private theorem add_same_denominator (a b D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] qadd (fraction a D) (fraction b D) ≐ fraction (a+b) D :=
  (fraction_sum a D b D hD hD).eqTrans
    (fraction_same _ _ _ _ (positive_product _ _ hD hD) hD (by ipra_ring))

theorem first_term_bound (a b L k : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hL : Γ ⊢[PRAAx] le (succ (two*succ k)) L) :
    Γ ⊢[PRAAx] rationalLE (fstT (firstTerm a b)) (fstT (partialSum a b (succ k))) := by
  let w := denominatorSquare a b
  let u := numeratorSquare b
  let T := fold w u L (succ k)
  let D := denominator a b L (succ k)
  have hw := square_positive a b hb
  have hd := denominator_positive a b L (succ k) hb
  have h3 := le_trans (le_of_eq_add (d := two*k) (by ipra_ring :
    Γ ⊢[PRAAx] succ (two*succ k) ≐ num 3+two*k)) hL
  have clear := StirlingRationalSeries.lower w u L k h3
  change Γ ⊢[PRAAx] le (u*pw w k*fact L) (num 3*T) at clear
  have exactOrder : Γ ⊢[PRAAx] le (D*u) (T*(num 3*w)) := by
    have step := natEq (pw_succ (Γ := Γ) w k)
    change Γ ⊢[PRAAx] le ((pw w (succ k)*fact L)*u) (T*(num 3*w))
    ipra_le 𝔞 w*sl clear using rw [step]; ring
  exact RationalArgmin.rationalLE_congr (.eqRefl _)
    (congrFst (partial_equals_fold a b L (succ k) hb hL).eqSymm)
    (fraction_order u (num 3*w) T D (positive_product _ _ (small_numeral_positive 2) hw) hd exactOrder)

def geometricTail (a b K : PTm n) : PTm n :=
  fraction (pw (numeratorSquare b) (succ K)) (num 3*gap a b*pw (denominatorSquare a b) K)

@[simp] theorem subst_geometricTail {l : ℕ} (σ : Fin n → PTm l) (a b K : PTm n) :
    Syn.subst σ (geometricTail a b K) = geometricTail (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ K) := by
  simp [geometricTail,num]

theorem sharp_upper (a b L k : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (hL : Γ ⊢[PRAAx] le (succ (two*succ (succ k))) L) : Γ ⊢[PRAAx]
    rationalLE (fstT (qadd (qadd (partialSum a b (succ (succ k))) (geometricTail a b (succ (succ k))))
      (upperMargin a b))) (fstT (geometricMain a b)) := by
  let K := succ (succ k)
  let w := denominatorSquare a b
  let u := numeratorSquare b
  let v := gap a b
  let T := fold w u L K
  let P := pw w K
  let F := fact L
  let D := num 15*(w*w)*v*P*F
  let A := num 15*(w*w)*v*T
  let B := num 5*(w*w)*pw u (succ K)*F
  let C := two*v*(u*u)*P*F
  let E := num 5*u*pw w (succ (succ K))*F
  have hw := square_positive a b hb
  have hv := gap_positive a b ha
  have hP := GaussianFactorBudget.power_positive w K hw
  have hF := GammaEulerMesh.factorial_positive (Γ := Γ) L
  have hw2 := positive_product _ _ hw hw
  have h15 := small_numeral_positive (Γ := Γ) 14
  have h3 := small_numeral_positive (Γ := Γ) 2
  have hD : Γ ⊢[PRAAx] le one D :=
    positive_product _ _ (positive_product _ _
      (positive_product _ _ (positive_product _ _ h15 hw2) hv) hP) hF
  have partialValue : Γ ⊢[PRAAx] partialSum a b K ≐ fraction A D :=
    (partial_equals_fold a b L K hb hL).eqTrans
      (fraction_same T (P*F) A D (denominator_positive a b L K hb) hD
        (by dsimp [A,D]; ipra_ring))
  have tailValue : Γ ⊢[PRAAx] geometricTail a b K ≐ fraction B D :=
    fraction_same (pw u (succ K)) (num 3*v*P) B D
      (positive_product _ _ (positive_product _ _ h3 hv) hP) hD (by dsimp [D,B]; ipra_ring)
  have marginDen : Γ ⊢[PRAAx] le one (num 15*w*w) :=
    positive_product _ _ (positive_product _ _ h15 hw) hw
  have marginValue : Γ ⊢[PRAAx] upperMargin a b ≐ fraction C D :=
    fraction_same (two*u*u) (num 15*w*w) C D marginDen hD (by dsimp [D,C]; ipra_ring)
  have mainValue : Γ ⊢[PRAAx] geometricMain a b ≐ fraction E D :=
    fraction_same u (num 3*v) E D (positive_product _ _ h3 hv) hD (by
      have p1 := natEq (pw_succ (Γ := Γ) w K)
      have p2 := natEq (pw_succ (Γ := Γ) w (succ K))
      dsimp [D,E,P]
      apply deriveNat
      ipra_simps
      rw [p2,p1]
      ring)
  have exactSum := (qadd_congr (qadd_congr partialValue tailValue) marginValue).eqTrans
    ((qadd_congr (add_same_denominator A B D hD) (.eqRefl _)).eqTrans (add_same_denominator (A+B) C D hD))
  have comparison : Γ ⊢[PRAAx] le (A+B+C) E := upper_at_base w v u L k (square_split a b) hL
  exact RationalArgmin.rationalLE_congr (congrFst exactSum.eqSymm) (congrFst mainValue.eqSymm)
    (fraction_order (A+B+C) D E D hD hD
      (le_congr (mul_comm _ _) (.eqRefl _) (mul_le_mul_right D comparison)))

theorem actual_finite_rational_Stirling_sharp_upper_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (le one (var 0) ⟶ le one (var 1) ⟶ le (succ (two*succ (succ (var 3)))) (var 2) ⟶
        rationalLE (fstT (qadd (qadd (partialSum (var 0) (var 1) (succ (succ (var 3))))
          (geometricTail (var 0) (var 1) (succ (succ (var 3))))) (upperMargin (var 0) (var 1))))
          (fstT (geometricMain (var 0) (var 1)))) :=
  closeUniv 4 (.impI (.impI (.impI (sharp_upper _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianStirlingFiniteBounds

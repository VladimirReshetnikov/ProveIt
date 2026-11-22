import IPRADerivations.Analysis.GaussianDescentClockArithmetic
import IPRADerivations.Analysis.RationalCubeMidpoint
import IPRADerivations.Foundations.FiniteObservations.MetricKernel
import IPRADerivations.Foundations.DyadicGain
import IPRADerivations.Core.OrderCertificates

/-!
# The two secants and dyadic clock of the local convexity modulus

Write the endpoints and arguments on a positive common denominator `D`.
The source samples are taken at `P/(2D)` and `(Q+D)/D`. The secant
weights are written on scale `2D`, including the margin
`min(P, 2D)/(2D)`. This also yields the exact source clock `k+ceil(M/δ)`.

The convexity inequalities can carry a common finite-precision error.
The resulting bounds retain that error after removing the secant weights.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalConvexSecantWeights

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ConciseIPRA.PTm (zero succ app)
open LeanProofs.IPRA.PTm (monus)
open RationalCubeMidpoint (fraction)
open LeanProofs.IPRA.Foundations.FiniteObservations.MetricKernel (meet meet_left meet_right meet_le_left meet_le_right)
open GaussianDescentClockArithmetic (ceiling ceiling_lower)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

def leftPoint (D P : PTm n) : PTm n := fraction P (two*D)
def rightPoint (D Q : PTm n) : PTm n := fraction (Q+D) D
def margin (D P : PTm n) : PTm n := meet P (two*D)
def displacement (X Y : PTm n) : PTm n := two*monus Y X
def rightRemainder (D Q Y : PTm n) : PTm n := two*monus (Q+D) Y
def leftRemainder (P X : PTm n) : PTm n := monus (two*X) P
def rightWidth (D Q X : PTm n) : PTm n := two*monus (Q+D) X
def leftWidth (P Y : PTm n) : PTm n := monus (two*Y) P
def budget (D P M : PTm n) : PTm n := ceiling (two*D*M) (margin D P)
def modulus (D P M k : PTm n) : PTm n := k+budget D P M

theorem margin_left (D P : PTm n) : Γ ⊢[PRAAx] le (margin D P) P := meet_le_left _ _
theorem margin_right (D P : PTm n) : Γ ⊢[PRAAx] le (margin D P) (two*D) := meet_le_right _ _

theorem margin_positive (D P : PTm n) (hD : Γ ⊢[PRAAx] le one D) (hP : Γ ⊢[PRAAx] le one P) :
    Γ ⊢[PRAAx] le one (margin D P) := by
  have h : Γ ⊢[PRAAx] le one (two*D) := by ipra_le 2 * sl hD + 1
  exact .orE (le_total P (two*D)) (le_congr (.eqRefl _) (meet_left Prf.hyp0).eqSymm hP.wk)
    (le_congr (.eqRefl _) (meet_right Prf.hyp0).eqSymm h.wk)

theorem right_width (D Q X Y : PTm n) (hXY : Γ ⊢[PRAAx] le X Y) (hYQ : Γ ⊢[PRAAx] le Y Q) :
    Γ ⊢[PRAAx] rightWidth D Q X ≐ displacement X Y+rightRemainder D Q Y := by
  have hY : Γ ⊢[PRAAx] le Y (Q+D) := by ipra_le sl hYQ + 𝔟 D
  have e₁ := natEq (eq_add_of_le (le_trans hXY hY))
  have e₂ := natEq (eq_add_of_le hXY)
  have e₃ := natEq (eq_add_of_le hY)
  unfold rightWidth displacement rightRemainder
  apply deriveNat
  ipra_simps
  linear_combination -2*e₁ + 2*e₂ + 2*e₃

theorem left_width (P X Y : PTm n) (hPX : Γ ⊢[PRAAx] le P X) (hXY : Γ ⊢[PRAAx] le X Y) :
    Γ ⊢[PRAAx] leftWidth P Y ≐ displacement X Y+leftRemainder P X := by
  have hP : Γ ⊢[PRAAx] le P (two*X) := by ipra_le sl hPX + 𝔟 X
  have hY : Γ ⊢[PRAAx] le P (two*Y) := by ipra_le sl hPX + sl hXY + 𝔟 Y
  have e₁ := natEq (eq_add_of_le hY)
  have e₂ := natEq (eq_add_of_le hXY)
  have e₃ := natEq (eq_add_of_le hP)
  unfold leftWidth displacement leftRemainder
  apply deriveNat
  ipra_simps
  linear_combination -e₁ + 2*e₂ + e₃

theorem right_margin (D P Q X : PTm n) (hXQ : Γ ⊢[PRAAx] le X Q) :
    Γ ⊢[PRAAx] le (margin D P) (rightWidth D Q X) := by
  have h : Γ ⊢[PRAAx] le X (Q+D) := by ipra_le sl hXQ + 𝔟 D
  have e := natEq (eq_add_of_le h)
  unfold rightWidth
  ipra_le sl (margin_right D P) + 2*sl hXQ using linear_combination -2*e

theorem left_margin (D P Y : PTm n) (hPY : Γ ⊢[PRAAx] le P Y) :
    Γ ⊢[PRAAx] le (margin D P) (leftWidth P Y) := by
  have h : Γ ⊢[PRAAx] le P (two*Y) := by ipra_le sl hPY + 𝔟 Y
  have e := natEq (eq_add_of_le h)
  unfold leftWidth
  ipra_le sl (margin_left D P) + 2*sl hPY using linear_combination -e

/-- The original right secant expresses `Y/D` using `X/D` and `(Q+D)/D`. -/
theorem right_barycenter (D Q X Y : PTm n) (hXY : Γ ⊢[PRAAx] le X Y) (hYQ : Γ ⊢[PRAAx] le Y Q) :
    Γ ⊢[PRAAx] rightWidth D Q X*Y ≐ rightRemainder D Q Y*X+displacement X Y*(Q+D) := by
  have hY : Γ ⊢[PRAAx] le Y (Q+D) := by ipra_le sl hYQ + 𝔟 D
  have e₁ := natEq (eq_add_of_le (le_trans hXY hY))
  have e₂ := natEq (eq_add_of_le hXY)
  have e₃ := natEq (eq_add_of_le hY)
  unfold rightWidth rightRemainder displacement
  apply deriveNat
  ipra_simps
  linear_combination -2*𝔟 Y*e₁ + 2*(𝔟 Q+𝔟 D)*e₂ + 2*𝔟 X*e₃

/-- The original left secant expresses `X/D` using `P/(2D)` and `Y/D`. -/
theorem left_barycenter (P X Y : PTm n) (hPX : Γ ⊢[PRAAx] le P X) (hXY : Γ ⊢[PRAAx] le X Y) :
    Γ ⊢[PRAAx] leftWidth P Y*(two*X) ≐ leftRemainder P X*(two*Y)+displacement X Y*P := by
  have hP : Γ ⊢[PRAAx] le P (two*X) := by ipra_le sl hPX + 𝔟 X
  have hY : Γ ⊢[PRAAx] le P (two*Y) := by ipra_le sl hPX + sl hXY + 𝔟 Y
  have e₁ := natEq (eq_add_of_le hY)
  have e₂ := natEq (eq_add_of_le hXY)
  have e₃ := natEq (eq_add_of_le hP)
  unfold leftWidth leftRemainder displacement
  apply deriveNat
  ipra_simps
  linear_combination -2*𝔟 X*e₁ + 2*𝔟 P*e₂ + 2*𝔟 Y*e₃

/-- The finite comparison allows a full secant-width times the sample error. -/
theorem secant_with_error (w t u δ U V B M E : PTm n) (hW : Γ ⊢[PRAAx] w ≐ t+u)
    (hConv : Γ ⊢[PRAAx] le (w*V) (u*U+t*B+w*E)) (hB : Γ ⊢[PRAAx] le B M)
    (hδ : Γ ⊢[PRAAx] le δ w) : Γ ⊢[PRAAx] le (δ*V) (δ*U+M*t+δ*E) := by
  refine .orE (le_total V (U+E)) ?_ ?_
  · ipra_le 𝔟 δ*sl Prf.hyp0 + 𝔟 M*𝔟 t
  · have e := natEq (hW.wk (ψ := le (U+E) V))
    have hc := hConv.wk (ψ := le (U+E) V)
    have hb := hB.wk (ψ := le (U+E) V)
    have hδ' := hδ.wk (ψ := le (U+E) V)
    have h : (le (U+E) V :: Γ) ⊢[PRAAx] le (U+E) V := Prf.hyp0
    ipra_le 𝔟 t*sl hb + sl hc + sl hδ'*sl h + 𝔟 t*𝔟 U using linear_combination 𝔟 U*e

theorem source_budget (D P M : PTm n) (hD : Γ ⊢[PRAAx] le one D) (hP : Γ ⊢[PRAAx] le one P) :
    Γ ⊢[PRAAx] le (two*D*M) (margin D P*budget D P M) :=
  ceiling_lower _ _ (margin_positive D P hD hP)

theorem budget_power (D P M : PTm n) : Γ ⊢[PRAAx] le (budget D P M) (pw two (budget D P M)) :=
  le_trans (le_succ_self _) (Foundations.DyadicGain.amplitude_reserve _)

/-- A source modulus input proves the desired precision with no extra clock factor. -/
theorem dyadic_secant (D P M k T : PTm n) (hD : Γ ⊢[PRAAx] le one D) (hP : Γ ⊢[PRAAx] le one P)
    (ht : Γ ⊢[PRAAx] le (T*pw two (modulus D P M k)) (two*D)) :
    Γ ⊢[PRAAx] le (M*T*pw two k) (margin D P) := by
  have ep := natEq (show Γ ⊢[PRAAx] pw two (modulus D P M k) ≐ pw two k*pw two (budget D P M) from
    pw_add two k (budget D P M))
  have hm := source_budget D P M hD hP
  have hh := budget_power (Γ := Γ) D P M
  have h : Γ ⊢[PRAAx] le ((two*D)*(M*T*pw two k)) ((two*D)*margin D P) := by
    ipra_le 𝔟 (T*pw two k)*sl hm + 𝔟 (margin D P*T*pw two k)*sl hh +
      𝔟 (margin D P)*sl ht using linear_combination 𝔟 (margin D P)*𝔟 T*ep
  exact RationalValueBounds.positive_cancel (GaussianDescentClockArithmetic.positive_product two D
    (le_succ_self one) hD) h

/-- The two finite sample comparisons use the exact horizontal geometry. -/
theorem both_secants (D P Q X Y VA VX VY VB M E : PTm n)
    (hPX : Γ ⊢[PRAAx] le P X) (hXY : Γ ⊢[PRAAx] le X Y) (hYQ : Γ ⊢[PRAAx] le Y Q)
    (ha : Γ ⊢[PRAAx] le VA M) (hb : Γ ⊢[PRAAx] le VB M)
    (hl : Γ ⊢[PRAAx] le (leftWidth P Y*VX)
      (leftRemainder P X*VY+displacement X Y*VA+leftWidth P Y*E))
    (hr : Γ ⊢[PRAAx] le (rightWidth D Q X*VY)
      (rightRemainder D Q Y*VX+displacement X Y*VB+rightWidth D Q X*E)) :
    Γ ⊢[PRAAx] le (margin D P*VX) (margin D P*VY+M*displacement X Y+margin D P*E) ⋏
      le (margin D P*VY) (margin D P*VX+M*displacement X Y+margin D P*E) :=
  .andI (secant_with_error _ _ _ _ _ _ _ _ _ (left_width P X Y hPX hXY) hl ha (left_margin D P Y (le_trans hPX hXY)))
    (secant_with_error _ _ _ _ _ _ _ _ _ (right_width D Q X Y hXY hYQ) hr hb (right_margin D P Q X (le_trans hXY hYQ)))

/-- The dyadic budget controls an actual secant difference with a separately tracked sample error. -/
theorem sample_clock (D P M k T J E U V : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hP : Γ ⊢[PRAAx] le one P) (ht : Γ ⊢[PRAAx] le (T*pw two (modulus D P M k)) (two*D))
    (hv : Γ ⊢[PRAAx] le (margin D P*V) (margin D P*U+M*J*T+margin D P*E)) :
    Γ ⊢[PRAAx] le (V*pw two k) (U*pw two k+J+E*pw two k) := by
  have h := dyadic_secant D P M k T hD hP ht
  have hs : Γ ⊢[PRAAx] le (margin D P*(V*pw two k)) (margin D P*(U*pw two k+J+E*pw two k)) := by
    ipra_le 𝔟(pw two k)*sl hv + 𝔟 J*sl h
  exact RationalValueBounds.positive_cancel (margin_positive D P hD hP) hs

/-- The output stores the two endpoint queries, the margin, and the source clock. -/
def output (D P Q M k : PTm n) : PTm n := pairT (leftPoint D P)
  (pairT (rightPoint D Q) (pairT (fraction (margin D P) (two*D)) (pairT (budget D P M) (modulus D P M k))))
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (D P Q M k : PTm n) : PTm n := app outputF ![D,P,Q,M,k]
theorem program_at (D P Q M k : PTm n) : Γ ⊢[PRAAx] run D P Q M k ≐ output D P Q M k := by
  simpa [run,outputF,output,leftPoint,rightPoint,margin,budget,modulus,meet] using
    toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![D,P,Q,M,k]
theorem returned_endpoints (D P Q M k : PTm n) : Γ ⊢[PRAAx]
    (fstT (run D P Q M k) ≐ leftPoint D P) ⋏ (fstT (sndT (run D P Q M k)) ≐ rightPoint D Q) :=
  .andI ((congrFst (program_at D P Q M k)).eqTrans (fst_pair _ _))
    (((congrFst (congrSnd (program_at D P Q M k))).eqTrans (congrFst (snd_pair _ _))).eqTrans (fst_pair _ _))

theorem actual_convex_left_secant_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 0) (var 1) ⟶ le (var 1) (var 2) ⟶
      leftWidth (var 0) (var 2)*(two*var 1) ≐
        leftRemainder (var 0) (var 1)*(two*var 2)+displacement (var 1) (var 2)*var 0) :=
  closeUniv 3 (.impI (.impI (left_barycenter _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_convex_right_secant_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (var 2) (var 3) ⟶ le (var 3) (var 1) ⟶
      rightWidth (var 0) (var 1) (var 2)*var 3 ≐
        rightRemainder (var 0) (var 1) (var 3)*var 2+displacement (var 2) (var 3)*(var 1+var 0)) :=
  closeUniv 4 (.impI (.impI (right_barycenter _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_convex_dyadic_clock_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 0) ⟶ le one (var 1) ⟶ le (var 4*pw two (modulus (var 0) (var 1) (var 2) (var 3))) (two*var 0) ⟶
      le (var 2*var 4*pw two (var 3)) (margin (var 0) (var 1))) :=
  closeUniv 5 (.impI (.impI (.impI (dyadic_secant _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))
theorem actual_convex_secant_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (program_at _ _ _ _ _)

end LeanProofs.IPRA.Analysis.RationalConvexSecantWeights

import IPRADerivations.Analysis.Euler.PositiveAxis.LowerBounds.GaussianEulerLowerTailPartition
import IPRADerivations.Analysis.Euler.PositiveAxis.LowerBounds.GaussianEulerLowerBlockWeight

/-!
# Actual finite lower-tail radius in the original cutoff budget

The actual grouped radius is converted by cleared native comparison.
The leading term uses the exact original height refinement; finite mesh
and evaluation errors use their genuine lower precision bounds. This is
an arbitrary actual-point conversion, with no named lower-tail conclusion
or quadrature/output estimate assumed beyond the stated finite radius.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLowerTailFiniteBudget

open_ipra
open GaussianGammaIntegralCutoffs (height)
open GaussianEulerLowerTailRootGrid (rootRatio rootDenominator)
open GaussianEulerLowerTailPartition (rootStep)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def scale (p q k : PTm n) : PTm n := succ k*rootStep p q
def oldNumerator (N D S L P : PTm n) : PTm n := N*S*(D*P+L*S*P+num 3*D)
def oldDenominator (D P : PTm n) : PTm n := D*D*P
def residual (S L : PTm n) : PTm n := L*S*S+num 3*S
def nativeNumerator (K H S L V : PTm n) : PTm n := K*V+residual S L*H
def nativeDenominator (H V : PTm n) : PTm n := H*V
def numerator (t p q k R L : PTm n) : PTm n := nativeNumerator (succ k) (unit (height p (succ k) R)) (scale p q k) L (unit t)
def denominator (t p k R : PTm n) : PTm n := unit (height p (succ k) R)*unit t

ipra_subst scale
ipra_subst oldNumerator
ipra_subst oldDenominator
ipra_subst residual
ipra_subst nativeNumerator
ipra_subst nativeDenominator
ipra_subst numerator [height, GaussianGammaIntegralCutoffs.tailCoefficient]
ipra_subst denominator [height, GaussianGammaIntegralCutoffs.tailCoefficient]

/-- Each of the three original radius terms is compared separately;
no division or raw rational cancellation is used. -/
theorem cleared_radius (N D S L P K H V : PTm n)
    (hLeading : Γ ⊢[PRAAx] le (N*S*H) (K*D))
    (hMesh : Γ ⊢[PRAAx] le (N*V) (D*D))
    (hObservation : Γ ⊢[PRAAx] le (N*V) (D*P)) : Γ ⊢[PRAAx]
    le (oldNumerator N D S L P*nativeDenominator H V) (nativeNumerator K H S L V*oldDenominator D P) := by
  have first := mul_le_mul_right (D*P*V) hLeading
  have second := mul_le_mul_right (L*S*S*P*H) hMesh
  have third := mul_le_mul_right (num 3*S*D*H) hObservation
  exact le_congr (by unfold oldNumerator nativeDenominator; ipra_ring)
    (by unfold nativeNumerator residual oldDenominator; ipra_ring) (add_le_add₂ (add_le_add₂ first second) third)

theorem point_radius_conversion (x N D S L P K H V : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hP : Γ ⊢[PRAAx] le one P)
    (hH : Γ ⊢[PRAAx] le one H) (hV : Γ ⊢[PRAAx] le one V)
    (hLeading : Γ ⊢[PRAAx] le (N*S*H) (K*D))
    (hMesh : Γ ⊢[PRAAx] le (N*V) (D*D))
    (hObservation : Γ ⊢[PRAAx] le (N*V) (D*P))
    (hx : Γ ⊢[PRAAx] bounded x (oldNumerator N D S L P) (oldDenominator D P)) : Γ ⊢[PRAAx]
    bounded x (nativeNumerator K H S L V) (nativeDenominator H V) :=
  bounded_radius_mono _ _ _ _ _ (positive_product _ _ (positive_product _ _ hD hD) hP)
    (positive_product _ _ hH hV) (cleared_radius N D S L P K H V hLeading hMesh hObservation) hx

theorem exact_height_factor (p q k R : PTm n) (h : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx]
    unit (height q (succ k) R) ≐ unit (height p (succ k) R)*rootRatio p q :=
  (congrAp2 powF (GaussianGammaCompactCutoffGeometry.height_refinement p q (succ k) R h) (.eqRefl two)).eqTrans (pw_add two _ _)

theorem leading_height_budget (p q k R : PTm n) (h : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx]
    le (scale p q k*unit (height p (succ k) R)) (succ k*unit (height q (succ k) R)) := by
  have small := mul_le_mul_right (succ k*unit (height p (succ k) R))
    (GaussianMonicResidualRadius.monus_le_left (Γ := Γ) (rootRatio p q) one)
  exact le_congr (by unfold scale rootStep; ipra_ring)
    ((by ipra_ring : Γ ⊢[PRAAx] rootRatio p q*(succ k*unit (height p (succ k) R)) ≐ succ k*(unit (height p (succ k) R)*rootRatio p q)).eqTrans
      (congrMul (.eqRefl _) (exact_height_factor p q k R h).eqSymm)) small

theorem root_denominator_ge (N q k R : PTm n) : Γ ⊢[PRAAx] le N (rootDenominator N q (succ k) R) :=
  le_congr (by ipra_ring) (.eqRefl _) (mul_le_mul_right N (unit_positive (height q (succ k) R)))

/-- Exact native conversion for the actual root denominator and step.
The old radius can come from any genuine actual-point supplier. -/
theorem original_radius_conversion (x s t N p q k R L : PTm n)
    (hpq : Γ ⊢[PRAAx] le p q) (hN : Γ ⊢[PRAAx] le (unit t) N)
    (hP : Γ ⊢[PRAAx] le (unit t) (unit s))
    (hx : Γ ⊢[PRAAx] bounded x
      (oldNumerator N (rootDenominator N q (succ k) R) (scale p q k) L (unit s))
      (oldDenominator (rootDenominator N q (succ k) R) (unit s))) : Γ ⊢[PRAAx]
    bounded x (numerator t p q k R L) (denominator t p k R) := by
  let D := rootDenominator N q (succ k) R
  have hND : Γ ⊢[PRAAx] le N D := root_denominator_ge N q k R
  have hV := unit_positive (Γ := Γ) t
  have hN1 := le_trans hV hN
  have hD := le_trans hN1 hND
  have leading : Γ ⊢[PRAAx] le (N*scale p q k*unit (height p (succ k) R)) (succ k*D) :=
    le_congr (by ipra_ring) (by unfold D rootDenominator; ipra_ring) (mul_le_mul_right N (leading_height_budget p q k R hpq))
  have square : Γ ⊢[PRAAx] le (N*unit t) (D*D) :=
    AnalyticNumberTheory.PhiLower.le_mul_mono hND (le_trans hN hND)
  have observation : Γ ⊢[PRAAx] le (N*unit t) (D*unit s) := AnalyticNumberTheory.PhiLower.le_mul_mono hND hP
  exact point_radius_conversion x N D (scale p q k) L (unit s) (succ k) (unit (height p (succ k) R)) (unit t)
    hD (unit_positive s) (unit_positive _) hV leading square observation hx

def output (t p q k R L : PTm n) : PTm n := pairT (numerator t p q k R L)
  (pairT (denominator t p k R) (residual (scale p q k) L))
def outputF : PR 6 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
def run (t p q k R L : PTm n) : PTm n := PTm.app outputF ![t,p,q,k,R,L]
ipra_subst output
theorem program_at (t p q k R L : PTm n) : Γ ⊢[PRAAx] run t p q k R L ≐ output t p q k R L := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) ![t,p,q,k,R,L]
theorem returned_numerator (t p q k R L : PTm n) : Γ ⊢[PRAAx] fstT (run t p q k R L) ≐ numerator t p q k R L :=
  (program_at t p q k R L).fstE
theorem returned_tail (t p q k R L : PTm n) : Γ ⊢[PRAAx] sndT (run t p q k R L) ≐ pairT (denominator t p k R) (residual (scale p q k) L) :=
  (program_at t p q k R L).sndE
theorem returned_denominator (t p q k R L : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run t p q k R L)) ≐ denominator t p k R :=
  (returned_tail t p q k R L).fstE
theorem returned_residual (t p q k R L : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run t p q k R L)) ≐ residual (scale p q k) L :=
  (returned_tail t p q k R L).sndE

theorem exact_native_lower_radius_clearing_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (le (var 0*var 2*var 6) (var 5*var 1) ⟶ le (var 0*var 7) (var 1*var 1) ⟶ le (var 0*var 7) (var 1*var 4) ⟶
      le (oldNumerator (var 0) (var 1) (var 2) (var 3) (var 4)*nativeDenominator (var 6) (var 7))
        (nativeNumerator (var 5) (var 6) (var 2) (var 3) (var 7)*oldDenominator (var 1) (var 4))) :=
  closeUniv 8 (.impI (.impI (.impI (cleared_radius _ _ _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem original_lower_root_leading_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (var 0) (var 1) ⟶ le (scale (var 0) (var 1) (var 2)*unit (height (var 0) (succ (var 2)) (var 3)))
      (succ (var 2)*unit (height (var 1) (succ (var 2)) (var 3)))) :=
  closeUniv 4 (.impI (leading_height_budget _ _ _ _ Prf.hyp0))
theorem actual_original_lower_finite_radius_conversion_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (le (var 4) (var 5) ⟶ le (unit (var 2)) (var 3) ⟶ le (unit (var 2)) (unit (var 1)) ⟶
      bounded (var 0)
        (oldNumerator (var 3) (rootDenominator (var 3) (var 5) (succ (var 6)) (var 7)) (scale (var 4) (var 5) (var 6)) (var 8) (unit (var 1)))
        (oldDenominator (rootDenominator (var 3) (var 5) (succ (var 6)) (var 7)) (unit (var 1))) ⟶
      bounded (var 0) (numerator (var 2) (var 4) (var 5) (var 6) (var 7) (var 8)) (denominator (var 2) (var 4) (var 6) (var 7))) :=
  closeUniv 9 (.impI (.impI (.impI (.impI (original_radius_conversion _ _ _ _ _ _ _ _ _ Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))
theorem actual_original_lower_finite_budget_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (program_at _ _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianEulerLowerTailFiniteBudget

import IPRADerivations.Analysis.Optimization.Aggregates.AggregateApproximatePointMap

/-!
# Exact rational distance cuts for the prescribed approximate point map

Finite-demand Section 3 states that the actual extension fhat is L-Lipschitz.
The finite meaning of distance <= C/D is the displayed mixed-observation
cut, with exactly the two original name errors. Its diagonal form is
proved equivalent using regularity and one actual integer-gap query.
The SAME pointF, clock and packed data preserve this cut with bound
(A*C)/(B*D). No completed function, limit or preimage selector is assumed.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.AggregateApproximateLipschitz

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open AggregateEquality (sample unit unit_positive)
open AggregateOptimization (pointRegular pointRegular_at)
open AggregateApproximateImage (mapContract map_at data clock)
open AggregateApproximatePointMap (pointF mapped point_at)
open RationalHausdorff (pointRadius)
open RationalPointDistanceVariation (pointNumerator pointDenominator point_bound_of_radius point_radius_of_bound)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def numerator (C D s t : PTm n) : PTm n := C*unit s*unit t+D*(unit s+unit t)
def denominator (D s t : PTm n) : PTm n := D*unit s*unit t

def distanceBounded (U V : PR 2) (d C D x : PTm n) : Fm PTm n :=
  .all (.all (pointRadius (sample U (var 1) (Syn.shift (Syn.shift x)))
    (sample V (var 0) (Syn.shift (Syn.shift x))) (Syn.shift (Syn.shift d))
    (numerator (Syn.shift (Syn.shift C)) (Syn.shift (Syn.shift D)) (var 1) (var 0))
    (denominator (Syn.shift (Syn.shift D)) (var 1) (var 0))))

def diagonalBounded (U V : PR 2) (d C D x : PTm n) : Fm PTm n :=
  .all (pointRadius (sample U (var 0) (Syn.shift x)) (sample V (var 0) (Syn.shift x))
    (Syn.shift d) (Syn.shift C*unit (var 0)+two*Syn.shift D) (Syn.shift D*unit (var 0)))

@[simp] theorem subst_numerator {l : ℕ} (σ : Fin n → PTm l) (C D s t : PTm n) :
    Syn.subst σ (numerator C D s t) = numerator (Syn.subst σ C) (Syn.subst σ D) (Syn.subst σ s) (Syn.subst σ t) := by simp [numerator]
@[simp] theorem subst_denominator {l : ℕ} (σ : Fin n → PTm l) (D s t : PTm n) :
    Syn.subst σ (denominator D s t) = denominator (Syn.subst σ D) (Syn.subst σ s) (Syn.subst σ t) := by simp [denominator]
@[simp] theorem subst_distanceBounded {l : ℕ} (σ : Fin n → PTm l) (U V : PR 2) (d C D x : PTm n) :
    (distanceBounded U V d C D x).subst σ = distanceBounded U V (Syn.subst σ d) (Syn.subst σ C) (Syn.subst σ D) (Syn.subst σ x) := by
  simp only [distanceBounded,Fm.subst_all,RationalHausdorff.subst_pointRadius,AggregateEquality.subst_sample,
    subst_numerator,subst_denominator,Syn.subst_var,Syn.up_zero,Syn.up_one,Syn.up_succ,Syn.subst_shift,Syn.shift_subst,
    Syn.shift_var,Fin.succ_zero_eq_one]
@[simp] theorem subst_diagonalBounded {l : ℕ} (σ : Fin n → PTm l) (U V : PR 2) (d C D x : PTm n) :
    (diagonalBounded U V d C D x).subst σ = diagonalBounded U V (Syn.subst σ d) (Syn.subst σ C) (Syn.subst σ D) (Syn.subst σ x) := by
  simp only [diagonalBounded,Fm.subst_all,RationalHausdorff.subst_pointRadius,AggregateEquality.subst_sample,
    AggregateEquality.subst_unit,PTm.subst_add,PTm.subst_mul,Syn.subst_var,Syn.up_zero,Syn.up_one,Syn.up_succ,
    Syn.subst_shift,Syn.shift_subst,one,two,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero]

theorem distance_at (U V : PR 2) (d C D x s t : PTm n)
    (h : Γ ⊢[PRAAx] distanceBounded U V d C D x) : Γ ⊢[PRAAx]
    pointRadius (sample U s x) (sample V t x) d (numerator C D s t) (denominator D s t) := by
  have a : Γ ⊢[PRAAx] .all (pointRadius (sample U (Syn.shift s) (Syn.shift x))
      (sample V (var 0) (Syn.shift x)) (Syn.shift d)
      (numerator (Syn.shift C) (Syn.shift D) (Syn.shift s) (var 0))
      (denominator (Syn.shift D) (Syn.shift s) (var 0))) := by
    simpa only [distanceBounded,Fm.subst_all,RationalHausdorff.subst_pointRadius,AggregateEquality.subst_sample,
      subst_numerator,subst_denominator,Syn.subst_var,Syn.up_zero,Syn.up_one,Syn.up_succ,
      AnalyticNumberTheory.Fermat.subst_up_shift',Syn.inst_zero,Syn.inst_succ,Syn.subst_inst_shift,Syn.shift_var] using Prf.allE s h
  simpa [Syn.inst_zero,Syn.inst_succ,Syn.subst_inst_shift] using Prf.allE t a

theorem diagonal_at (U V : PR 2) (d C D x v : PTm n)
    (h : Γ ⊢[PRAAx] diagonalBounded U V d C D x) : Γ ⊢[PRAAx]
    pointRadius (sample U v x) (sample V v x) d (C*unit v+two*D) (D*unit v) := by
  simpa [diagonalBounded] using Prf.allE v h

theorem denominator_positive (D s t : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] le one (denominator D s t) :=
  AggregateApproximateImage.positive_product _ _
    (AggregateApproximateImage.positive_product _ _ hD (unit_positive s)) (unit_positive t)

/-- A single explicit query removes all auxiliary slack in an actual rational
point comparison. No radius denominator or native numerator is cancelled. -/
theorem remove_slack (q r d A B E : PTm n)
    (h : Γ ⊢[PRAAx] pointRadius q r d
      (A*unit (E*pointDenominator q r d)+E) (B*unit (E*pointDenominator q r d))) :
    Γ ⊢[PRAAx] pointRadius q r d A B := by
  have actual := point_bound_of_radius q r d _ _ h
  apply point_radius_of_bound
  apply GapRemoval.gap (C := E*pointDenominator q r d)
  exact le_congr (by unfold unit; ipra_ring) (by unfold unit; ipra_ring) actual

/-- The two name errors plus the central diagonal comparison cost exactly
four auxiliary errors, independently of either raw point denominator. -/
theorem diagonal_bridge (U V : PR 2) (d C D x s t v : PTm n)
    (hD : Γ ⊢[PRAAx] le one D)
    (hU : Γ ⊢[PRAAx] pointRegular U d x) (hV : Γ ⊢[PRAAx] pointRegular V d x)
    (h : Γ ⊢[PRAAx] diagonalBounded U V d C D x) : Γ ⊢[PRAAx]
    pointRadius (sample U s x) (sample V t x) d
      (numerator C D s t*unit v+PTm.num 4*D*unit s*unit t) (denominator D s t*unit v) := by
  have first := pointRegular_at U s v d x hU
  have middle := diagonal_at U V d C D x v h
  have last := pointRegular_at V v t d x hV
  have joined := RationalHausdorffTriangle.pointRadius_triangle _ _ _ d _ _ _ _
    (RationalHausdorffTriangle.pointRadius_triangle _ _ _ d _ _ _ _ first middle) last
  have pos := AggregateApproximateImage.positive_product (Γ := Γ) _ _
      (AggregateApproximateImage.positive_product _ _
        (AggregateApproximateImage.positive_product _ _ (unit_positive s) (unit_positive v))
        (AggregateApproximateImage.positive_product _ _ hD (unit_positive v)))
      (AggregateApproximateImage.positive_product _ _ (unit_positive v) (unit_positive t))
  exact AggregateChain.point_mono _ _ _ _ _ _ _ pos joined
    (le_of_eq_add (d := ConciseIPRA.PTm.zero) (by unfold numerator denominator; ipra_ring))

theorem distance_of_diagonal_at (U V : PR 2) (d C D x s t : PTm n)
    (hD : Γ ⊢[PRAAx] le one D)
    (hU : Γ ⊢[PRAAx] pointRegular U d x) (hV : Γ ⊢[PRAAx] pointRegular V d x)
    (h : Γ ⊢[PRAAx] diagonalBounded U V d C D x) : Γ ⊢[PRAAx]
    pointRadius (sample U s x) (sample V t x) d (numerator C D s t) (denominator D s t) := by
  let E := PTm.num 4*D*unit s*unit t
  exact remove_slack _ _ _ _ _ E
    (diagonal_bridge U V d C D x s t (E*pointDenominator (sample U s x) (sample V t x) d) hD hU hV h)

theorem diagonal_of_distance_at (U V : PR 2) (d C D x v : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (h : Γ ⊢[PRAAx] distanceBounded U V d C D x) : Γ ⊢[PRAAx]
    pointRadius (sample U v x) (sample V v x) d (C*unit v+two*D) (D*unit v) :=
  AggregateChain.point_mono _ _ _ _ _ _ _ (denominator_positive _ _ _ hD)
    (distance_at U V d C D x v v h) (by
      apply le_of_eq_add (d := ConciseIPRA.PTm.zero)
      unfold numerator denominator
      ipra_ring)

theorem distance_of_diagonal (U V : PR 2) (d C D x : PTm n)
    (hD : Γ ⊢[PRAAx] le one D)
    (hU : Γ ⊢[PRAAx] pointRegular U d x) (hV : Γ ⊢[PRAAx] pointRegular V d x)
    (h : Γ ⊢[PRAAx] diagonalBounded U V d C D x) : Γ ⊢[PRAAx] distanceBounded U V d C D x := by
  refine .allI (.allI ?_)
  have d' : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (Syn.shift (Syn.shift D)) := by
    simpa [Fm.shift,Syn.shift,one] using hD.shift.shift
  have u' : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] pointRegular U (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift x)) := by
    simpa [Fm.shift,Syn.shift] using hU.shift.shift
  have v' : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] pointRegular V (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift x)) := by
    simpa [Fm.shift,Syn.shift] using hV.shift.shift
  have a' : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] diagonalBounded U V (Syn.shift (Syn.shift d))
      (Syn.shift (Syn.shift C)) (Syn.shift (Syn.shift D)) (Syn.shift (Syn.shift x)) := by
    simpa [Fm.shift,Syn.shift] using h.shift.shift
  exact distance_of_diagonal_at U V _ _ _ _ (var 1) (var 0) d' u' v' a'

theorem diagonal_of_distance (U V : PR 2) (d C D x : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (h : Γ ⊢[PRAAx] distanceBounded U V d C D x) :
    Γ ⊢[PRAAx] diagonalBounded U V d C D x := by
  refine .allI ?_
  have d' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift D) := by simpa [Fm.shift,Syn.shift,one] using hD.shift
  have a' : Γ.map Fm.shift ⊢[PRAAx] distanceBounded U V (Syn.shift d) (Syn.shift C) (Syn.shift D) (Syn.shift x) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  exact diagonal_of_distance_at U V _ _ _ _ (var 0) d' a'

theorem diagonal_iff_distance (U V : PR 2) (d C D x : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hU : Γ ⊢[PRAAx] pointRegular U d x) (hV : Γ ⊢[PRAAx] pointRegular V d x) :
    Γ ⊢[PRAAx] Fm.iff (diagonalBounded U V d C D x) (distanceBounded U V d C D x) :=
  .andI (.impI (distance_of_diagonal U V d C D x hD.wk hU.wk hV.wk Prf.hyp0))
    (.impI (diagonal_of_distance U V d C D x hD.wk Prf.hyp0))

/-- The exact native budget: multiplying the source distance cut by A/B
and paying the original two evaluator errors preserves the SAME name cut. -/
theorem mapped_budget (A B C D c s t : PTm n)
    (hc : Γ ⊢[PRAAx] le (A+B) (B*unit c)) : Γ ⊢[PRAAx] le
    (AggregateOptimization.errorNumerator A B (numerator C D (s+c) (t+c))
      (denominator D (s+c) (t+c)) (s+c) (t+c)*denominator (B*D) s t)
    (numerator (A*C) (B*D) s t*AggregateOptimization.errorDenominator B
      (denominator D (s+c) (t+c)) (s+c) (t+c)) := by
  have es := natEq (AggregateChain.unit_add (Γ := Γ) s c)
  have et := natEq (AggregateChain.unit_add (Γ := Γ) t c)
  have bound := mul_le_mul_right (B*D*D*(unit s+unit t)*unit s*unit s*unit t*unit t*unit c*unit c*unit c) hc
  refine le_congr ?_ ?_ (add_le_add₂ (le_refl (A*C*B*D*unit s*unit s*unit s*unit t*unit t*unit t*unit c*unit c*unit c*unit c)) bound)
  all_goals
    apply deriveNat
    simp only [numerator,denominator,AggregateOptimization.errorNumerator,AggregateOptimization.errorDenominator]
    ipra_simps
    rw [es,et]
    ring

theorem mapped_distance_at (U V : PR 2) (f : PR 3) (d e A B C D c x s t : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (hc : Γ ⊢[PRAAx] le (A+B) (B*unit c))
    (h : Γ ⊢[PRAAx] distanceBounded U V d C D x)
    (hmap : Γ ⊢[PRAAx] mapContract f d e A B x) : Γ ⊢[PRAAx]
    pointRadius (mapped U f s c x) (mapped V f t c x) e
      (numerator (A*C) (B*D) s t) (denominator (B*D) s t) := by
  have source := distance_at U V d C D x (s+c) (t+c) h
  have actual := map_at f d e A B x _ _ (s+c) (t+c) _ _ hmap source
  exact AggregateChain.point_mono _ _ _ _ _ _ _
    (AggregateApproximateImage.denominator_positive B (denominator D (s+c) (t+c)) (s+c) (t+c) hB
      (denominator_positive _ _ _ hD)) actual (mapped_budget A B C D c s t hc)

theorem mapped_distance (U V : PR 2) (f : PR 3) (d e A B C D c x : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (hc : Γ ⊢[PRAAx] le (A+B) (B*unit c))
    (h : Γ ⊢[PRAAx] distanceBounded U V d C D x)
    (hmap : Γ ⊢[PRAAx] mapContract f d e A B x) : Γ ⊢[PRAAx]
    distanceBounded (pointF U f) (pointF V f) e (A*C) (B*D) (data c x) := by
  refine .allI (.allI ?_)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let d' := Syn.shift (Syn.shift d)
  let e' := Syn.shift (Syn.shift e)
  let a := Syn.shift (Syn.shift A)
  let b := Syn.shift (Syn.shift B)
  let C' := Syn.shift (Syn.shift C)
  let D' := Syn.shift (Syn.shift D)
  let c' := Syn.shift (Syn.shift c)
  let y := Syn.shift (Syn.shift x)
  have b' : Δ ⊢[PRAAx] le one b := by simpa [Δ,b,Fm.shift,Syn.shift,one] using hB.shift.shift
  have Dp : Δ ⊢[PRAAx] le one D' := by simpa [Δ,D',Fm.shift,Syn.shift,one] using hD.shift.shift
  have cp : Δ ⊢[PRAAx] le (a+b) (b*unit c') := by simpa [Δ,a,b,c',Fm.shift,Syn.shift] using hc.shift.shift
  have hp : Δ ⊢[PRAAx] distanceBounded U V d' C' D' y := by simpa [Δ,d',C',D',y,Fm.shift,Syn.shift] using h.shift.shift
  have lp : Δ ⊢[PRAAx] mapContract f d' e' a b y := by simpa [Δ,d',e',a,b,y,Fm.shift,Syn.shift] using hmap.shift.shift
  simpa [Δ,d',e',a,b,C',D',c',y,Syn.shift] using AggregateChain.point_congr
    (point_at U f (var 1) c' y).eqSymm (point_at V f (var 0) c' y).eqSymm
    (.eqRefl _) (.eqRefl _) (.eqRefl _) (mapped_distance_at U V f d' e' a b C' D' c' y (var 1) (var 0) b' Dp cp hp lp)

theorem computed_distance (U V : PR 2) (f : PR 3) (d e A B C D x : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] distanceBounded U V d C D x)
    (hmap : Γ ⊢[PRAAx] mapContract f d e A B x) : Γ ⊢[PRAAx]
    distanceBounded (pointF U f) (pointF V f) e (A*C) (B*D) (data (clock A B) x) :=
  mapped_distance U V f d e A B C D (clock A B) x hB hD
    (AggregateApproximateImage.clock_budget A B hB) h hmap

/-- Original point regularity, the source diagonal distance cut and the
original approximate Lipschitz contract are the only semantic inputs. -/
theorem represented_lipschitz (U V : PR 2) (f : PR 3) (d e A B C D x : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (hU : Γ ⊢[PRAAx] pointRegular U d x) (hV : Γ ⊢[PRAAx] pointRegular V d x)
    (h : Γ ⊢[PRAAx] diagonalBounded U V d C D x)
    (hmap : Γ ⊢[PRAAx] mapContract f d e A B x) : Γ ⊢[PRAAx]
    diagonalBounded (pointF U f) (pointF V f) e (A*C) (B*D) (data (clock A B) x) :=
  diagonal_of_distance _ _ _ _ _ _ (AggregateApproximateImage.positive_product _ _ hB hD)
    (computed_distance U V f d e A B C D x hB hD (distance_of_diagonal U V d C D x hD hU hV h) hmap)

theorem zero_diagonal_equivalent (U V : PR 2) (d x : PTm n)
    (h : Γ ⊢[PRAAx] diagonalBounded U V d ConciseIPRA.PTm.zero one x) :
    Γ ⊢[PRAAx] AggregateDistanceName.pointEquivalent U V d x := by
  refine .allI ?_
  have a : Γ.map Fm.shift ⊢[PRAAx] diagonalBounded U V (Syn.shift d) ConciseIPRA.PTm.zero one (Syn.shift x) := by
    simpa [Fm.shift,Syn.shift,one] using h.shift
  exact AggregateChain.point_congr (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (by ipra_ring) (one_mul _) (diagonal_at U V _ _ _ _ (var 0) a)

theorem zero_diagonal_of_equivalent (U V : PR 2) (d x : PTm n)
    (h : Γ ⊢[PRAAx] AggregateDistanceName.pointEquivalent U V d x) :
    Γ ⊢[PRAAx] diagonalBounded U V d ConciseIPRA.PTm.zero one x := by
  refine .allI ?_
  have a : Γ.map Fm.shift ⊢[PRAAx] AggregateDistanceName.pointEquivalent U V (Syn.shift d) (Syn.shift x) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  simpa [Syn.shift,one] using AggregateChain.point_congr (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (show Γ.map Fm.shift ⊢[PRAAx] two ≐ ConciseIPRA.PTm.zero*unit (var 0)+two*one by ipra_ring)
    (one_mul _).eqSymm (AggregateDistanceName.point_equivalent_at U V (var 0) (Syn.shift d) (Syn.shift x) a)

theorem zero_distance_iff_equivalent (U V : PR 2) (d x : PTm n)
    (hU : Γ ⊢[PRAAx] pointRegular U d x) (hV : Γ ⊢[PRAAx] pointRegular V d x) : Γ ⊢[PRAAx]
    Fm.iff (distanceBounded U V d ConciseIPRA.PTm.zero one x) (AggregateDistanceName.pointEquivalent U V d x) :=
  .andI (.impI (zero_diagonal_equivalent U V d x
      (diagonal_of_distance U V d _ _ x (le_refl _) Prf.hyp0)))
    (.impI (distance_of_diagonal U V d _ _ x (le_refl _) hU.wk hV.wk
      (zero_diagonal_of_equivalent U V d x Prf.hyp0)))

/-- Actual original point observations and their resulting rational bound.
The program uses the already prescribed clock and point producers. -/
def output (U V : PR 2) (f : PR 3) (s t A B C D x : PTm n) : PTm n :=
  pairT (AggregateApproximatePointMap.computed U f s A B x)
    (pairT (AggregateApproximatePointMap.computed V f t A B x) (pairT (A*C) (B*D)))
def outputF (U V : PR 2) (f : PR 3) : PR 7 :=
  PTm.toPR (output U V f (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
def run (U V : PR 2) (f : PR 3) (s t A B C D x : PTm n) : PTm n :=
  PTm.app (outputF U V f) ![s,t,A,B,C,D,x]

@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (U V : PR 2) (f : PR 3) (s t A B C D x : PTm n) :
    Syn.subst σ (output U V f s t A B C D x) = output U V f (Syn.subst σ s) (Syn.subst σ t)
      (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ C) (Syn.subst σ D) (Syn.subst σ x) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (U V : PR 2) (f : PR 3) (s t A B C D x : PTm n) :
    Syn.subst σ (run U V f s t A B C D x) = run U V f (Syn.subst σ s) (Syn.subst σ t)
      (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ C) (Syn.subst σ D) (Syn.subst σ x) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem run_at (U V : PR 2) (f : PR 3) (s t A B C D x : PTm n) : Γ ⊢[PRAAx]
    run U V f s t A B C D x ≐ output U V f s t A B C D x := by
  simpa [run,outputF] using
    toPR_eq (Γ := Γ) (output U V f (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) : PTm 7) ![s,t,A,B,C,D,x]

theorem returned_left (U V : PR 2) (f : PR 3) (s t A B C D x : PTm n) : Γ ⊢[PRAAx]
    fstT (run U V f s t A B C D x) ≐ AggregateApproximatePointMap.computed U f s A B x :=
  (congrFst (run_at U V f s t A B C D x)).eqTrans (fst_pair _ _)
theorem returned_right (U V : PR 2) (f : PR 3) (s t A B C D x : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run U V f s t A B C D x)) ≐ AggregateApproximatePointMap.computed V f t A B x :=
  (congrFst ((congrSnd (run_at U V f s t A B C D x)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_numerator (U V : PR 2) (f : PR 3) (s t A B C D x : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (run U V f s t A B C D x))) ≐ A*C :=
  (congrFst ((congrSnd ((congrSnd (run_at U V f s t A B C D x)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_denominator (U V : PR 2) (f : PR 3) (s t A B C D x : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (run U V f s t A B C D x))) ≐ B*D :=
  (congrSnd ((congrSnd ((congrSnd (run_at U V f s t A B C D x)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)

theorem returned_distance (U V : PR 2) (f : PR 3) (d e A B C D x s t : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] distanceBounded U V d C D x)
    (hmap : Γ ⊢[PRAAx] mapContract f d e A B x) : Γ ⊢[PRAAx]
    pointRadius (fstT (run U V f s t A B C D x)) (fstT (sndT (run U V f s t A B C D x))) e
      (numerator (fstT (sndT (sndT (run U V f s t A B C D x))))
        (sndT (sndT (sndT (run U V f s t A B C D x)))) s t)
      (denominator (sndT (sndT (sndT (run U V f s t A B C D x)))) s t) := by
  have actual := mapped_distance_at U V f d e A B C D (clock A B) x s t hB hD
    (AggregateApproximateImage.clock_budget A B hB) h hmap
  have nc : Γ ⊢[PRAAx] numerator (A*C) (B*D) s t ≐
      numerator (fstT (sndT (sndT (run U V f s t A B C D x))))
        (sndT (sndT (sndT (run U V f s t A B C D x)))) s t := by
    unfold numerator
    exact congrAdd (congrMul (congrMul (returned_numerator U V f s t A B C D x).eqSymm (.eqRefl _)) (.eqRefl _))
      (congrMul (returned_denominator U V f s t A B C D x).eqSymm (.eqRefl _))
  have dc : Γ ⊢[PRAAx] denominator (B*D) s t ≐ denominator
      (sndT (sndT (sndT (run U V f s t A B C D x)))) s t :=
    congrMul (congrMul (returned_denominator U V f s t A B C D x).eqSymm (.eqRefl _)) (.eqRefl _)
  exact AggregateChain.point_congr (returned_left U V f s t A B C D x).eqSymm
    (returned_right U V f s t A B C D x).eqSymm (.eqRefl _) nc dc actual

theorem diagonal_distance_closed (U V : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 2) ⟶ pointRegular U (var 0) (var 3) ⟶ pointRegular V (var 0) (var 3) ⟶
      Fm.iff (diagonalBounded U V (var 0) (var 1) (var 2) (var 3))
        (distanceBounded U V (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (.impI (.impI (diagonal_iff_distance U V _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

theorem represented_lipschitz_closed (U V : PR 2) (f : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (le one (var 3) ⟶ le one (var 5) ⟶ pointRegular U (var 0) (var 6) ⟶ pointRegular V (var 0) (var 6) ⟶
      diagonalBounded U V (var 0) (var 4) (var 5) (var 6) ⟶ mapContract f (var 0) (var 1) (var 2) (var 3) (var 6) ⟶
        diagonalBounded (pointF U f) (pointF V f) (var 1) (var 2*var 4) (var 3*var 5)
          (data (clock (var 2) (var 3)) (var 6))) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (.impI (.impI (represented_lipschitz U V f _ _ _ _ _ _ _
    Prf.hyp1.wk.wk.wk.wk Prf.hyp1.wk.wk.wk Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))))

theorem zero_cut_equivalence_closed (U V : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (pointRegular U (var 0) (var 1) ⟶ pointRegular V (var 0) (var 1) ⟶
      Fm.iff (distanceBounded U V (var 0) ConciseIPRA.PTm.zero one (var 1))
        (AggregateDistanceName.pointEquivalent U V (var 0) (var 1))) :=
  closeUniv 2 (.impI (.impI (zero_distance_iff_equivalent U V _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_program_closed (U V : PR 2) (f : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (run U V f (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ≐
      output U V f (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) :=
  closeUniv 7 (run_at U V f _ _ _ _ _ _ _)

theorem returned_distance_closed (U V : PR 2) (f : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (le one (var 3) ⟶ le one (var 5) ⟶ distanceBounded U V (var 0) (var 4) (var 5) (var 6) ⟶
      mapContract f (var 0) (var 1) (var 2) (var 3) (var 6) ⟶
        pointRadius (fstT (run U V f (var 7) (var 8) (var 2) (var 3) (var 4) (var 5) (var 6)))
          (fstT (sndT (run U V f (var 7) (var 8) (var 2) (var 3) (var 4) (var 5) (var 6)))) (var 1)
          (numerator (fstT (sndT (sndT (run U V f (var 7) (var 8) (var 2) (var 3) (var 4) (var 5) (var 6)))))
            (sndT (sndT (sndT (run U V f (var 7) (var 8) (var 2) (var 3) (var 4) (var 5) (var 6))))) (var 7) (var 8))
          (denominator (sndT (sndT (sndT (run U V f (var 7) (var 8) (var 2) (var 3) (var 4) (var 5) (var 6))))) (var 7) (var 8))) :=
  closeUniv 9 (.impI (.impI (.impI (.impI (returned_distance U V f _ _ _ _ _ _ _ _ _
    Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.AggregateApproximateLipschitz

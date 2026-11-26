import IPRADerivations.Analysis.Barnes.Logarithms.GaussianBarnesCanonicalFiniteLog
import IPRADerivations.Analysis.Barnes.Logarithms.GaussianBarnesCanonicalLogRowFractionProperness
import IPRADerivations.Analysis.Names.GaussianNameEquivalence

/-!
# Rational presentation independence of the original finite Barnes logarithm

Exact equality of the unrounded finite sums compares the original
quotient-rounded observations. The existing rounding clock and regularity
give cross-equivalence at independent observation precisions.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteLogFractionProperness

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalFiniteLog (clock clock_budget data nameF regular rounding_gain sample_at)
open GaussianBarnesCanonicalLogTail (body body_at source)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (crossEquivalent diagonalEquivalent diagonal_to_cross)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalFiniteSum (termsEqual)
open GaussianRationalHorner (ofGaussian)
open GaussianRationalMetric (distanceBounded)
open ConciseIPRA.PTm (succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem unrounded_tail_equal (z w B D N r L : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] GaussianBarnesCanonicalLogTail.value z B N r L ≐
      GaussianBarnesCanonicalLogTail.value w D N r L := by
  apply GaussianRationalFiniteSum.sum_congr_bounded body body r
    (GaussianBarnesCanonicalLogTail.data z B N L) (GaussianBarnesCanonicalLogTail.data w D N L)
  refine .allI (.impI ?_)
  let sh (u : PTm n) := Syn.shift u
  let Δ := lt (var 0) (sh r) :: Γ.map Fm.shift
  let i : PTm (n+1) := var 0
  have hb : Δ ⊢[PRAAx] le one (sh B) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hB.shift.wk
  have hd : Δ ⊢[PRAAx] le one (sh D) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hD.shift.wk
  have eq : Δ ⊢[PRAAx] ofGaussian (sh z) (sh B) ≐ ofGaussian (sh w) (sh D) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using he.shift.wk
  have rows := GaussianBarnesCanonicalLogRowFractionProperness.finite_row_equal
    (sh z) (sh w) (sh B) (sh D) (succ (sh N+i)) (sh L) hb hd (zero_lt_succ _) eq
  simpa only [termsEqual,GaussianBarnesCanonicalLogTail.subst_data,Syn.shift,sh,Δ,i] using
    (body_at (sh z) (sh B) (sh N) (sh L) i).eqTrans
      (rows.eqTrans (body_at (sh w) (sh D) (sh N) (sh L) i).eqSymm)

def unroundedObservation (p z B N r : PTm n) : PTm n :=
  GaussianBarnesCanonicalLogTail.value z B N r (DyadicComplexLogarithm.precision (clock p N r))

theorem observation_error (p z R B N r : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data z R B N r)) (unroundedObservation p z B N r) one (unit p) := by
  let v := clock p N r
  have paid := clock_budget (r*(two*(N+r))) p N r v (rounding_gain (Γ := Γ) N r) (le_refl v)
  exact distance_congr (sample_at p z R B N r).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ (GaussianLocalLogarithmName.unit_positive v) (unit_positive p)
      (le_congr (.eqRefl _) (one_mul _).eqSymm paid)
      (GaussianBarnesCanonicalLogRoundedTail.rounding_error v z R B N r h))

theorem diagonal_observation (p z w R S B D N r : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B N) (hw : Γ ⊢[PRAAx] source w S D N)
    (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data z R B N r)) (ap2 nameF p (data w S D N r)) two (unit p) := by
  have same : Γ ⊢[PRAAx] unroundedObservation p z B N r ≐ unroundedObservation p w D N r :=
    unrounded_tail_equal z w B D N r _ hz.andE₁ hw.andE₁ he
  have first := observation_error p z R B N r hz
  have second := distance_congr (.eqRefl _) same.eqSymm (.eqRefl _) (.eqRefl _) (observation_error p w S D N r hw)
  have together := distance_triangle_same _ _ _ _ _ _ (unit_positive p) first
    (distance_symmetric _ _ _ _ (unit_positive p) second)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _) together

theorem proper (z w R S B D N r : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B N) (hw : Γ ⊢[PRAAx] source w S D N)
    (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] crossEquivalent nameF nameF (data z R B N r) (data w S D N r) := by
  apply diagonal_to_cross nameF nameF _ _ (regular z R B N r hz) (regular w S D N r hw)
  refine .allI ?_
  let sh (u : PTm n) := Syn.shift u
  have hzs : Γ.map Fm.shift ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh N) := by
    simpa [sh,Fm.shift,Syn.shift] using hz.shift
  have hws : Γ.map Fm.shift ⊢[PRAAx] source (sh w) (sh S) (sh D) (sh N) := by
    simpa [sh,Fm.shift,Syn.shift] using hw.shift
  have hes : Γ.map Fm.shift ⊢[PRAAx] ofGaussian (sh z) (sh B) ≐ ofGaussian (sh w) (sh D) := by
    simpa [sh,Fm.shift,Syn.shift] using he.shift
  simpa only [diagonalEquivalent,GaussianBarnesCanonicalFiniteLog.subst_data,Syn.shift,sh] using
    diagonal_observation (var 0) (sh z) (sh w) (sh R) (sh S) (sh B) (sh D) (sh N) (sh r) hzs hws hes

theorem actual_Barnes_finite_log_interval_fraction_proper_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (let z := var 0
     let w := var 1
     let R := var 2
     let S := var 3
     let B := var 4
     let D := var 5
     let N := var 6
     let r := var 7
     (source z R B N ⋏ (source w S D N ⋏ (ofGaussian z B ≐ ofGaussian w D))) ⟶
       crossEquivalent nameF nameF (data z R B N r) (data w S D N r)) :=
  closeUniv 8 (.impI (proper _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteLogFractionProperness

import IPRADerivations.Analysis.Stirling.Raabe.GaussianRaabeUnitGridRecurrence
import IPRADerivations.Analysis.Integration.GaussianCompactAlignedTime
import IPRADerivations.Analysis.Logarithm.GaussianCompactLogarithmBounds
import IPRADerivations.Analysis.Stirling.GaussianStirlingGammaFractionalIncrementConvexity

/-!
# Equal rational tags for the actual real log-Gamma evaluator

Two positive rational tags with the same physical value share a
common product-denominator encoding. The unchanged observations of
the real log-Gamma name then have only their two dyadic allowances.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianRaabeLogGammaAlignedTime

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit)
open GaussianCompactRiemannName (inside value)
open GaussianCompactAlignedTime (alignedSamples)
open GaussianNameEquivalence (crossEquivalent cross_at cross_symm cross_trans)
open GaussianRaabeUnitGridRecurrence (logGammaEvaluator)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalMetric (distanceBounded)
open GaussianStirlingGammaFractionalIncrementConvexity (gamma_rescale_from)
open GaussianStirlingGammaLogarithm (logGammaF logGammaData source)
open RationalHarmonicIntervalVariation (gap)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem evaluator_read (p t x : PTm n) :
    Γ ⊢[PRAAx] ap3 logGammaEvaluator p t x ≐ ap2 logGammaF p (logGammaData (fstT t) (sndT t)) := by
  let body : PTm 3 := ap2 logGammaF (var 0) (logGammaData (fstT (var 1)) (sndT (var 1)))
  let schema : PTm 3 :=
    ap2 logGammaF (var 0) (inst2 (logGammaData (var 0) (var 1)) (fstT (var 1)) (sndT (var 1)))
  have es : schema = body := by
    simp only [schema,body,inst2,GaussianStirlingGammaLogarithm.subst_logGammaData,Syn.subst_var,
      Matrix.cons_val_zero,Matrix.cons_val_one]
  have ev : logGammaEvaluator = PTm.toPR body := by
    rw [← es]
    rfl
  simpa only [ev,body,ap3,subst_ap2,GaussianStirlingGammaLogarithm.subst_logGammaData,
    subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    toPR_eq (Γ := Γ) body ![p,t,x]

theorem equal_ratio (A D B E : PTm n) (hA : Γ ⊢[PRAAx] source A D)
    (hB : Γ ⊢[PRAAx] source B E) (eq : Γ ⊢[PRAAx] A*E ≐ B*D) :
    Γ ⊢[PRAAx] crossEquivalent logGammaF logGammaF (logGammaData A D) (logGammaData B E) := by
  let t := logGammaData (A*E) (D*E)
  have left := gamma_rescale_from (A*E) (D*E) A D E hA hB.andE₂ (mul_comm A E) (mul_comm D E)
  have right := gamma_rescale_from (A*E) (D*E) B E D hB hA.andE₂
    (eq.eqTrans (mul_comm B D)) (.eqRefl (D*E))
  exact cross_trans logGammaF logGammaF logGammaF _ t _ (cross_symm _ _ _ _ left) right

private theorem gap_zero_ratio (A D B E : PTm n) (h : Γ ⊢[PRAAx] gap A D B E ≐ zero) :
    Γ ⊢[PRAAx] A*E ≐ D*B := by
  let x := LeanProofs.IPRA.PTm.monus (A*E) (D*B)
  let y := LeanProofs.IPRA.PTm.monus (D*B) (A*E)
  have hx : Γ ⊢[PRAAx] le x zero :=
    le_congr (.eqRefl x) h (le_add_right x y)
  have hy : Γ ⊢[PRAAx] le y zero :=
    le_congr (.eqRefl y) ((add_comm y x).eqTrans h) (le_add_right y x)
  exact le_antisymm
    (AnalyticNumberTheory.EulerDomination.eq_zero_of_le_zero hx)
    (AnalyticNumberTheory.EulerDomination.eq_zero_of_le_zero hy)

theorem observation (p q t u x : PTm n)
    (ht : Γ ⊢[PRAAx] source (fstT t) (sndT t)) (hu : Γ ⊢[PRAAx] source (fstT u) (sndT u))
    (h : Γ ⊢[PRAAx] distanceBounded (value t) (value u) zero one) :
    Γ ⊢[PRAAx] distanceBounded (ap3 logGammaEvaluator p t x) (ap3 logGammaEvaluator q u x)
      (unit p+unit q) (unit p*unit q) := by
  let a := fstT t
  let d := sndT t
  let b := fstT u
  let e := sndT u
  have narrow := GaussianCompactLogarithmBounds.original_gaussian_time_distance a d b e zero one
    ht.andE₂ hu.andE₂ (le_refl one) h
  have hz : Γ ⊢[PRAAx] le (gap a d b e) zero := le_congr (one_mul _) (by ipra_ring) narrow
  have ratio := gap_zero_ratio a d b e (AnalyticNumberTheory.EulerDomination.eq_zero_of_le_zero hz)
  have exactCross := equal_ratio a d b e ht hu (ratio.eqTrans (mul_comm d b))
  exact distance_congr (evaluator_read p t x).eqSymm (evaluator_read q u x).eqSymm (.eqRefl _) (.eqRefl _)
    (cross_at logGammaF logGammaF (logGammaData a d) (logGammaData b e) p q exactCross)

theorem aligned (A C D x : PTm n) : Γ ⊢[PRAAx] alignedSamples logGammaEvaluator A C D x := by
  refine .allI (.allI (.allI (.allI (.impI (.impI (.impI ?_))))))
  exact observation (var 3) (var 2) (var 1) (var 0) _
    (.andI (Prf.hyp0.wk.wk).andE₁ (Prf.hyp0.wk.wk).andE₂.andE₁)
    (.andI Prf.hyp1.andE₁ Prf.hyp1.andE₂.andE₁) Prf.hyp0

theorem actual_real_log_Gamma_aligned_time_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (alignedSamples logGammaEvaluator (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (aligned _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianRaabeLogGammaAlignedTime

import IPRADerivations.Analysis.RationalArithmetic.Grids.Minimization.RationalCubeCoherentMinimizer
import IPRADerivations.Analysis.Optimization.CubeInfimum.RationalCubeInfimumComparison
import IPRADerivations.Analysis.Optimization.Aggregates.AggregateApproximateLipschitz

/-!
# Exact uniqueness of the cube-presented minimizing point name

A competing point name supplies only its ordinary coherence, cube-domain
presentation and equality of its actual prescribed evaluation to V. Its
rational approximants are proved near-minimal by continuity. The source
quantitative uniqueness rule and one finite gap query then identify the
actual point names. No near-point or cross-name distance law is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalCubeMinimizerUniqueness

open_ipra
open RationalCubeMinimum (coherence continuity presentedCube sample precision)
open RationalCubeGrid (scale)
open RationalCubeInfimumName (value data)
open RationalCubeCoherentMinimizer (point pointName uniqueness schedule near nearAt evaluationIndex)
open RationalCubeInfimumComparison (cubePoints cube_points_at)
open RationalHausdorff (pointRadius)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def evaluation (A : PR 3) (mu b : PR 2) (p x z : PTm n) : PTm n :=
  sample A (ap2 b (evaluationIndex mu p x) z) (precision p) x
def sameValue (A : PR 3) (mu b : PR 2) (d x z : PTm n) : Fm PTm n := .all
  (RationalValueBounds.radius (evaluation A mu b (var 0) (Syn.shift x) (Syn.shift z))
    (value A mu (Syn.shift d) (var 0) (Syn.shift x)) two (scale (var 0)))
def equivalent (f g : PR 2) (d x z : PTm n) : Fm PTm n := .all (.all
  (pointRadius (ap2 f (var 1) (Syn.shift (Syn.shift x))) (ap2 g (var 0) (Syn.shift (Syn.shift z)))
    (Syn.shift (Syn.shift d)) (scale (var 1)+scale (var 0)) (scale (var 1)*scale (var 0))))

ipra_subst evaluation
ipra_subst sameValue [Syn.subst_shift, Syn.shift_subst]
ipra_subst equivalent [Syn.subst_shift, Syn.shift_subst]

theorem point_name_at (b : PR 2) (d z s t : PTm n) (h : Γ ⊢[PRAAx] pointName b d z) : Γ ⊢[PRAAx]
    pointRadius (ap2 b s z) (ap2 b t z) d (scale s+scale t) (scale s*scale t) := by
  simpa [pointName,Syn.subst_shift,Syn.shift_subst,Syn.shift,Syn.subst_subst,Function.comp_def] using (h.allE s).allE t

theorem same_value_at (A : PR 3) (mu b : PR 2) (d p x z : PTm n) (h : Γ ⊢[PRAAx] sameValue A mu b d x z) : Γ ⊢[PRAAx]
    RationalValueBounds.radius (evaluation A mu b p x z) (value A mu d p x) two (scale p) := by
  simpa [sameValue] using h.allE p

/-- Two ordinary point-name tails beyond l+1 are within the source l-radius. -/
theorem point_tail_radius (b : PR 2) (d z l s t : PTm n) (h : Γ ⊢[PRAAx] pointName b d z)
    (hs : Γ ⊢[PRAAx] le (succ l) s) (ht : Γ ⊢[PRAAx] le (succ l) t) : Γ ⊢[PRAAx]
    pointRadius (ap2 b s z) (ap2 b t z) d one (scale l) := by
  have ps : Γ ⊢[PRAAx] le (two*scale l) (scale s) :=
    le_congr ((pw_succ two l).eqTrans (mul_comm _ _)) (.eqRefl _)
      (AnalyticNumberTheory.PowerCleared.pw_le_exp Foundations.CoherentMinimizer.two_pos hs)
  have pt : Γ ⊢[PRAAx] le (two*scale l) (scale t) :=
    le_congr ((pw_succ two l).eqTrans (mul_comm _ _)) (.eqRefl _)
      (AnalyticNumberTheory.PowerCleared.pw_le_exp Foundations.CoherentMinimizer.two_pos ht)
  apply AggregateChain.point_mono _ _ _ _ _ _ _
    (RationalAlgebra.positive_product (RationalCubeGrid.scale_positive s) (RationalCubeGrid.scale_positive t)) (point_name_at b d z s t h)
  apply RationalValueBounds.positive_cancel (c := two) (le_of_eq_add (d := one) (by ipra_ring))
  exact le_congr (by ipra_ring) (by ipra_ring)
    (Foundations.FiniteHausdorff.sum_mono (mul_le_mul_right (scale t) ps) (mul_le_mul_right (scale s) pt))

/-- A fixed rational approximant is genuinely near-minimal, derived from
ordinary coherence and the actual value equality at one computed query. -/
theorem approximant_near_at (A : PR 3) (mu b : PR 2) (d x z e s p q : PTm n)
    (hc : Γ ⊢[PRAAx] coherence A d x) (ht : Γ ⊢[PRAAx] continuity A mu d x) (hN : Γ ⊢[PRAAx] pointName b d z)
    (hC : Γ ⊢[PRAAx] cubePoints b d z) (hV : Γ ⊢[PRAAx] sameValue A mu b d x z)
    (hs : Γ ⊢[PRAAx] le (succ (ap2 mu (succ e) x)) s) : Γ ⊢[PRAAx]
    nearAt A mu d x (ap2 b s z) e p q := by
  let K := s+succ (precision e)
  have sk : Γ ⊢[PRAAx] le s K := le_add_right _ _
  have kr : Γ ⊢[PRAAx] le K (evaluationIndex mu K x) :=
    le_trans (le_of_eq_add (d := two) (by unfold precision; ipra_ring)) (RationalCubeCoherentMinimizer.evaluation_index_ge mu K x)
  have hd := point_tail_radius b d z (ap2 mu (succ e) x) s (evaluationIndex mu K x) hN hs (le_trans hs (le_trans sk kr))
  have first := RationalValueBounds.upper_of_radius (Γ := Γ) _ _ _ _
    (RationalCubeMinimum.continuity_at A mu d x _ _ (succ e) p (precision K) ht
      (cube_points_at b d z s hC) (cube_points_at b d z (evaluationIndex mu K x) hC) hd)
  have diagonal := RationalValueBounds.upper_of_radius _ _ _ _ (same_value_at A mu b d K x z hV)
  have tail := RationalValueBounds.upper_of_radius _ _ _ _ (RationalCubeInfimumName.value_regular A mu d K q x hc ht)
  have second : Γ ⊢[PRAAx] RationalValueBounds.upper (evaluation A mu b K x z) (value A mu d q x)
      ((succ two)*scale q+scale K) (scale K*scale q) :=
    RationalValueBounds.upper_cancel _ _ _ _ (scale K) (RationalCubeGrid.scale_positive K)
      (RationalValueBounds.upper_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
        (RationalValueBounds.upper_triangle _ _ _ _ _ _ _ diagonal tail))
  have combined := RationalValueBounds.upper_triangle _ _ _ _ _ _ _ first second
  have kp : Γ ⊢[PRAAx] le (succ (precision e)) K := le_add_left _ _
  have third : Γ ⊢[PRAAx] scale (succ (precision e)) ≐ (two*(two*two))*scale e :=
    (pw_succ two (precision e)).eqTrans ((congrMul (RationalCubeCoherentMinimizer.scale_precision_exact e) (.eqRefl two)).eqTrans (by ipra_ring))
  have power : Γ ⊢[PRAAx] le ((two*(two*two))*scale e) (scale K) :=
    le_congr third (.eqRefl _)
      (AnalyticNumberTheory.PowerCleared.pw_le_exp Foundations.CoherentMinimizer.two_pos kp)
  apply RationalValueBounds.upper_mono _ _ _ _ _ _
    (RationalAlgebra.positive_product (RationalCubeMinimum.error_denominator_positive _ _ _)
      (RationalAlgebra.positive_product (RationalCubeGrid.scale_positive K) (RationalCubeGrid.scale_positive q))) combined
  refine le_of_eq_add (d := two*scale e*scale p*scale p*scale K*scale q*scale q*
    ((succ two)*scale e+two*monus (scale K) ((two*(two*two))*scale e))) ?_
  have ep := natEq (eq_add_of_le power)
  apply deriveNat
  simp only [RationalCubeMinimum.errorNumerator,RationalCubeMinimum.errorDenominator]
  ipra_simps
  rw [natEq (show Γ ⊢[PRAAx] scale (succ e) ≐ scale e*two from pw_succ two e),
    natEq (RationalCubeCoherentMinimizer.scale_precision_exact (Γ := Γ) K)]
  ipra_simps
  rw [ep]
  ring

theorem approximant_near (A : PR 3) (mu b : PR 2) (d x z e s : PTm n)
    (hc : Γ ⊢[PRAAx] coherence A d x) (ht : Γ ⊢[PRAAx] continuity A mu d x) (hN : Γ ⊢[PRAAx] pointName b d z)
    (hC : Γ ⊢[PRAAx] cubePoints b d z) (hV : Γ ⊢[PRAAx] sameValue A mu b d x z)
    (hs : Γ ⊢[PRAAx] le (succ (ap2 mu (succ e) x)) s) : Γ ⊢[PRAAx] near A mu d x (ap2 b s z) e := by
  refine .allI (.allI ?_)
  have c : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] coherence A (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,RationalCubeMinimum.subst_coherence,Syn.shift] using hc.shift.shift
  have t : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] continuity A mu (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,RationalCubeMinimum.subst_continuity,Syn.shift] using ht.shift.shift
  have nn : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] pointName b (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift z)) := by
    simpa only [Fm.shift,RationalCubeCoherentMinimizer.subst_pointName,Syn.shift] using hN.shift.shift
  have cc : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] cubePoints b (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift z)) := by
    simpa only [Fm.shift,RationalCubeInfimumComparison.subst_cubePoints,Syn.shift] using hC.shift.shift
  have vv : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] sameValue A mu b (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift z)) := by
    simpa only [Fm.shift,subst_sameValue,Syn.shift] using hV.shift.shift
  have ss : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le (succ (ap2 mu (succ (Syn.shift (Syn.shift e))) (Syn.shift (Syn.shift x)))) (Syn.shift (Syn.shift s)) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_succ,subst_ap2,Syn.shift] using hs.shift.shift
  simpa only [Syn.shift,subst_ap2] using approximant_near_at A mu b (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift x))
    (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift e)) (Syn.shift (Syn.shift s)) (var 1) (var 0) c t nn cc vv ss

def tailIndex (mu u : PR 2) (k x : PTm n) : PTm n := k+succ (ap2 mu (succ (ap2 u k x)) x)
ipra_subst tailIndex

theorem tail_index_ge (mu u : PR 2) (k x : PTm n) : Γ ⊢[PRAAx] le k (tailIndex mu u k x) := le_add_right _ _
theorem tail_index_modulus (mu u : PR 2) (k x : PTm n) : Γ ⊢[PRAAx]
    le (succ (ap2 mu (succ (ap2 u k x)) x)) (tailIndex mu u k x) := le_add_left _ _

/-- The actual two rational tails meet the supplied source uniqueness
hypotheses; ordinary name errors account for the remaining explicit slack. -/
theorem approximate_cross_radius (A : PR 3) (mu u b : PR 2) (d x z q t k : PTm n)
    (hc : Γ ⊢[PRAAx] coherence A d x) (ht : Γ ⊢[PRAAx] continuity A mu d x)
    (hu : Γ ⊢[PRAAx] uniqueness A mu u d x) (hN : Γ ⊢[PRAAx] pointName b d z)
    (hC : Γ ⊢[PRAAx] cubePoints b d z) (hV : Γ ⊢[PRAAx] sameValue A mu b d x z) : Γ ⊢[PRAAx]
    pointRadius (point A mu u d q x) (ap2 b t z) d
      ((scale q+scale t)*scale k+two*(scale q*scale t)) ((scale q*scale t)*scale k) := by
  let s := tailIndex mu u k x
  let l := q+k
  have ql : Γ ⊢[PRAAx] le q l := le_add_right _ _
  have kl : Γ ⊢[PRAAx] le k l := le_add_left _ _
  have first := RationalCubeCoherentMinimizer.point_later A mu u d q l x hc ht hu ql
  have middle := RationalCubeCoherentMinimizer.uniqueness_at A mu u d x k (point A mu u d l x) (ap2 b s z) hu
    (RationalCubeCoherentMinimizer.point_presented _ _ _ _ _ _) (cube_points_at b d z s hC)
    (RationalCubeCoherentMinimizer.selected_near A mu d _ _ x hc ht (RationalCubeCoherentMinimizer.schedule_modulus u k l x kl))
    (approximant_near A mu b d x z (ap2 u k x) s hc ht hN hC hV (tail_index_modulus mu u k x))
  have last := point_name_at b d z s t hN
  have combined := RationalHausdorffTriangle.pointRadius_triangle _ _ _ d _ _ _ _
    (RationalHausdorffTriangle.pointRadius_triangle _ _ _ d _ _ _ _ first middle) last
  have power : Γ ⊢[PRAAx] le (scale k) (scale s) :=
    AnalyticNumberTheory.PowerCleared.pw_le_exp Foundations.CoherentMinimizer.two_pos (tail_index_ge mu u k x)
  apply AggregateChain.point_mono _ _ _ _ _ _ _
    (RationalAlgebra.positive_product
      (RationalAlgebra.positive_product (RationalCubeGrid.scale_positive q) (RationalCubeGrid.scale_positive k))
      (RationalAlgebra.positive_product (RationalCubeGrid.scale_positive s) (RationalCubeGrid.scale_positive t))) combined
  refine le_of_eq_add (d := (scale q*scale t)*(scale q*scale t)*scale k*monus (scale s) (scale k)) ?_
  ipra_lc 𝔞(scale q)^2*𝔞(scale t)^2*𝔞(scale k)*natEq (eq_add_of_le power)

/-- Exact mixed-query equality follows by one actual rational distance-gap
query. No unknown point, limiting choice or cross-name premise is used. -/
theorem unique_radius (A : PR 3) (mu u b : PR 2) (d x z q t : PTm n)
    (hc : Γ ⊢[PRAAx] coherence A d x) (ht : Γ ⊢[PRAAx] continuity A mu d x)
    (hu : Γ ⊢[PRAAx] uniqueness A mu u d x) (hN : Γ ⊢[PRAAx] pointName b d z)
    (hC : Γ ⊢[PRAAx] cubePoints b d z) (hV : Γ ⊢[PRAAx] sameValue A mu b d x z) : Γ ⊢[PRAAx]
    pointRadius (point A mu u d q x) (ap2 b t z) d (scale q+scale t) (scale q*scale t) := by
  let E := two*(scale q*scale t)
  let C := E*RationalPointDistanceVariation.pointDenominator (point A mu u d q x) (ap2 b t z) d
  apply AggregateApproximateLipschitz.remove_slack _ _ _ _ _ E
  exact approximate_cross_radius A mu u b d x z q t C hc ht hu hN hC hV

theorem unique_name_radius (A : PR 3) (mu u b : PR 2) (d x z q t : PTm n)
    (hc : Γ ⊢[PRAAx] coherence A d x) (ht : Γ ⊢[PRAAx] continuity A mu d x)
    (hu : Γ ⊢[PRAAx] uniqueness A mu u d x) (hN : Γ ⊢[PRAAx] pointName b d z)
    (hC : Γ ⊢[PRAAx] cubePoints b d z) (hV : Γ ⊢[PRAAx] sameValue A mu b d x z) : Γ ⊢[PRAAx]
    pointRadius (ap2 (RationalCubeCoherentMinimizer.pointF A mu u) q (data d x)) (ap2 b t z) d (scale q+scale t) (scale q*scale t) :=
  RationalHausdorffConcat.pointRadius_congr (RationalCubeCoherentMinimizer.point_at A mu u d q x).eqSymm (.eqRefl _)
    (unique_radius A mu u b d x z q t hc ht hu hN hC hV)

theorem unique_name (A : PR 3) (mu u b : PR 2) (d x z : PTm n)
    (hc : Γ ⊢[PRAAx] coherence A d x) (ht : Γ ⊢[PRAAx] continuity A mu d x)
    (hu : Γ ⊢[PRAAx] uniqueness A mu u d x) (hN : Γ ⊢[PRAAx] pointName b d z)
    (hC : Γ ⊢[PRAAx] cubePoints b d z) (hV : Γ ⊢[PRAAx] sameValue A mu b d x z) : Γ ⊢[PRAAx]
    equivalent (RationalCubeCoherentMinimizer.pointF A mu u) b d (data d x) z := by
  refine .allI (.allI ?_)
  have c : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] coherence A (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,RationalCubeMinimum.subst_coherence,Syn.shift] using hc.shift.shift
  have tt : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] continuity A mu (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,RationalCubeMinimum.subst_continuity,Syn.shift] using ht.shift.shift
  have uu : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] uniqueness A mu u (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,RationalCubeCoherentMinimizer.subst_uniqueness,Syn.shift] using hu.shift.shift
  have nn : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] pointName b (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift z)) := by
    simpa only [Fm.shift,RationalCubeCoherentMinimizer.subst_pointName,Syn.shift] using hN.shift.shift
  have cc : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] cubePoints b (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift z)) := by
    simpa only [Fm.shift,RationalCubeInfimumComparison.subst_cubePoints,Syn.shift] using hC.shift.shift
  have vv : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] sameValue A mu b (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift z)) := by
    simpa only [Fm.shift,subst_sameValue,Syn.shift] using hV.shift.shift
  simpa only [Syn.shift,RationalCubeInfimumName.subst_data] using unique_name_radius A mu u b
    (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift z)) (var 1) (var 0) c tt uu nn cc vv

theorem selected_evaluation_at (A : PR 3) (mu u : PR 2) (d p x : PTm n) : Γ ⊢[PRAAx]
    evaluation A mu (RationalCubeCoherentMinimizer.pointF A mu u) p x (data d x) ≐ RationalCubeCoherentMinimizer.evaluation A mu u d p x :=
  congrAp3 A (RationalCubeCoherentMinimizer.point_at A mu u d (evaluationIndex mu p x) x) (.eqRefl _) (.eqRefl _)

theorem selected_same_value_at (A : PR 3) (mu u : PR 2) (d p x : PTm n) (hc : Γ ⊢[PRAAx] coherence A d x)
    (ht : Γ ⊢[PRAAx] continuity A mu d x) : Γ ⊢[PRAAx]
    RationalValueBounds.radius (evaluation A mu (RationalCubeCoherentMinimizer.pointF A mu u) p x (data d x)) (value A mu d p x) two (scale p) := by
  have h := RationalValueBounds.radius_congr (selected_evaluation_at A mu u d p x).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (RationalCubeCoherentMinimizer.evaluation_value A mu u d p p x hc ht)
  apply RationalValueBounds.radius_mono _ _ _ _ _ _
    (RationalAlgebra.positive_product (RationalAlgebra.positive_product
      (le_of_eq_add (d := one) (by ipra_ring)) (RationalCubeGrid.scale_positive p)) (RationalCubeGrid.scale_positive p)) h
  exact le_of_eq_add (d := scale p*scale p) (by ipra_ring)

theorem source_same_value (A : PR 3) (mu u : PR 2) (d x : PTm n) (hc : Γ ⊢[PRAAx] coherence A d x)
    (ht : Γ ⊢[PRAAx] continuity A mu d x) : Γ ⊢[PRAAx]
    sameValue A mu (RationalCubeCoherentMinimizer.pointF A mu u) d x (data d x) := by
  refine .allI ?_
  have c : Γ.map Fm.shift ⊢[PRAAx] coherence A (Syn.shift d) (Syn.shift x) := by
    simpa only [Fm.shift,RationalCubeMinimum.subst_coherence,Syn.shift] using hc.shift
  have t : Γ.map Fm.shift ⊢[PRAAx] continuity A mu (Syn.shift d) (Syn.shift x) := by
    simpa only [Fm.shift,RationalCubeMinimum.subst_continuity,Syn.shift] using ht.shift
  simpa only [Syn.shift,RationalCubeInfimumName.subst_data] using selected_same_value_at A mu u (Syn.shift d) (var 0) (Syn.shift x) c t

theorem source_cube_points (A : PR 3) (mu u : PR 2) (d x : PTm n) : Γ ⊢[PRAAx]
    cubePoints (RationalCubeCoherentMinimizer.pointF A mu u) d (data d x) := by
  refine .allI ?_
  have eq := RationalCubeCoherentMinimizer.point_at (Γ := Γ.map Fm.shift) A mu u (Syn.shift d) (var 0) (Syn.shift x)
  have proof := Prf.eqSubst (Γ := Γ.map Fm.shift) (presentedCube (var 0) (var 1) : Fm PTm 2)
    ![point A mu u (Syn.shift d) (var 0) (Syn.shift x),Syn.shift d]
    ![ap2 (RationalCubeCoherentMinimizer.pointF A mu u) (var 0) (data (Syn.shift d) (Syn.shift x)),Syn.shift d]
    (fun i => by fin_cases i; exact eq.eqSymm; exact .eqRefl _)
    (by simpa using RationalCubeCoherentMinimizer.point_presented (Γ := Γ.map Fm.shift) A mu u (Syn.shift d) (var 0) (Syn.shift x))
  simpa [Syn.shift,RationalCubeInfimumName.subst_data] using proof

/-- The actual constructed program meets all point-name/domain/value
properties; none of these generated laws is a premise. -/
theorem source_minimizer (A : PR 3) (mu u : PR 2) (d x : PTm n) (hc : Γ ⊢[PRAAx] coherence A d x)
    (ht : Γ ⊢[PRAAx] continuity A mu d x) (hu : Γ ⊢[PRAAx] uniqueness A mu u d x) : Γ ⊢[PRAAx]
    pointName (RationalCubeCoherentMinimizer.pointF A mu u) d (data d x) ⋏
      cubePoints (RationalCubeCoherentMinimizer.pointF A mu u) d (data d x) ⋏
        sameValue A mu (RationalCubeCoherentMinimizer.pointF A mu u) d x (data d x) :=
  .andI (RationalCubeCoherentMinimizer.point_fast A mu u d x hc ht hu)
    (.andI (source_cube_points A mu u d x) (source_same_value A mu u d x hc ht))

theorem unique_diagonal (A : PR 3) (mu u b : PR 2) (d x z q : PTm n)
    (hc : Γ ⊢[PRAAx] coherence A d x) (ht : Γ ⊢[PRAAx] continuity A mu d x)
    (hu : Γ ⊢[PRAAx] uniqueness A mu u d x) (hN : Γ ⊢[PRAAx] pointName b d z)
    (hC : Γ ⊢[PRAAx] cubePoints b d z) (hV : Γ ⊢[PRAAx] sameValue A mu b d x z) : Γ ⊢[PRAAx]
    pointRadius (ap2 (RationalCubeCoherentMinimizer.pointF A mu u) q (data d x)) (ap2 b q z) d two (scale q) :=
  AggregateChain.point_mono _ _ _ _ _ _ _
    (RationalAlgebra.positive_product (RationalCubeGrid.scale_positive q) (RationalCubeGrid.scale_positive q))
    (unique_name_radius A mu u b d x z q q hc ht hu hN hC hV) (le_of_eq_add (d := zero) (by ipra_ring))

def evaluationF (A : PR 3) (mu b : PR 2) : PR 3 := PTm.toPR (evaluation A mu b (var 0) (var 1) (var 2))
def evaluateName (A : PR 3) (mu b : PR 2) (p x z : PTm n) : PTm n := app (evaluationF A mu b) ![p,x,z]
def tailF (mu u : PR 2) : PR 2 := PTm.toPR (tailIndex mu u (var 0) (var 1))
def runTail (mu u : PR 2) (k x : PTm n) : PTm n := ap2 (tailF mu u) k x

theorem evaluation_program_at (A : PR 3) (mu b : PR 2) (p x z : PTm n) : Γ ⊢[PRAAx]
    evaluateName A mu b p x z ≐ evaluation A mu b p x z := by
  simpa [evaluateName,evaluationF,Matrix.cons_val_succ',Matrix.cons_val_zero'] using
    toPR_eq (Γ := Γ) (evaluation A mu b (var 0) (var 1) (var 2) : PTm 3) ![p,x,z]
theorem tail_program_at (mu u : PR 2) (k x : PTm n) : Γ ⊢[PRAAx] runTail mu u k x ≐ tailIndex mu u k x := by
  simpa [ap2,runTail,tailF,Matrix.cons_val_succ',Matrix.cons_val_zero'] using
    toPR_eq (Γ := Γ) (tailIndex mu u (var 0) (var 1) : PTm 2) ![k,x]

theorem actual_point_name_tail_radius_closed (b : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (pointName b (var 0) (var 1) ⟶ le (succ (var 2)) (var 3) ⟶ le (succ (var 2)) (var 4) ⟶
      pointRadius (ap2 b (var 3) (var 1)) (ap2 b (var 4) (var 1)) (var 0) one (scale (var 2))) :=
  closeUniv 5 (.impI (.impI (.impI (point_tail_radius b (var 0) (var 1) (var 2) (var 3) (var 4) Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_same_value_approximant_near_closed (A : PR 3) (mu b : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (coherence A (var 0) (var 1) ⟶ continuity A mu (var 0) (var 1) ⟶ pointName b (var 0) (var 2) ⟶
      cubePoints b (var 0) (var 2) ⟶ sameValue A mu b (var 0) (var 1) (var 2) ⟶
        le (succ (ap2 mu (succ (var 3)) (var 1))) (var 4) ⟶ near A mu (var 0) (var 1) (ap2 b (var 4) (var 2)) (var 3)) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (.impI (.impI (approximant_near A mu b (var 0) (var 1) (var 2) (var 3) (var 4)
    (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)))))))))
theorem actual_source_constructed_minimizer_closed (A : PR 3) (mu u : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (coherence A (var 0) (var 1) ⟶ continuity A mu (var 0) (var 1) ⟶ uniqueness A mu u (var 0) (var 1) ⟶
      pointName (RationalCubeCoherentMinimizer.pointF A mu u) (var 0) (data (var 0) (var 1)) ⋏
        cubePoints (RationalCubeCoherentMinimizer.pointF A mu u) (var 0) (data (var 0) (var 1)) ⋏
          sameValue A mu (RationalCubeCoherentMinimizer.pointF A mu u) (var 0) (var 1) (data (var 0) (var 1))) :=
  closeUniv 2 (.impI (.impI (.impI (source_minimizer A mu u (var 0) (var 1) Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_source_minimizer_unique_point_name_closed (A : PR 3) (mu u b : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (coherence A (var 0) (var 1) ⟶ continuity A mu (var 0) (var 1) ⟶ uniqueness A mu u (var 0) (var 1) ⟶
      pointName b (var 0) (var 2) ⟶ cubePoints b (var 0) (var 2) ⟶ sameValue A mu b (var 0) (var 1) (var 2) ⟶
        equivalent (RationalCubeCoherentMinimizer.pointF A mu u) b (var 0) (data (var 0) (var 1)) (var 2)) :=
  closeUniv 3 (.impI (.impI (.impI (.impI (.impI (.impI (unique_name A mu u b (var 0) (var 1) (var 2)
    (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)))))))))
theorem actual_source_minimizer_unique_diagonal_closed (A : PR 3) (mu u b : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (coherence A (var 0) (var 1) ⟶ continuity A mu (var 0) (var 1) ⟶ uniqueness A mu u (var 0) (var 1) ⟶
      pointName b (var 0) (var 2) ⟶ cubePoints b (var 0) (var 2) ⟶ sameValue A mu b (var 0) (var 1) (var 2) ⟶
        pointRadius (ap2 (RationalCubeCoherentMinimizer.pointF A mu u) (var 3) (data (var 0) (var 1))) (ap2 b (var 3) (var 2)) (var 0) two (scale (var 3))) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (.impI (.impI (unique_diagonal A mu u b (var 0) (var 1) (var 2) (var 3)
    (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)))))))))
theorem actual_competing_point_evaluation_program_closed (A : PR 3) (mu b : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (evaluateName A mu b (var 0) (var 1) (var 2) ≐ sample A (ap2 b (evaluationIndex mu (var 0) (var 1)) (var 2)) (precision (var 0)) (var 1)) :=
  closeUniv 3 (evaluation_program_at A mu b (var 0) (var 1) (var 2))
theorem actual_finite_comparison_tail_program_closed (mu u : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (runTail mu u (var 0) (var 1) ≐ tailIndex mu u (var 0) (var 1)) := closeUniv 2 (tail_program_at mu u (var 0) (var 1))

end LeanProofs.IPRA.Analysis.RationalCubeMinimizerUniqueness

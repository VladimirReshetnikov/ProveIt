import IPRADerivations.Analysis.RationalCubeStrongConvexity
import IPRADerivations.Analysis.RationalCubeMinimizerUniqueness
import IPRADerivations.Core.LinearCombination

/-!
# The source's literal strongly convex minimizer a_(2k+c)

The numerical cutoff is a data parameter. The actual point producer uses
2k+c directly, rather than the general running-majorant schedule. Original
midpoint-drop and positive coefficient data supply its uniqueness law.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalCubeStrongMinimizer

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open RationalCubeMinimum (coherence continuity presentedCube sample precision minimizer)
open RationalCubeGrid (scale)
open RationalCubeStrongConvexity (linearIndex linearUniqueness midpointDrop cutoff)
open RationalCubeCoherentMinimizer (near evaluationIndex pointName)
open RationalCubeInfimumName (value)
open RationalCubeInfimumComparison (cubePoints)
open RationalCubeMinimizerUniqueness (sameValue)
open RationalHausdorff (pointRadius)
open LeanProofs.IPRA.Probability.Ninther (mn)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ app)
open LeanProofs.IPRA.PTm (monus num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def point (A : PR 3) (mu : PR 2) (d c k x : PTm n) : PTm n := minimizer A mu d (linearIndex k c) x
def data (d c x : PTm n) : PTm n := pairT d (pairT c x)
def evaluation (A : PR 3) (mu : PR 2) (d c p x : PTm n) : PTm n := sample A (point A mu d c (evaluationIndex mu p x) x) (precision p) x
@[simp] theorem subst_point {j : ℕ} (σ : Fin n → PTm j) (A : PR 3) (mu : PR 2) (d c k x : PTm n) :
    Syn.subst σ (point A mu d c k x) = point A mu (Syn.subst σ d) (Syn.subst σ c) (Syn.subst σ k) (Syn.subst σ x) := by simp [point]
@[simp] theorem subst_data {j : ℕ} (σ : Fin n → PTm j) (d c x : PTm n) :
    Syn.subst σ (data d c x) = data (Syn.subst σ d) (Syn.subst σ c) (Syn.subst σ x) := by simp [data]
@[simp] theorem subst_evaluation {j : ℕ} (σ : Fin n → PTm j) (A : PR 3) (mu : PR 2) (d c p x : PTm n) :
    Syn.subst σ (evaluation A mu d c p x) = evaluation A mu (Syn.subst σ d) (Syn.subst σ c) (Syn.subst σ p) (Syn.subst σ x) := by simp [evaluation]

theorem linear_index_ge (k c : PTm n) : Γ ⊢[PRAAx] le k (linearIndex k c) := le_of_eq_add (d := k+c) (by unfold linearIndex; ipra_ring)
theorem linear_index_mono (k l c : PTm n) (h : Γ ⊢[PRAAx] le k l) : Γ ⊢[PRAAx] le (linearIndex k c) (linearIndex l c) :=
  add_le_add₂ (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl two) h) (le_refl c)

theorem linear_unique_at (A : PR 3) (mu : PR 2) (d x c k y z : PTm n) (h : Γ ⊢[PRAAx] linearUniqueness A mu d x c)
    (hy : Γ ⊢[PRAAx] presentedCube y d) (hz : Γ ⊢[PRAAx] presentedCube z d)
    (hn : Γ ⊢[PRAAx] near A mu d x y (linearIndex k c)) (hm : Γ ⊢[PRAAx] near A mu d x z (linearIndex k c)) : Γ ⊢[PRAAx]
    pointRadius y z d one (scale k) := by
  have law : Γ ⊢[PRAAx] presentedCube y d ⟶ presentedCube z d ⟶ near A mu d x y (linearIndex k c) ⟶
      near A mu d x z (linearIndex k c) ⟶ pointRadius y z d one (scale k) := by
    simpa [linearUniqueness,Syn.subst_shift,Syn.shift_subst,Syn.shift,Syn.subst_subst,Function.comp_def] using ((h.allE k).allE y).allE z
  exact .impE (.impE (.impE (.impE law hy) hz) hn) hm

theorem point_presented (A : PR 3) (mu : PR 2) (d c k x : PTm n) : Γ ⊢[PRAAx] presentedCube (point A mu d c k x) d := RationalCubeMinimum.minimizer_presented _ _ _ _ _

theorem point_later (A : PR 3) (mu : PR 2) (d c k l x : PTm n) (hc : Γ ⊢[PRAAx] coherence A d x)
    (ht : Γ ⊢[PRAAx] continuity A mu d x) (hu : Γ ⊢[PRAAx] linearUniqueness A mu d x c) (hkl : Γ ⊢[PRAAx] le k l) : Γ ⊢[PRAAx]
    pointRadius (point A mu d c k x) (point A mu d c l x) d one (scale k) :=
  linear_unique_at A mu d x c k _ _ hu (point_presented _ _ _ _ _ _) (point_presented _ _ _ _ _ _)
    (RationalCubeCoherentMinimizer.selected_near A mu d _ _ x hc ht (le_refl _))
    (RationalCubeCoherentMinimizer.selected_near A mu d _ _ x hc ht (linear_index_mono k l c hkl))

theorem point_strong (A : PR 3) (mu : PR 2) (d c k l x : PTm n) (hc : Γ ⊢[PRAAx] coherence A d x)
    (ht : Γ ⊢[PRAAx] continuity A mu d x) (hu : Γ ⊢[PRAAx] linearUniqueness A mu d x c) : Γ ⊢[PRAAx]
    pointRadius (point A mu d c k x) (point A mu d c l x) d one (scale (mn k l)) :=
  linear_unique_at A mu d x c (mn k l) _ _ hu (point_presented _ _ _ _ _ _) (point_presented _ _ _ _ _ _)
    (RationalCubeCoherentMinimizer.selected_near A mu d _ _ x hc ht (linear_index_mono _ _ c (Foundations.CoherentMinimizer.mn_le_left k l)))
    (RationalCubeCoherentMinimizer.selected_near A mu d _ _ x hc ht (linear_index_mono _ _ c (Foundations.CoherentMinimizer.mn_le_right k l)))

theorem point_regular (A : PR 3) (mu : PR 2) (d c k l x : PTm n) (hc : Γ ⊢[PRAAx] coherence A d x)
    (ht : Γ ⊢[PRAAx] continuity A mu d x) (hu : Γ ⊢[PRAAx] linearUniqueness A mu d x c) : Γ ⊢[PRAAx]
    pointRadius (point A mu d c k x) (point A mu d c l x) d (scale k+scale l) (scale k*scale l) :=
  AggregateChain.point_mono _ _ _ _ _ _ _ (RationalCubeGrid.scale_positive _) (point_strong A mu d c k l x hc ht hu)
    (le_congr (one_mul _).eqSymm (.eqRefl _) (Foundations.CoherentMinimizer.pw_min k l))

theorem evaluation_distance (A : PR 3) (mu : PR 2) (d c p q x : PTm n) (hc : Γ ⊢[PRAAx] coherence A d x)
    (ht : Γ ⊢[PRAAx] continuity A mu d x) (hu : Γ ⊢[PRAAx] linearUniqueness A mu d x c) (hpq : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx]
    pointRadius (point A mu d c (evaluationIndex mu p x) x) (point A mu d c (evaluationIndex mu q x) x) d one (scale (ap2 mu (precision p) x)) :=
  AggregateChain.point_mono _ _ _ _ _ _ _ (RationalCubeGrid.scale_positive _)
    (point_later A mu d c _ _ x hc ht hu (RationalCubeCoherentMinimizer.evaluation_index_mono mu p q x hpq))
    (le_congr (one_mul _).eqSymm (one_mul _).eqSymm
      (AnalyticNumberTheory.PowerCleared.pw_le_exp Foundations.CoherentMinimizer.two_pos (RationalCubeCoherentMinimizer.evaluation_index_modulus mu p x)))

theorem evaluation_regular_later (A : PR 3) (mu : PR 2) (d c p q x : PTm n) (hc : Γ ⊢[PRAAx] coherence A d x)
    (ht : Γ ⊢[PRAAx] continuity A mu d x) (hu : Γ ⊢[PRAAx] linearUniqueness A mu d x c) (hpq : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx]
    RationalValueBounds.radius (evaluation A mu d c p x) (evaluation A mu d c q x) (scale p+scale q) (scale p*scale q) := by
  have h := RationalCubeMinimum.continuity_at A mu d x _ _ (precision p) (precision p) (precision q) ht
    (point_presented _ _ _ _ _ _) (point_presented _ _ _ _ _ _) (evaluation_distance A mu d c p q x hc ht hu hpq)
  apply RationalValueBounds.radius_mono _ _ _ _ _ _ (RationalCubeMinimum.error_denominator_positive _ _ _) h
  refine le_of_eq_add (d := ((two*two)*(two*two))*scale p*scale p*scale q*((succ two)*scale p+two*scale q)) ?_
  apply deriveNat
  simp only [RationalCubeMinimum.errorNumerator,RationalCubeMinimum.errorDenominator]
  ipra_simps
  rw [natEq (RationalCubeCoherentMinimizer.scale_precision_exact (Γ := Γ) p),natEq (RationalCubeCoherentMinimizer.scale_precision_exact (Γ := Γ) q)]
  ipra_simps
  ring

theorem evaluation_regular (A : PR 3) (mu : PR 2) (d c p q x : PTm n) (hc : Γ ⊢[PRAAx] coherence A d x)
    (ht : Γ ⊢[PRAAx] continuity A mu d x) (hu : Γ ⊢[PRAAx] linearUniqueness A mu d x c) : Γ ⊢[PRAAx]
    RationalValueBounds.radius (evaluation A mu d c p x) (evaluation A mu d c q x) (scale p+scale q) (scale p*scale q) := by
  refine .orE (le_total p q) (evaluation_regular_later A mu d c p q x hc.wk ht.wk hu.wk Prf.hyp0) ?_
  exact RationalValueBounds.radius_congr (.eqRefl _) (.eqRefl _) (add_comm _ _) (mul_comm _ _)
    (RationalValueBounds.radius_symmetric _ _ _ _ (evaluation_regular_later A mu d c q p x hc.wk ht.wk hu.wk Prf.hyp0))

theorem evaluation_value (A : PR 3) (mu : PR 2) (d c p q x : PTm n) (hc : Γ ⊢[PRAAx] coherence A d x)
    (ht : Γ ⊢[PRAAx] continuity A mu d x) : Γ ⊢[PRAAx]
    RationalValueBounds.radius (evaluation A mu d c p x) (value A mu d q x) (scale q+two*scale p) (two*scale p*scale q) := by
  let f := two*scale (precision p)
  have h := RationalCubeCoherentMinimizer.selected_near_at A mu d (linearIndex (evaluationIndex mu p x) c) (precision p) x (precision p) q hc ht
    (le_trans (RationalCubeCoherentMinimizer.evaluation_index_ge mu p x) (linear_index_ge _ _))
  have upper : Γ ⊢[PRAAx] RationalValueBounds.upper (evaluation A mu d c p x) (value A mu d q x)
      (scale q+two*scale p) (two*scale p*scale q) := by
    apply RationalValueBounds.upper_cancel _ _ _ _ f
      (RationalAlgebra.positive_product (le_of_eq_add (d := one) (by ipra_ring)) (RationalCubeGrid.scale_positive _))
    apply RationalValueBounds.upper_congr (.eqRefl _) (.eqRefl _) _ _ h
    · apply deriveNat
      dsimp [f]
      ipra_simps
      rw [natEq (RationalCubeCoherentMinimizer.scale_precision_exact (Γ := Γ) p)]
      ipra_simps
      ring
    · apply deriveNat
      dsimp [f]
      ipra_simps
      rw [natEq (RationalCubeCoherentMinimizer.scale_precision_exact (Γ := Γ) p)]
      ipra_simps
      ring
  have lower : Γ ⊢[PRAAx] RationalValueBounds.upper (value A mu d q x) (evaluation A mu d c p x)
      (scale q+two*scale p) (two*scale p*scale q) := by
    apply RationalValueBounds.upper_mono _ _ _ _ _ _
      (RationalAlgebra.positive_product (RationalCubeGrid.scale_positive q) (RationalCubeGrid.scale_positive (precision p)))
      (RationalCubeInfimumName.value_lower_bound A mu d q x _ (precision p) hc ht (point_presented _ _ _ _ _ _))
    refine le_of_eq_add (d := two*scale p*scale q*scale q) ?_
    apply deriveNat
    ipra_simps
    rw [natEq (RationalCubeCoherentMinimizer.scale_precision_exact (Γ := Γ) p)]
    ipra_simps
    ring
  exact RationalValueBounds.radius_of_upper _ _ _ _ upper lower

def pointBody (A : PR 3) (mu : PR 2) : PTm 2 := point A mu (fstT (var 1)) (fstT (sndT (var 1))) (var 0) (sndT (sndT (var 1)))
def pointF (A : PR 3) (mu : PR 2) : PR 2 := PTm.toPR (pointBody A mu)
def evaluationBody (A : PR 3) (mu : PR 2) : PTm 2 := evaluation A mu (fstT (var 1)) (fstT (sndT (var 1))) (var 0) (sndT (sndT (var 1)))
def evaluationF (A : PR 3) (mu : PR 2) : PR 2 := PTm.toPR (evaluationBody A mu)

theorem data_fields (d c x : PTm n) : Γ ⊢[PRAAx] fstT (data d c x) ≐ d ⋏
    fstT (sndT (data d c x)) ≐ c ⋏ sndT (sndT (data d c x)) ≐ x :=
  .andI (fst_pair _ _) (.andI ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)) ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)))
theorem point_at (A : PR 3) (mu : PR 2) (d c k x : PTm n) : Γ ⊢[PRAAx] ap2 (pointF A mu) k (data d c x) ≐ point A mu d c k x := by
  have e := toPR_eq (Γ := Γ) (pointBody A mu) ![k,data d c x]
  have f := data_fields (Γ := Γ) d c x
  have q := Prf.eqCongr (Γ := Γ) (point A mu (var 0) (var 1) (var 2) (var 3) : PTm 4)
    (σ := ![fstT (data d c x),fstT (sndT (data d c x)),k,sndT (sndT (data d c x))]) (σ' := ![d,c,k,x])
    (fun i => by fin_cases i; exact .andE₁ f; exact .andE₁ (.andE₂ f); exact .eqRefl _; exact .andE₂ (.andE₂ f))
  exact e.eqTrans (by simpa [pointBody,Matrix.cons_val_succ',Matrix.cons_val_zero'] using q)
theorem evaluation_at (A : PR 3) (mu : PR 2) (d c p x : PTm n) : Γ ⊢[PRAAx] ap2 (evaluationF A mu) p (data d c x) ≐ evaluation A mu d c p x := by
  have e := toPR_eq (Γ := Γ) (evaluationBody A mu) ![p,data d c x]
  have f := data_fields (Γ := Γ) d c x
  have q := Prf.eqCongr (Γ := Γ) (evaluation A mu (var 0) (var 1) (var 2) (var 3) : PTm 4)
    (σ := ![fstT (data d c x),fstT (sndT (data d c x)),p,sndT (sndT (data d c x))]) (σ' := ![d,c,p,x])
    (fun i => by fin_cases i; exact .andE₁ f; exact .andE₁ (.andE₂ f); exact .eqRefl _; exact .andE₂ (.andE₂ f))
  exact e.eqTrans (by simpa [evaluationBody,Matrix.cons_val_succ',Matrix.cons_val_zero'] using q)

theorem point_name_radius (A : PR 3) (mu : PR 2) (d c k l x : PTm n) (hc : Γ ⊢[PRAAx] coherence A d x)
    (ht : Γ ⊢[PRAAx] continuity A mu d x) (hu : Γ ⊢[PRAAx] linearUniqueness A mu d x c) : Γ ⊢[PRAAx]
    pointRadius (ap2 (pointF A mu) k (data d c x)) (ap2 (pointF A mu) l (data d c x)) d (scale k+scale l) (scale k*scale l) :=
  RationalHausdorffConcat.pointRadius_congr (point_at A mu d c k x).eqSymm (point_at A mu d c l x).eqSymm (point_regular A mu d c k l x hc ht hu)

theorem point_fast (A : PR 3) (mu : PR 2) (d c x : PTm n) (hc : Γ ⊢[PRAAx] coherence A d x)
    (ht : Γ ⊢[PRAAx] continuity A mu d x) (hu : Γ ⊢[PRAAx] linearUniqueness A mu d x c) : Γ ⊢[PRAAx] pointName (pointF A mu) d (data d c x) := by
  refine .allI (.allI ?_)
  have co : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] coherence A (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,RationalCubeMinimum.subst_coherence,Syn.shift] using hc.shift.shift
  have ct : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] continuity A mu (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,RationalCubeMinimum.subst_continuity,Syn.shift] using ht.shift.shift
  have uu : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] linearUniqueness A mu (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift c)) := by
    simpa only [Fm.shift,RationalCubeStrongConvexity.subst_linearUniqueness,Syn.shift] using hu.shift.shift
  simpa only [Syn.shift,subst_data] using point_name_radius A mu (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift c)) (var 1) (var 0) (Syn.shift (Syn.shift x)) co ct uu

theorem evaluation_fast (A : PR 3) (mu : PR 2) (d c x : PTm n) (hc : Γ ⊢[PRAAx] coherence A d x)
    (ht : Γ ⊢[PRAAx] continuity A mu d x) (hu : Γ ⊢[PRAAx] linearUniqueness A mu d x c) : Γ ⊢[PRAAx]
    RationalCubeInfimumName.regular (evaluationF A mu) (data d c x) := by
  refine .allI (.allI ?_)
  have co : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] coherence A (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,RationalCubeMinimum.subst_coherence,Syn.shift] using hc.shift.shift
  have ct : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] continuity A mu (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,RationalCubeMinimum.subst_continuity,Syn.shift] using ht.shift.shift
  have uu : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] linearUniqueness A mu (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift c)) := by
    simpa only [Fm.shift,RationalCubeStrongConvexity.subst_linearUniqueness,Syn.shift] using hu.shift.shift
  simpa only [Syn.shift,subst_data] using RationalValueBounds.radius_congr
    (evaluation_at A mu (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift c)) (var 1) (Syn.shift (Syn.shift x))).eqSymm
    (evaluation_at A mu (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift c)) (var 0) (Syn.shift (Syn.shift x))).eqSymm (.eqRefl _) (.eqRefl _)
    (evaluation_regular A mu (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift c)) (var 1) (var 0) (Syn.shift (Syn.shift x)) co ct uu)

theorem source_cube_points (A : PR 3) (mu : PR 2) (d c x : PTm n) : Γ ⊢[PRAAx] cubePoints (pointF A mu) d (data d c x) := by
  refine .allI ?_
  have eq := point_at (Γ := Γ.map Fm.shift) A mu (Syn.shift d) (Syn.shift c) (var 0) (Syn.shift x)
  have proof := Prf.eqSubst (Γ := Γ.map Fm.shift) (presentedCube (var 0) (var 1) : Fm PTm 2)
    ![point A mu (Syn.shift d) (Syn.shift c) (var 0) (Syn.shift x),Syn.shift d]
    ![ap2 (pointF A mu) (var 0) (data (Syn.shift d) (Syn.shift c) (Syn.shift x)),Syn.shift d]
    (fun i => by fin_cases i; exact eq.eqSymm; exact .eqRefl _)
    (by simpa using point_presented (Γ := Γ.map Fm.shift) A mu (Syn.shift d) (Syn.shift c) (var 0) (Syn.shift x))
  simpa [Syn.shift,subst_data] using proof

theorem selected_evaluation_at (A : PR 3) (mu : PR 2) (d c p x : PTm n) : Γ ⊢[PRAAx]
    RationalCubeMinimizerUniqueness.evaluation A mu (pointF A mu) p x (data d c x) ≐ evaluation A mu d c p x :=
  congrAp3 A (point_at A mu d c (evaluationIndex mu p x) x) (.eqRefl _) (.eqRefl _)

theorem source_same_value (A : PR 3) (mu : PR 2) (d c x : PTm n) (hc : Γ ⊢[PRAAx] coherence A d x)
    (ht : Γ ⊢[PRAAx] continuity A mu d x) : Γ ⊢[PRAAx] sameValue A mu (pointF A mu) d x (data d c x) := by
  refine .allI ?_
  have co : Γ.map Fm.shift ⊢[PRAAx] coherence A (Syn.shift d) (Syn.shift x) := by
    simpa only [Fm.shift,RationalCubeMinimum.subst_coherence,Syn.shift] using hc.shift
  have ct : Γ.map Fm.shift ⊢[PRAAx] continuity A mu (Syn.shift d) (Syn.shift x) := by
    simpa only [Fm.shift,RationalCubeMinimum.subst_continuity,Syn.shift] using ht.shift
  let D := Syn.shift d
  let C := Syn.shift c
  let X := Syn.shift x
  have h := RationalValueBounds.radius_congr (selected_evaluation_at A mu D C (var 0) X).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (evaluation_value A mu D C (var 0) (var 0) X co ct)
  have result : Γ.map Fm.shift ⊢[PRAAx] RationalValueBounds.radius
      (RationalCubeMinimizerUniqueness.evaluation A mu (pointF A mu) (var 0) X (data D C X)) (value A mu D (var 0) X) two (scale (var 0)) := by
    apply RationalValueBounds.radius_mono _ _ _ _ _ _
      (RationalAlgebra.positive_product (RationalAlgebra.positive_product
        (le_of_eq_add (d := one) (by ipra_ring)) (RationalCubeGrid.scale_positive _)) (RationalCubeGrid.scale_positive _)) h
    exact le_of_eq_add (d := scale (var 0)*scale (var 0)) (by ipra_ring)
  simpa only [D,C,X,Syn.shift,subst_data] using result

/-- Only actual finite tails are compared before removing their explicit slack. -/
theorem approximate_cross_radius (A : PR 3) (mu b : PR 2) (d c x z q t k : PTm n)
    (hc : Γ ⊢[PRAAx] coherence A d x) (ht : Γ ⊢[PRAAx] continuity A mu d x)
    (hu : Γ ⊢[PRAAx] linearUniqueness A mu d x c) (hN : Γ ⊢[PRAAx] pointName b d z)
    (hC : Γ ⊢[PRAAx] cubePoints b d z) (hV : Γ ⊢[PRAAx] sameValue A mu b d x z) : Γ ⊢[PRAAx]
    pointRadius (point A mu d c q x) (ap2 b t z) d
      ((scale q+scale t)*scale k+two*(scale q*scale t)) ((scale q*scale t)*scale k) := by
  let s := k+succ (ap2 mu (succ (linearIndex k c)) x)
  let l := q+k
  have ql : Γ ⊢[PRAAx] le q l := le_add_right _ _
  have kl : Γ ⊢[PRAAx] le k l := le_add_left _ _
  have first := point_later A mu d c q l x hc ht hu ql
  have middle := linear_unique_at A mu d x c k (point A mu d c l x) (ap2 b s z) hu
    (point_presented _ _ _ _ _ _) (RationalCubeInfimumComparison.cube_points_at b d z s hC)
    (RationalCubeCoherentMinimizer.selected_near A mu d _ _ x hc ht (linear_index_mono k l c kl))
    (RationalCubeMinimizerUniqueness.approximant_near A mu b d x z (linearIndex k c) s hc ht hN hC hV (le_add_left _ _))
  have last := RationalCubeMinimizerUniqueness.point_name_at b d z s t hN
  have combined := RationalHausdorffTriangle.pointRadius_triangle _ _ _ d _ _ _ _
    (RationalHausdorffTriangle.pointRadius_triangle _ _ _ d _ _ _ _ first middle) last
  have power : Γ ⊢[PRAAx] le (scale k) (scale s) :=
    AnalyticNumberTheory.PowerCleared.pw_le_exp Foundations.CoherentMinimizer.two_pos (le_add_right _ _)
  apply AggregateChain.point_mono _ _ _ _ _ _ _
    (RationalAlgebra.positive_product
      (RationalAlgebra.positive_product (RationalCubeGrid.scale_positive q) (RationalCubeGrid.scale_positive k))
      (RationalAlgebra.positive_product (RationalCubeGrid.scale_positive s) (RationalCubeGrid.scale_positive t))) combined
  refine le_of_eq_add (d := (scale q*scale t)*(scale q*scale t)*scale k*monus (scale s) (scale k)) ?_
  ipra_lc 𝔞(scale q)^2*𝔞(scale t)^2*𝔞(scale k)*natEq (eq_add_of_le power)

theorem unique_radius (A : PR 3) (mu b : PR 2) (d c x z q t : PTm n)
    (hc : Γ ⊢[PRAAx] coherence A d x) (ht : Γ ⊢[PRAAx] continuity A mu d x)
    (hu : Γ ⊢[PRAAx] linearUniqueness A mu d x c) (hN : Γ ⊢[PRAAx] pointName b d z)
    (hC : Γ ⊢[PRAAx] cubePoints b d z) (hV : Γ ⊢[PRAAx] sameValue A mu b d x z) : Γ ⊢[PRAAx]
    pointRadius (point A mu d c q x) (ap2 b t z) d (scale q+scale t) (scale q*scale t) := by
  let E := two*(scale q*scale t)
  let C := E*RationalPointDistanceVariation.pointDenominator (point A mu d c q x) (ap2 b t z) d
  apply AggregateApproximateLipschitz.remove_slack _ _ _ _ _ E
  exact approximate_cross_radius A mu b d c x z q t C hc ht hu hN hC hV

theorem source_minimizer (A : PR 3) (mu : PR 2) (L M d x c : PTm n)
    (hc : Γ ⊢[PRAAx] coherence A d x) (ht : Γ ⊢[PRAAx] continuity A mu d x)
    (hd : Γ ⊢[PRAAx] midpointDrop A L M d x) (hM : Γ ⊢[PRAAx] le one M)
    (hBudget : Γ ⊢[PRAAx] le (num 8*M) (L*scale c)) : Γ ⊢[PRAAx]
    pointName (pointF A mu) d (data d c x) ⋏ RationalCubeInfimumName.regular (evaluationF A mu) (data d c x) ⋏
      cubePoints (pointF A mu) d (data d c x) ⋏ sameValue A mu (pointF A mu) d x (data d c x) := by
  have hu := RationalCubeStrongConvexity.source_linear_uniqueness A mu L M d x c hc ht hd hM hBudget
  exact .andI (point_fast A mu d c x hc ht hu) (.andI (evaluation_fast A mu d c x hc ht hu)
    (.andI (source_cube_points A mu d c x) (source_same_value A mu d c x hc ht)))

theorem source_unique_radius (A : PR 3) (mu b : PR 2) (L M d x c z q t : PTm n)
    (hc : Γ ⊢[PRAAx] coherence A d x) (ht : Γ ⊢[PRAAx] continuity A mu d x)
    (hd : Γ ⊢[PRAAx] midpointDrop A L M d x) (hM : Γ ⊢[PRAAx] le one M)
    (hBudget : Γ ⊢[PRAAx] le (num 8*M) (L*scale c)) (hN : Γ ⊢[PRAAx] pointName b d z)
    (hC : Γ ⊢[PRAAx] cubePoints b d z) (hV : Γ ⊢[PRAAx] sameValue A mu b d x z) : Γ ⊢[PRAAx]
    pointRadius (ap2 (pointF A mu) q (data d c x)) (ap2 b t z) d (scale q+scale t) (scale q*scale t) :=
  RationalHausdorffConcat.pointRadius_congr (point_at A mu d c q x).eqSymm (.eqRefl _)
    (unique_radius A mu b d c x z q t hc ht
      (RationalCubeStrongConvexity.source_linear_uniqueness A mu L M d x c hc ht hd hM hBudget) hN hC hV)

theorem computed_source_minimizer (A : PR 3) (mu : PR 2) (L M d x : PTm n)
    (hc : Γ ⊢[PRAAx] coherence A d x) (ht : Γ ⊢[PRAAx] continuity A mu d x)
    (hd : Γ ⊢[PRAAx] midpointDrop A L M d x) (hL : Γ ⊢[PRAAx] le one L) (hM : Γ ⊢[PRAAx] le one M) : Γ ⊢[PRAAx]
    pointName (pointF A mu) d (data d (cutoff M) x) ⋏ RationalCubeInfimumName.regular (evaluationF A mu) (data d (cutoff M) x) ⋏
      cubePoints (pointF A mu) d (data d (cutoff M) x) ⋏ sameValue A mu (pointF A mu) d x (data d (cutoff M) x) :=
  source_minimizer A mu L M d x (cutoff M) hc ht hd hM (RationalCubeStrongConvexity.cutoff_budget L M hL)

theorem computed_source_unique_radius (A : PR 3) (mu b : PR 2) (L M d x z q t : PTm n)
    (hc : Γ ⊢[PRAAx] coherence A d x) (ht : Γ ⊢[PRAAx] continuity A mu d x)
    (hd : Γ ⊢[PRAAx] midpointDrop A L M d x) (hL : Γ ⊢[PRAAx] le one L) (hM : Γ ⊢[PRAAx] le one M)
    (hN : Γ ⊢[PRAAx] pointName b d z) (hC : Γ ⊢[PRAAx] cubePoints b d z) (hV : Γ ⊢[PRAAx] sameValue A mu b d x z) : Γ ⊢[PRAAx]
    pointRadius (ap2 (pointF A mu) q (data d (cutoff M) x)) (ap2 b t z) d (scale q+scale t) (scale q*scale t) :=
  source_unique_radius A mu b L M d x (cutoff M) z q t hc ht hd hM (RationalCubeStrongConvexity.cutoff_budget L M hL) hN hC hV

def computedF (A : PR 3) (mu : PR 2) : PR 4 := PTm.toPR (point A mu (var 1) (cutoff (var 0)) (var 2) (var 3))
def run (A : PR 3) (mu : PR 2) (M d k x : PTm n) : PTm n := app (computedF A mu) ![M,d,k,x]
@[simp] theorem subst_run {j : ℕ} (σ : Fin n → PTm j) (A : PR 3) (mu : PR 2) (M d k x : PTm n) :
    Syn.subst σ (run A mu M d k x) = run A mu (Syn.subst σ M) (Syn.subst σ d) (Syn.subst σ k) (Syn.subst σ x) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem computed_program_at (A : PR 3) (mu : PR 2) (M d k x : PTm n) : Γ ⊢[PRAAx]
    run A mu M d k x ≐ minimizer A mu d (two*k+num 8*M) x := by
  simpa [run,computedF,point,linearIndex,cutoff,Matrix.cons_val_succ',Matrix.cons_val_zero'] using
    toPR_eq (Γ := Γ) (point A mu (var 1) (cutoff (var 0)) (var 2) (var 3) : PTm 4) ![M,d,k,x]

theorem actual_literal_linear_minimizer_program_closed (A : PR 3) (mu : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (ap2 (pointF A mu) (var 2) (data (var 0) (var 1) (var 3)) ≐ minimizer A mu (var 0) (two*var 2+var 1) (var 3)) :=
  closeUniv 4 (point_at A mu (var 0) (var 1) (var 2) (var 3))
theorem actual_literal_linear_evaluation_program_closed (A : PR 3) (mu : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (ap2 (evaluationF A mu) (var 2) (data (var 0) (var 1) (var 3)) ≐ evaluation A mu (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (evaluation_at A mu (var 0) (var 1) (var 2) (var 3))
theorem actual_source_strongly_convex_minimizer_closed (A : PR 3) (mu : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (coherence A (var 2) (var 3) ⟶ continuity A mu (var 2) (var 3) ⟶ midpointDrop A (var 0) (var 1) (var 2) (var 3) ⟶
      le one (var 1) ⟶ le (num 8*var 1) (var 0*scale (var 4)) ⟶
      pointName (pointF A mu) (var 2) (data (var 2) (var 4) (var 3)) ⋏
        RationalCubeInfimumName.regular (evaluationF A mu) (data (var 2) (var 4) (var 3)) ⋏
        cubePoints (pointF A mu) (var 2) (data (var 2) (var 4) (var 3)) ⋏
        sameValue A mu (pointF A mu) (var 2) (var 3) (data (var 2) (var 4) (var 3))) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (.impI (source_minimizer A mu (var 0) (var 1) (var 2) (var 3) (var 4)
    (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp))))))))
theorem actual_source_strong_minimizer_uniqueness_closed (A : PR 3) (mu b : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (coherence A (var 2) (var 3) ⟶ continuity A mu (var 2) (var 3) ⟶ midpointDrop A (var 0) (var 1) (var 2) (var 3) ⟶
      le one (var 1) ⟶ le (num 8*var 1) (var 0*scale (var 4)) ⟶ pointName b (var 2) (var 5) ⟶
      cubePoints b (var 2) (var 5) ⟶ sameValue A mu b (var 2) (var 3) (var 5) ⟶
      pointRadius (ap2 (pointF A mu) (var 6) (data (var 2) (var 4) (var 3))) (ap2 b (var 7) (var 5)) (var 2)
        (scale (var 6)+scale (var 7)) (scale (var 6)*scale (var 7))) :=
  closeUniv 8 (.impI (.impI (.impI (.impI (.impI (.impI (.impI (.impI (source_unique_radius A mu b (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)
    (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)))))))))))
theorem actual_computed_source_strong_minimizer_closed (A : PR 3) (mu : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (coherence A (var 2) (var 3) ⟶ continuity A mu (var 2) (var 3) ⟶ midpointDrop A (var 0) (var 1) (var 2) (var 3) ⟶
      le one (var 0) ⟶ le one (var 1) ⟶
      pointName (pointF A mu) (var 2) (data (var 2) (cutoff (var 1)) (var 3)) ⋏
        RationalCubeInfimumName.regular (evaluationF A mu) (data (var 2) (cutoff (var 1)) (var 3)) ⋏
        cubePoints (pointF A mu) (var 2) (data (var 2) (cutoff (var 1)) (var 3)) ⋏
        sameValue A mu (pointF A mu) (var 2) (var 3) (data (var 2) (cutoff (var 1)) (var 3))) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (.impI (computed_source_minimizer A mu (var 0) (var 1) (var 2) (var 3)
    (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp))))))))
theorem actual_computed_source_strong_minimizer_program_closed (A : PR 3) (mu : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run A mu (var 0) (var 1) (var 2) (var 3) ≐ minimizer A mu (var 1) (two*var 2+num 8*var 0) (var 3)) :=
  closeUniv 4 (computed_program_at A mu (var 0) (var 1) (var 2) (var 3))

end LeanProofs.IPRA.Analysis.RationalCubeStrongMinimizer

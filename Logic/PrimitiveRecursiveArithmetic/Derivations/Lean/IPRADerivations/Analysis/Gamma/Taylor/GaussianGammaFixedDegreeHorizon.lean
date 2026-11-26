import IPRADerivations.Analysis.Gamma.Taylor.GaussianGammaFiniteDegreeRearrangement
import IPRADerivations.Core.CongruenceTactic

/-!
# Actual fixed-degree Gamma tails over cofinal factor horizons

The finite factor sum splits at an arbitrary internal horizon. Its
remaining segment has the original C6 bound at its actual later start,
uniformly in the fixed Taylor degree. The old computed factor-count
schedule therefore supplies genuine dyadic comparisons at fixed degree.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaFixedDegreeHorizon

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaCanonicalTailFiniteSplit (gaussianSum term)
open GaussianRationalHorner (qadd qzero)
open GaussianRationalSyntheticDivision (qadd_congr qsub_congr qadd_sub_cancel)
open GaussianRationalFiniteSum (sum_index_congr)
open GaussianRationalMetric (distanceBounded)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianGammaFiniteDegreeRearrangement (degreeMajor)
open GaussianGammaCanonicalTailName (source)
open GaussianRationalHorner (positive_product)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def splitLaw (z B N r L s : PTm n) : Fm PTm n := gaussianSum z B N (r+s) L ≐
  qadd (gaussianSum z B N r L) (gaussianSum z B (N+r) s L)
@[simp] theorem subst_splitLaw {m : ℕ} (σ : Fin n → PTm m) (z B N r L s : PTm n) :
    (splitLaw z B N r L s).subst σ = splitLaw (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N)
      (Syn.subst σ r) (Syn.subst σ L) (Syn.subst σ s) := by simp [splitLaw]
theorem split_zero (z B N r L : PTm n) : Γ ⊢[PRAAx] splitLaw z B N r L zero :=
  (GaussianRationalFiniteSum.sum_index_congr _ (add_zero r) (.eqRefl _)).eqTrans
    ((GaussianRationalLinearProduct.qadd_zero_right _ (GaussianRationalFiniteSum.sum_canonical _ _ _)).eqSymm.eqTrans
      (qadd_congr (.eqRefl _) (GaussianGammaCanonicalTailFiniteSplit.gaussian_sum_zero z B (N+r) L).eqSymm))
theorem split_step (z B N r L s : PTm n) (ih : Γ ⊢[PRAAx] splitLaw z B N r L s) :
    Γ ⊢[PRAAx] splitLaw z B N r L (succ s) := by
  have next := (GaussianRationalFiniteSum.sum_index_congr (Γ := Γ) _ (add_succ r s) (.eqRefl _)).eqTrans
    (GaussianGammaCanonicalTailFiniteSplit.gaussian_sum_succ z B N (r+s) L)
  have last := GaussianGammaCanonicalTailFiniteSplit.term_index_congr z B L (by ipra_ring : Γ ⊢[PRAAx] succ (N+(r+s)) ≐ succ ((N+r)+s))
  exact next.eqTrans ((qadd_congr ih last).eqTrans
    ((GaussianRationalSumAlgebra.qadd_associative _ _ _).eqTrans
      (qadd_congr (.eqRefl _) (GaussianGammaCanonicalTailFiniteSplit.gaussian_sum_succ z B (N+r) s L).eqSymm)))
theorem sum_split (z B N r s L : PTm n) : Γ ⊢[PRAAx] splitLaw z B N r L s := by
  have hall : Γ ⊢[PRAAx] .all (splitLaw (Syn.shift z) (Syn.shift B) (Syn.shift N) (Syn.shift r) (Syn.shift L) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simpa only [subst_splitLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using split_zero (Γ := Γ) z B N r L
    · simp only [subst_splitLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact split_step _ _ _ _ _ _ Prf.hyp0
  simpa only [subst_splitLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using hall.allE s

theorem original_sum_as_degree (z B N r L : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    gaussianSum z B N r L ≐ degreeMajor z B N r L :=
  (GaussianGammaCanonicalTailFiniteSplit.finite_value_as_sum z B N r L hB).eqSymm.eqTrans
    (GaussianGammaFiniteDegreeRearrangement.original_finite_rearrangement z B N r L hB)

theorem later_source (z R B N r : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] source z R B (N+r) := .andI h.andE₁
      (.andI (le_trans h.andE₂.andE₁ (le_add_right N r))
        (.andI h.andE₂.andE₂.andE₁ (le_trans h.andE₂.andE₂.andE₂ (le_add_right N r))))

theorem finite_horizon_distance (z R B N r s L : PTm n) (h : Γ ⊢[PRAAx] source z R B N) : Γ ⊢[PRAAx]
    distanceBounded (degreeMajor z B N (r+s) L) (degreeMajor z B N r L) (R*R) (N+r) := by
  have eq := (GaussianRationalSyntheticDivision.qsub_congr (sum_split (Γ := Γ) z B N r s L) (.eqRefl _)).eqTrans
    (qadd_sub_cancel _ _ (GaussianRationalFiniteSum.sum_canonical _ _ _))
  have tail := GaussianRationalReciprocal.bound_congr
    (original_sum_as_degree z B (N+r) s L h.andE₁).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianGammaFiniteDegreeRearrangement.uniform_rearranged_bound z R B (N+r) s L (later_source z R B N r h))
  have diff := GaussianRationalReciprocal.bound_congr eq.eqSymm (.eqRefl _) (.eqRefl _) tail
  exact distance_congr (original_sum_as_degree z B N (r+s) L h.andE₁)
    (original_sum_as_degree z B N r L h.andE₁) (.eqRefl _) (.eqRefl _) diff

def observation (p z R B N L : PTm n) : PTm n := degreeMajor z B N (GammaCanonicalNames.count p R) L
@[simp] theorem subst_observation {m : ℕ} (σ : Fin n → PTm m) (p z R B N L : PTm n) :
    Syn.subst σ (observation p z R B N L) = observation (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ L) := by simp [observation]

theorem original_count_budget (p R N : PTm n) : Γ ⊢[PRAAx]
    le (unit p*(R*R)) (N+GammaCanonicalNames.count p R) := by
  have grow : Γ ⊢[PRAAx] le (unit p) (pw two (GammaCanonicalNames.precision p)) :=
    GaussianFactorBudget.power_monotone_length two p _ (le_succ_self one) (le_add_right _ _)
  exact le_trans (AnalyticNumberTheory.PhiLower.le_mul_mono grow (le_refl (R*R)))
    (le_congr (by ipra_ring : Γ ⊢[PRAAx] pw two (GammaCanonicalNames.precision p)*R*R ≐
      pw two (GammaCanonicalNames.precision p)*(R*R)) (.eqRefl _) (GammaCanonicalNames.index_budget p R N))

theorem ordered_precision_distance (p k z R B N L : PTm n) (h : Γ ⊢[PRAAx] source z R B N) : Γ ⊢[PRAAx]
    distanceBounded (observation (p+k) z R B N L) (observation p z R B N L) one (unit p) := by
  have first := finite_horizon_distance z R B N (GammaCanonicalNames.count p R) (GammaCanonicalNames.gap p k R) L h
  have moved := distance_congr
    (GaussianRationalFiniteSum.sum_index_congr (Γ := Γ) _ (.eqRefl _)
      (congrPairT (GammaCanonicalNames.count_gap p k R).eqSymm (.eqRefl _)))
    (.eqRefl _) (.eqRefl _) (.eqRefl _) first
  exact distance_radius_mono _ _ _ _ _ _ (le_trans h.andE₂.andE₁ (le_add_right _ _)) (unit_positive p)
    (le_congr (mul_comm (unit p) (R*R)) (one_mul _).eqSymm (original_count_budget p R N)) moved

theorem observation_congr {p p' z z' R R' B B' N N' L L' : PTm n}
    (hp : Γ ⊢[PRAAx] p ≐ p') (hz : Γ ⊢[PRAAx] z ≐ z') (hR : Γ ⊢[PRAAx] R ≐ R')
    (hB : Γ ⊢[PRAAx] B ≐ B') (hN : Γ ⊢[PRAAx] N ≐ N') (hL : Γ ⊢[PRAAx] L ≐ L') : Γ ⊢[PRAAx]
    observation p z R B N L ≐ observation p' z' R' B' N' L' := by
  have e5 : (![p,z,R,B,N,L] : Fin 6 → PTm n) 5 = L := rfl
  have e5' : (![p',z',R',B',N',L'] : Fin 6 → PTm n) 5 = L' := rfl
  ipra_congr (observation (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) with
    [hp, hz, hR, hB, hN, hL] using [e5, e5']
theorem later_precision_distance (s t z R B N L : PTm n) (h : Γ ⊢[PRAAx] source z R B N)
    (hst : Γ ⊢[PRAAx] le s t) : Γ ⊢[PRAAx]
    distanceBounded (observation t z R B N L) (observation s z R B N L) one (unit s) :=
  distance_congr (observation_congr (eq_add_of_le hst).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _))
    (.eqRefl _) (.eqRefl _) (.eqRefl _) (ordered_precision_distance s (LeanProofs.IPRA.PTm.monus t s) z R B N L h)
theorem observation_regularity (s t z R B N L : PTm n) (h : Γ ⊢[PRAAx] source z R B N) : Γ ⊢[PRAAx]
    distanceBounded (observation s z R B N L) (observation t z R B N L) (unit s+unit t) (unit s*unit t) := by
  have us := unit_positive (Γ := Γ) s
  have ut := unit_positive (Γ := Γ) t
  refine .orE (lt_or_le s t) ?_ ?_
  · exact distance_radius_mono _ _ _ _ _ _ us.wk (positive_product _ _ us.wk ut.wk)
      (le_of_eq_add (d := unit s*unit s) (by ipra_ring))
      (distance_symmetric _ _ _ _ us.wk (later_precision_distance s t z R B N L h.wk (le_of_lt Prf.hyp0)))
  · exact distance_radius_mono _ _ _ _ _ _ ut.wk (positive_product _ _ us.wk ut.wk)
      (le_of_eq_add (d := unit t*unit t) (by ipra_ring)) (later_precision_distance t s z R B N L h.wk Prf.hyp0)

def data (z R B N L : PTm n) : PTm n := pairT z (pairT R (pairT B (pairT N L)))
def nameF : PR 2 := PTm.toPR (observation (var 0) (fstT (var 1)) (fstT (sndT (var 1)))
  (fstT (sndT (sndT (var 1)))) (fstT (sndT (sndT (sndT (var 1))))) (sndT (sndT (sndT (sndT (var 1))))) : PTm 2)
def sample (p z R B N L : PTm n) : PTm n := ap2 nameF p (data z R B N L)
@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (z R B N L : PTm n) :
    Syn.subst σ (data z R B N L) = data (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ L) := by
  simp [data]
theorem sample_at (p z R B N L : PTm n) : Γ ⊢[PRAAx] sample p z R B N L ≐ observation p z R B N L := by
  have raw := toPR_eq (Γ := Γ) (observation (var 0) (fstT (var 1)) (fstT (sndT (var 1)))
    (fstT (sndT (sndT (var 1)))) (fstT (sndT (sndT (sndT (var 1))))) (sndT (sndT (sndT (sndT (var 1))))) : PTm 2)
    ![p,data z R B N L]
  have e : Γ ⊢[PRAAx] sample p z R B N L ≐ observation p (fstT (data z R B N L)) (fstT (sndT (data z R B N L)))
      (fstT (sndT (sndT (data z R B N L)))) (fstT (sndT (sndT (sndT (data z R B N L)))))
      (sndT (sndT (sndT (sndT (data z R B N L))))) := by
    simpa only [sample,nameF,ap2,subst_observation,subst_fstT,subst_sndT,Syn.subst_var,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons] using raw
  have t₁ := snd_pair (Γ := Γ) z (pairT R (pairT B (pairT N L)))
  have t₂ := (congrSnd t₁).eqTrans (snd_pair R (pairT B (pairT N L)))
  have t₃ := (congrSnd t₂).eqTrans (snd_pair B (pairT N L))
  exact e.eqTrans (observation_congr (.eqRefl _) (fst_pair _ _) ((congrFst t₁).eqTrans (fst_pair _ _))
    ((congrFst t₂).eqTrans (fst_pair _ _)) ((congrFst t₃).eqTrans (fst_pair _ _)) ((congrSnd t₃).eqTrans (snd_pair _ _)))
theorem sample_canonical (p z R B N L : PTm n) : Γ ⊢[PRAAx] GaussianRationalHorner.canonical (sample p z R B N L) :=
  GaussianRationalHorner.canonical_congr (sample_at p z R B N L)
    (GaussianGammaFiniteDegreeRearrangement.degree_major_canonical z B N (GammaCanonicalNames.count p R) L)
theorem sample_bound (p z R B N L : PTm n) (h : Γ ⊢[PRAAx] source z R B N) : Γ ⊢[PRAAx]
    GaussianRationalMetric.bounded (sample p z R B N L) (R*R) N :=
  GaussianRationalReciprocal.bound_congr (sample_at p z R B N L).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianGammaFiniteDegreeRearrangement.uniform_rearranged_bound z R B N (GammaCanonicalNames.count p R) L h)
theorem name_regular (z R B N L : PTm n) (h : Γ ⊢[PRAAx] source z R B N) : Γ ⊢[PRAAx]
    GaussianEuclideanDistanceName.pointCN nameF (data z R B N L) := by
  refine .allI (.allI ?_)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R))
      (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift N)) := by simpa [Fm.shift,Syn.shift] using h.shift.shift
  have bound := distance_congr
    (sample_at (var 1) (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift B))
      (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift L))).eqSymm
    (sample_at (var 0) (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift B))
      (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift L))).eqSymm (.eqRefl _) (.eqRefl _)
    (observation_regularity (var 1) (var 0) (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift B))
      (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift L)) hs)
  simpa only [GaussianEuclideanDistanceName.pointCN,sample,Syn.shift,subst_data,unit,GaussianEuclideanPointDistance.unit] using bound

theorem original_finite_horizon_split_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (splitLaw (var 0) (var 1) (var 2) (var 3) (var 5) (var 4)) := closeUniv 6 (sum_split _ _ _ _ _ _)
theorem original_fixed_degree_horizon_distance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 0) (var 1) (var 2) (var 3) ⟶
      distanceBounded (degreeMajor (var 0) (var 2) (var 3) (var 4+var 5) (var 6))
        (degreeMajor (var 0) (var 2) (var 3) (var 4) (var 6)) (var 1*var 1) (var 3+var 4)) :=
  closeUniv 7 (.impI (finite_horizon_distance _ _ _ _ _ _ _ Prf.hyp0))
theorem actual_fixed_degree_tail_sampler_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (sample (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ≐ observation (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (sample_at _ _ _ _ _ _)
theorem original_fixed_degree_tail_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) (var 3) ⟶ GaussianEuclideanDistanceName.pointCN nameF
      (data (var 0) (var 1) (var 2) (var 3) (var 4))) := closeUniv 5 (.impI (name_regular _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaFixedDegreeHorizon

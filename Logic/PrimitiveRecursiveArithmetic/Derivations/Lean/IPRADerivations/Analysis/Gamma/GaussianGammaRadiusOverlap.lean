import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaWeierstrassConvergence
import IPRADerivations.Analysis.Gamma.GaussianGammaReciprocalInverse

/-!
# Original Gamma names agree on overlapping disks

The original folded P_N program and its data are independent of the
supplied radius. A common arbitrarily late cutoff meets both C11 rates.
The two original C7 observations therefore differ only by their requested
dyadic errors and an auxiliary error removed by finite rational slack.
Actual named reciprocal properness then permits different radii, pole
certificates and numerical apartness anchors for Gamma itself.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaRadiusOverlap

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaFiniteApproximantName (pF pData)
open GaussianGammaCanonicalExponent (source)
open GaussianGammaWeierstrassConvergence (rate)
open GaussianGammaC9Bound (majorant)
open GaussianNamedSmallPerturbationTransport (budgetNumerator budgetDenominator denominator_positive)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalHorner (positive_product)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianNameEquivalence (crossEquivalent cross_at)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def commonCutoff (t R S : PTm n) : PTm n :=
  GaussianGammaWeierstrassConvergence.cutoff t R+GaussianGammaWeierstrassConvergence.cutoff t S+t
@[simp] theorem subst_commonCutoff {m : ℕ} (σ : Fin n → PTm m) (t R S : PTm n) :
    Syn.subst σ (commonCutoff t R S) = commonCutoff (Syn.subst σ t) (Syn.subst σ R) (Syn.subst σ S) := by
  simp [commonCutoff]

theorem common_cutoff_bounds (t R S : PTm n) : Γ ⊢[PRAAx]
    le (GaussianGammaWeierstrassConvergence.cutoff t R) (commonCutoff t R S) ⋏
      (le (GaussianGammaWeierstrassConvergence.cutoff t S) (commonCutoff t R S) ⋏ le t (commonCutoff t R S)) := by
  unfold commonCutoff
  refine .andI ?_ (.andI ?_ ?_)
  · ipra_le 𝔞 (GaussianGammaWeierstrassConvergence.cutoff t S)+𝔞 t
  · ipra_le 𝔞 (GaussianGammaWeierstrassConvergence.cutoff t R)+𝔞 t
  · ipra_le 𝔞 (GaussianGammaWeierstrassConvergence.cutoff t R)+𝔞 (GaussianGammaWeierstrassConvergence.cutoff t S)

theorem finite_cutoff_error (t p z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B)
    (hcut : Γ ⊢[PRAAx] le (GaussianGammaWeierstrassConvergence.cutoff t R) N) : Γ ⊢[PRAAx]
    distanceBounded (ap2 pF (succ t) (pData z B N)) (GaussianGammaC7Name.sample p z R B)
      (unit t+unit p) (unit t*unit p) := by
  have hg := GaussianGammaWeierstrassConvergence.cutoff_guards (Γ := Γ) t R
  have hs : Γ ⊢[PRAAx] GaussianGammaWeierstrassConvergence.source z R B N :=
    .andI h (.andI (le_trans hg.andE₁ hcut) (le_trans hg.andE₂.andE₁ hcut))
  have hn := (GaussianGammaWeierstrassConvergence.local_source z R B N hs).andE₂.andE₁
  have c : Γ ⊢[PRAAx] le (budgetNumerator (succ t) p (R*R) N (majorant R)*(unit t*unit p))
      ((unit t+unit p)*budgetDenominator (succ t) p N) := by
    have e := natEq (pw_succ (Γ := Γ) two t)
    have hm := le_trans hg.andE₂.andE₂ hcut
    ipra_le 𝔞 (unit t)*𝔞 (unit p)*𝔞 (unit p)*sl hm using
      unfold budgetNumerator budgetDenominator rate unit
      ipra_simps
      rw [e]
      ring
  exact distance_radius_mono _ _ _ _ _ _ (denominator_positive (succ t) p N hn)
    (positive_product _ _ (unit_positive t) (unit_positive p)) c
    (GaussianGammaWeierstrassConvergence.observation_error (succ t) p z R B N hs)

theorem original_P_overlap_slack (p q t z R S B : PTm n)
    (hR : Γ ⊢[PRAAx] source z R B) (hS : Γ ⊢[PRAAx] source z S B) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (qsub (GaussianGammaC7Name.sample p z R B) (GaussianGammaC7Name.sample q z S B))
      (unit p+unit q) (unit p*unit q) two t := by
  let N := commonCutoff t R S
  let Z := unit p*unit q*unit t
  have zpos : Γ ⊢[PRAAx] le one Z := positive_product _ _
    (positive_product _ _ (unit_positive p) (unit_positive q)) (unit_positive t)
  have hb := common_cutoff_bounds (Γ := Γ) t R S
  have left := distance_radius_mono _ _ _ _ ((unit t+unit p)*unit q) Z
    (positive_product _ _ (unit_positive t) (unit_positive p)) zpos
    (le_of_eq_add (d := zero) (by dsimp only [Z]; ipra_ring))
    (distance_symmetric _ _ _ _ (positive_product _ _ (unit_positive t) (unit_positive p))
      (finite_cutoff_error t p z R B N hR hb.andE₁))
  have right := distance_radius_mono _ _ _ _ ((unit t+unit q)*unit p) Z
    (positive_product _ _ (unit_positive t) (unit_positive q)) zpos
    (le_of_eq_add (d := zero) (by dsimp only [Z]; ipra_ring))
    (finite_cutoff_error t q z S B N hS hb.andE₂.andE₁)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold unit; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ zpos left right)

theorem original_P_observation_overlap (p q z R S B : PTm n)
    (hR : Γ ⊢[PRAAx] source z R B) (hS : Γ ⊢[PRAAx] source z S B) : Γ ⊢[PRAAx]
    distanceBounded (GaussianGammaC7Name.sample p z R B) (GaussianGammaC7Name.sample q z S B)
      (unit p+unit q) (unit p*unit q) := by
  apply GaussianRationalSlackRemoval.slack_removal _ _ _ two (positive_product _ _ (unit_positive p) (unit_positive q))
  refine .allI ?_
  have r : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) := by
    simpa [Fm.shift,Syn.shift] using hR.shift
  have s : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift S) (Syn.shift B) := by
    simpa [Fm.shift,Syn.shift] using hS.shift
  simpa only [GaussianRationalSlackRemoval.allSlack,GaussianRationalMetric.subst_qsub,GaussianGammaC7Name.subst_sample,
    GaussianCoefficientNameBounds.subst_unit,PTm.subst_add,PTm.subst_mul,Syn.shift,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    original_P_overlap_slack (Syn.shift p) (Syn.shift q) (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift S) (Syn.shift B) r s

theorem original_P_overlap (z R S B : PTm n) (hR : Γ ⊢[PRAAx] source z R B) (hS : Γ ⊢[PRAAx] source z S B) : Γ ⊢[PRAAx]
    crossEquivalent GaussianGammaC7Name.nameF GaussianGammaC7Name.nameF (GaussianGammaC7Name.data z R B) (GaussianGammaC7Name.data z S B) := by
  refine .allI (.allI ?_)
  have r : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift B)) := by
    simpa [Fm.shift,Syn.shift] using hR.shift.shift
  have s : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift S)) (Syn.shift (Syn.shift B)) := by
    simpa [Fm.shift,Syn.shift] using hS.shift.shift
  simpa only [crossEquivalent,GaussianGammaC7Name.sample,GaussianGammaC7Name.subst_data,Syn.shift,unit,
    GaussianEuclideanPointDistance.unit] using original_P_observation_overlap (var 1) (var 0)
    (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift S)) (Syn.shift (Syn.shift B)) r s

theorem original_Gamma_overlap (z R S B a d c e : PTm n)
    (hR : Γ ⊢[PRAAx] GaussianGammaReciprocalInverse.source z R B a d)
    (hS : Γ ⊢[PRAAx] GaussianGammaReciprocalInverse.source z S B c e) : Γ ⊢[PRAAx]
    crossEquivalent GaussianGammaReciprocalInverse.gammaF GaussianGammaReciprocalInverse.gammaF
      (GaussianGammaReciprocalInverse.gammaData z R B d) (GaussianGammaReciprocalInverse.gammaData z S B e) := by
  have r := (GaussianGammaReciprocalInverse.original_gamma_inverse z R B a d hR).andE₁
  have s := (GaussianGammaReciprocalInverse.original_gamma_inverse z S B c e hS).andE₁
  exact GaussianNameReciprocal.names_equivalent GaussianGammaC7Name.nameF GaussianGammaC7Name.nameF
    (GaussianGammaReciprocalInverse.gammaHeight z R B d) (GaussianGammaReciprocalInverse.gammaHeight z S B e)
    (GaussianGammaC7Name.data z R B) (GaussianGammaC7Name.data z S B) r.andE₁ s.andE₁ r.andE₂ s.andE₂
    (GaussianNameEquivalence.cross_to_diagonal _ _ _ _ (original_P_overlap z R S B hR.andE₁ hS.andE₁))

theorem original_Gamma_observation_overlap (p q z R S B a d c e : PTm n)
    (hR : Γ ⊢[PRAAx] GaussianGammaReciprocalInverse.source z R B a d)
    (hS : Γ ⊢[PRAAx] GaussianGammaReciprocalInverse.source z S B c e) : Γ ⊢[PRAAx]
    distanceBounded
      (ap2 GaussianGammaReciprocalInverse.gammaF p (GaussianGammaReciprocalInverse.gammaData z R B d))
      (ap2 GaussianGammaReciprocalInverse.gammaF q (GaussianGammaReciprocalInverse.gammaData z S B e))
      (unit p+unit q) (unit p*unit q) := cross_at _ _ _ _ p q (original_Gamma_overlap z R S B a d c e hR hS)

theorem actual_common_cutoff_cofinal_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 0) (commonCutoff (var 0) (var 1) (var 2))) := closeUniv 3 (common_cutoff_bounds _ _ _).andE₂.andE₂
theorem original_C7_radius_overlap_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((source (var 0) (var 1) (var 3) ⋏ source (var 0) (var 2) (var 3)) ⟶
      crossEquivalent GaussianGammaC7Name.nameF GaussianGammaC7Name.nameF
        (GaussianGammaC7Name.data (var 0) (var 1) (var 3)) (GaussianGammaC7Name.data (var 0) (var 2) (var 3))) :=
  closeUniv 4 (.impI (original_P_overlap _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))
theorem original_Gamma_radius_and_certificate_overlap_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((GaussianGammaReciprocalInverse.source (var 0) (var 1) (var 3) (var 4) (var 5) ⋏
      GaussianGammaReciprocalInverse.source (var 0) (var 2) (var 3) (var 6) (var 7)) ⟶
      crossEquivalent GaussianGammaReciprocalInverse.gammaF GaussianGammaReciprocalInverse.gammaF
        (GaussianGammaReciprocalInverse.gammaData (var 0) (var 1) (var 3) (var 5))
        (GaussianGammaReciprocalInverse.gammaData (var 0) (var 2) (var 3) (var 7))) :=
  closeUniv 8 (.impI (original_Gamma_overlap _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))
theorem original_Gamma_independent_overlap_observations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    ((GaussianGammaReciprocalInverse.source (var 2) (var 3) (var 5) (var 6) (var 7) ⋏
      GaussianGammaReciprocalInverse.source (var 2) (var 4) (var 5) (var 8) (var 9)) ⟶
      distanceBounded
        (ap2 GaussianGammaReciprocalInverse.gammaF (var 0) (GaussianGammaReciprocalInverse.gammaData (var 2) (var 3) (var 5) (var 7)))
        (ap2 GaussianGammaReciprocalInverse.gammaF (var 1) (GaussianGammaReciprocalInverse.gammaData (var 2) (var 4) (var 5) (var 9)))
        (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 10 (.impI (original_Gamma_observation_overlap _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaRadiusOverlap

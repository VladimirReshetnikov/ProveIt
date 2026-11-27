import IPRADerivations.Analysis.Euler.Logarithms.Exhaustion.GaussianEulerLogarithmicCutoffCauchy
import IPRADerivations.Analysis.Euler.CompactExhaustion.Cutoffs.GaussianEulerVaryingCutoffName

/-!
# The original logarithmic integrals as regular varying-cutoff names

The actual compact program is evaluated at the scheduled cutoff and
observation query. The finite lower and upper tails derive regularity
for every internal logarithmic order, under the original source guards.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicImproperName

open_ipra
open GaussianEulerLogarithmicCutoffCauchy (source observation)
open GaussianEulerLogarithmicCommonCutoff (cutoff)
open GaussianEulerCutoffCauchyComparison (clock)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianRationalHorner (canonical positive_product)
open GaussianEuclideanDistanceName (pointCN)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (j z R B A : PTm n) : PTm n := pairT j (GaussianEulerVaryingCutoffName.data z R B A)
def sample (p j z R B A : PTm n) : PTm n := observation (clock p) j z R B A (cutoff p j A)
private def reader (p d : PTm n) : PTm n := sample p (fstT d) (fstT (sndT d)) (fstT (sndT (sndT d)))
  (fstT (sndT (sndT (sndT d)))) (sndT (sndT (sndT (sndT d))))
def nameF : PR 2 := PTm.toPR (reader (var 0) (var 1))

ipra_subst data
ipra_subst sample

theorem name_at (p j z R B A : PTm n) : Γ ⊢[PRAAx] ap2 nameF p (data j z R B A) ≐ sample p j z R B A := by
  let x := data j z R B A
  have program : Γ ⊢[PRAAx] ap2 nameF p x ≐ reader p x := by
    simpa [nameF,ap2,reader] using toPR_eq (Γ := Γ) (reader (var 0) (var 1) : PTm 2) ![p,x]
  have tail : Γ ⊢[PRAAx] sndT x ≐ GaussianEulerVaryingCutoffName.data z R B A := snd_pair _ _
  refine program.eqTrans ?_
  simpa [reader] using Prf.eqCongr
    (sample (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6)
    (σ := ![p,fstT x,fstT (sndT x),fstT (sndT (sndT x)),fstT (sndT (sndT (sndT x))),sndT (sndT (sndT (sndT x)))])
    (σ' := ![p,j,z,R,B,A]) (fun i => by
      fin_cases i
      · exact .eqRefl _
      · exact fst_pair _ _
      · exact (congrFst tail).eqTrans (GaussianEulerVaryingCutoffName.data_z _ _ _ _)
      · exact (congrFst (congrSnd tail)).eqTrans (GaussianEulerVaryingCutoffName.data_R _ _ _ _)
      · exact (congrFst (congrSnd (congrSnd tail))).eqTrans (GaussianEulerVaryingCutoffName.data_B _ _ _ _)
      · exact (congrSnd (congrSnd (congrSnd tail))).eqTrans (GaussianEulerVaryingCutoffName.data_A _ _ _ _))

theorem name_canonical (p j z R B A : PTm n) : Γ ⊢[PRAAx] canonical (ap2 nameF p (data j z R B A)) :=
  GaussianRationalHorner.canonical_congr (name_at p j z R B A)
    (GaussianEulerLogarithmicCutoffCauchy.observation_canonical _ _ _ _ _ _ _)

private theorem observation_congr (p q j z R B A : PTm n) (h : Γ ⊢[PRAAx] p ≐ q) : Γ ⊢[PRAAx]
    sample p j z R B A ≐ sample q j z R B A := by
  simpa using Prf.eqCongr (sample (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6)
    (σ := ![p,j,z,R,B,A]) (σ' := ![q,j,z,R,B,A]) (fun i => by fin_cases i <;> first | exact h | exact .eqRefl _)

private theorem ordered_samples (p q j z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A)
    (hpq : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx]
    distanceBounded (sample q j z R B A) (sample p j z R B A) (unit p+unit q) (unit p*unit q) := by
  refine .orE (lt_or_eq_of_le hpq) (GaussianEulerLogarithmicCutoffCauchy.ordered_clock_comparison p q j z R B A h.wk Prf.hyp0) ?_
  have hD : (p ≐ q) :: Γ ⊢[PRAAx] le one (unit p*unit q) :=
    positive_product _ _ (unit_positive _) (unit_positive _)
  have refl := GaussianRationalPowerDifference.distance_refl_zero (sample p j z R B A) (unit p*unit q) hD
  exact distance_congr (observation_congr p q j z R B A Prf.hyp0) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ zero _ _ _ hD hD (le_congr (by ipra_ring) (.eqRefl _) (zero_le _)) refl)

theorem sample_regularity (p q j z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    distanceBounded (sample p j z R B A) (sample q j z R B A) (unit p+unit q) (unit p*unit q) := by
  refine .orE (le_total p q) ?_ ?_
  · exact distance_symmetric _ _ _ _ (positive_product _ _ (unit_positive p) (unit_positive q))
      (ordered_samples p q j z R B A h.wk Prf.hyp0)
  · exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (by ipra_ring)
      (ordered_samples q p j z R B A h.wk Prf.hyp0)

theorem name_observations (p q j z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (data j z R B A)) (ap2 nameF q (data j z R B A)) (unit p+unit q) (unit p*unit q) :=
  distance_congr (name_at p j z R B A).eqSymm (name_at q j z R B A).eqSymm (.eqRefl _) (.eqRefl _)
    (sample_regularity p q j z R B A h)

theorem name_regular (j z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx] pointCN nameF (data j z R B A) := by
  let lift (x : PTm n) := Syn.shift (Syn.shift x)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source (lift z) (lift R) (lift B) (lift A) :=
    by simpa only [Fm.shift,Syn.shift,GaussianEulerLogarithmicCutoffCauchy.subst_source,lift] using h.shift.shift
  refine .allI (.allI ?_)
  simpa only [pointCN,GaussianEuclideanPointDistance.unit,unit,Syn.shift,subst_data,lift] using
    name_observations (var 1) (var 0) (lift j) (lift z) (lift R) (lift B) (lift A) hs

theorem actual_original_logarithmic_Euler_improper_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 1) (var 2) (var 3) (var 4) ⟶ pointCN nameF (data (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (name_regular _ _ _ _ _ Prf.hyp0))

theorem actual_original_logarithmic_Euler_improper_observation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (ap2 nameF (var 0) (data (var 1) (var 2) (var 3) (var 4) (var 5)) ≐
      sample (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) := closeUniv 6 (name_at _ _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicImproperName

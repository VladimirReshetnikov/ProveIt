import IPRADerivations.Analysis.GaussianEulerLogarithmicIntervalName
import IPRADerivations.Analysis.GaussianCompactClientIndependence

/-!
# The actual logarithmic Euler quadrature at order zero

The numerical power zero leaves the original integrand sample. Comparing
the actual compact names also accounts for the logarithmic evaluator's
query and the two original independently selected quadrature meshes.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicOrderZero

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerCompactAdditivity (intervalSource)
open GaussianCompactRiemannName (inside nameData evaluatorName)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianNameEquivalence (crossEquivalent)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianEulerLogarithmicCompactName (query)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "logEvaluator" => GaussianEulerLogarithmicCompactName.evaluatorF
local notation "plainEvaluator" => GaussianEulerIntegrandName.evaluatorF
local notation "logClient" => GaussianEulerLogarithmicCompactName.fixedData
local notation "plainClient" => GaussianEulerIntegrandName.fixedData

theorem raw_order_zero (p z R B E T a b : PTm n) : Γ ⊢[PRAAx]
    GaussianEulerLogarithmicCompactName.sample p zero R E T z B a b ≐
      GaussianEulerIntegrandName.sample (query p zero R E T) z B a b := by
  let k := query p zero R E T
  let e := GaussianEulerIntegrandName.sample k z B a b
  exact (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl e)
    (GaussianRationalReciprocal.power_zero (GaussianPositiveRationalLogarithm.sample k a b))).eqTrans
    (GaussianReciprocalHorner.qmul_one_right e (GaussianEulerIntegrandName.sample_canonical k z B a b))

theorem original_sample_comparison (p q z R B E T a b : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerIntegrandName.source z B a b) : Γ ⊢[PRAAx]
    distanceBounded (GaussianEulerLogarithmicCompactName.sample p zero R E T z B a b)
      (GaussianEulerIntegrandName.sample q z B a b) (unit p+unit q) (unit p*unit q) := by
  let k := query p zero R E T
  have later : Γ ⊢[PRAAx] le p k := le_add_right _ _
  have hu := GaussianExponentialReference.unit_monotone later
  have uq := unit_positive (Γ := Γ) q
  have d := GaussianEulerIntegrandName.sample_regularity k q z B a b h
  have comparison := distance_radius_mono _ _ _ _ (unit p+unit q) (unit p*unit q)
    (positive_product _ _ (unit_positive k) uq) (positive_product _ _ (unit_positive p) uq)
    (by dsimp only [k]; ipra_le (𝔞(unit q)*𝔞(unit q))*sl hu) d
  exact distance_congr (raw_order_zero p z R B E T a b).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) comparison

private theorem original_raw_plain_at (q t z B : PTm n) : Γ ⊢[PRAAx]
    ap3 plainEvaluator q t (plainClient z B) ≐ GaussianEulerIntegrandName.sample q z B (fstT t) (sndT t) := by
  have decoded : Γ ⊢[PRAAx] GaussianEulerIntegrandName.data (fstT (plainClient z B)) (sndT (plainClient z B)) (fstT t) (sndT t) ≐
      GaussianEulerIntegrandName.data z B (fstT t) (sndT t) := by
    simpa using Prf.eqCongr (GaussianEulerIntegrandName.data (var 0) (var 1) (var 2) (var 3) : PTm 4)
      (σ := ![fstT (plainClient z B),sndT (plainClient z B),fstT t,sndT t]) (σ' := ![z,B,fstT t,sndT t]) (fun i => by
        fin_cases i
        · exact fst_pair _ _
        · exact snd_pair _ _
        · exact .eqRefl _
        · exact .eqRefl _)
  exact (GaussianEulerIntegrandName.evaluator_at q t (plainClient z B)).eqTrans
    ((congrAp2 GaussianEulerIntegrandName.nameF (.eqRefl _) decoded).eqTrans
      (GaussianEulerIntegrandName.sample_at q z B (fstT t) (sndT t)).eqSymm)

theorem original_local_cross (t z R B E T : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerIntegrandName.source z B (fstT t) (sndT t)) : Γ ⊢[PRAAx]
    crossEquivalent (evaluatorName logEvaluator) (evaluatorName plainEvaluator)
      (nameData t (logClient zero R E T z B)) (nameData t (plainClient z B)) := by
  let lift (x : PTm n) := Syn.shift (Syn.shift x)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      GaussianEulerIntegrandName.source (lift z) (lift B) (fstT (lift t)) (sndT (lift t)) :=
    by simpa [Fm.shift,Syn.shift,lift,GaussianEulerIntegrandName.source] using h.shift.shift
  have old := original_sample_comparison (var 1) (var 0) (lift z) (lift R) (lift B) (lift E) (lift T)
    (fstT (lift t)) (sndT (lift t)) hs
  have logAt := (GaussianCompactRiemannName.evaluator_at (Γ := (Γ.map Fm.shift).map Fm.shift) logEvaluator (var 1) (lift t)
    (logClient zero (lift R) (lift E) (lift T) (lift z) (lift B))).eqTrans
    (GaussianEulerLogarithmicCompactName.raw_evaluator_at (var 1) (lift t) zero (lift R) (lift E) (lift T) (lift z) (lift B))
  have plainAt := (GaussianCompactRiemannName.evaluator_at (Γ := (Γ.map Fm.shift).map Fm.shift)
    plainEvaluator (var 0) (lift t) (plainClient (lift z) (lift B))).eqTrans
    (original_raw_plain_at (var 0) (lift t) (lift z) (lift B))
  refine .allI (.allI ?_)
  simpa [crossEquivalent,Syn.shift,lift] using distance_congr logAt.eqSymm plainAt.eqSymm (.eqRefl _) (.eqRefl _) old

theorem compact_order_zero (z R B a C E T : PTm n) (h : Γ ⊢[PRAAx] intervalSource z R B a C E T) : Γ ⊢[PRAAx]
    crossEquivalent GaussianEulerLogarithmicIntervalName.nameF GaussianEulerCompactAdditivity.nameF
      (GaussianEulerLogarithmicIntervalName.data zero z R B a C E T) (GaussianEulerCompactAdditivity.data z R B a C E T) := by
  have localRows : Γ ⊢[PRAAx] GaussianCompactClientIndependence.localAgreement logEvaluator plainEvaluator a C E
      (logClient zero R E T z B) (plainClient z B) := by
    let sh (x : PTm n) := Syn.shift x
    let Δ := inside (sh a) (sh C) (sh E) (var 0) :: Γ.map Fm.shift
    have hs : Γ.map Fm.shift ⊢[PRAAx] intervalSource (sh z) (sh R) (sh B) (sh a) (sh C) (sh E) (sh T) :=
      by simpa [Fm.shift,Syn.shift,sh] using h.shift
    have ht : Δ ⊢[PRAAx] inside (sh a) (sh C) (sh E) (var 0) := Prf.hyp0
    have positiveTime : Δ ⊢[PRAAx] GaussianEulerIntegrandName.source (sh z) (sh B) (fstT (var 0)) (sndT (var 0)) :=
      .andI hs.wk.andE₁.andE₁ (.andI ht.andE₁ ht.andE₂.andE₁)
    refine .allI (.impI ?_)
    simpa [GaussianCompactClientIndependence.localAgreement,Syn.shift,sh,Δ] using
      original_local_cross (var 0) (sh z) (sh R) (sh B) (sh E) (sh T) positiveTime
  exact GaussianCompactClientIndependence.name_independence logEvaluator plainEvaluator a C E
    (GaussianEulerLogarithmicMultiplier.lipschitz zero R E T) T (GaussianEulerCompactModulus.lipschitz R E T) T
    (logClient zero R E T z B) (plainClient z B) (.andI (GaussianEulerLogarithmicIntervalName.compact_input zero z R B a C E T h)
      (.andI (GaussianEulerCompactAdditivity.compact_input z R B a C E T h) localRows))

theorem actual_original_logarithmic_compact_order_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (intervalSource (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      crossEquivalent GaussianEulerLogarithmicIntervalName.nameF GaussianEulerCompactAdditivity.nameF
        (GaussianEulerLogarithmicIntervalName.data zero (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
        (GaussianEulerCompactAdditivity.data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))) :=
  closeUniv 7 (.impI (compact_order_zero _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicOrderZero

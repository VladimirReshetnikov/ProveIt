import IPRADerivations.Analysis.Stirling.AllOrders.GaussianStirlingAllOrderFirstPanelFiniteSum
import IPRADerivations.Analysis.Stirling.GaussianStirlingGlobalBoundsTranslatedRate
import IPRADerivations.Analysis.Stirling.GaussianStirlingGammaFractionalIncrement

/-!
# The original improper first-order Stirling remainder

At the computed cutoff, the normalized finite sum of literal first
periodic panels approaches the original log-Gamma remainder. The
control comes from the original finite telescope and the certified
translated Stirling observation rate, with the identified constant.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderFirstPanelImproper

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianStirlingNames (source)
open GaussianStirlingGlobalBounds (steps translatedPoint endpoint_close remainder_regular remainder_cross remainderF remainderData
  limitRemainderF limitRemainderData rate_at)
open GaussianStirlingGlobalBoundsTranslatedRate (translated_rate)
open GaussianStirlingGammaFractionalIncrement (increment_rate)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianNameEquivalence (crossEquivalent cross_at point_at)
open GaussianEuclideanDistanceName (pointCN)
open GaussianValueNormalizerExtensionality (rawDiagonal)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "panelsF" => GaussianStirlingAllOrderFirstPanelFiniteSum.nameF
local notation "panelsData" => GaussianStirlingAllOrderFirstPanelFiniteSum.data
local notation "endpointF" => GaussianNamedDifference.nameF GaussianStirlingNames.nameF GaussianStirlingNames.nameF

def raw (p A B : PTm n) : PTm n := ap2 panelsF p (panelsData (steps p) A B)
def rawF : PR 2 := PTm.toPR (raw (var 0) (fstT (var 1)) (sndT (var 1)))
def rawData (A B : PTm n) : PTm n := pairT A B
def nameF : PR 2 := GaussianFastValueCut.nameF rawF
def data (A B : PTm n) : PTm n := GaussianFastValueCut.nameData (num 47) (rawData A B)

@[simp] theorem subst_raw {l : ℕ} (σ : Fin n → PTm l) (p A B : PTm n) :
    Syn.subst σ (raw p A B) = raw (Syn.subst σ p) (Syn.subst σ A) (Syn.subst σ B) := by simp [raw]
@[simp] theorem subst_rawData {l : ℕ} (σ : Fin n → PTm l) (A B : PTm n) :
    Syn.subst σ (rawData A B) = rawData (Syn.subst σ A) (Syn.subst σ B) := by simp [rawData]
@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (A B : PTm n) :
    Syn.subst σ (data A B) = data (Syn.subst σ A) (Syn.subst σ B) := by simp [data]

theorem raw_at (p A B : PTm n) : Γ ⊢[PRAAx] ap2 rawF p (rawData A B) ≐ raw p A B := by
  let w := rawData A B
  have e : Γ ⊢[PRAAx] ap2 rawF p w ≐ raw p (fstT w) (sndT w) := by
    simpa [rawF,ap2] using toPR_eq (Γ := Γ) (raw (var 0) (fstT (var 1)) (sndT (var 1)) : PTm 2) ![p,w]
  exact e.eqTrans (by
    simpa using Prf.eqCongr (Γ := Γ) (raw (var 0) (var 1) (var 2) : PTm 3)
      (σ := ![p,fstT w,sndT w]) (σ' := ![p,A,B]) (fun i => by
        fin_cases i
        exact .eqRefl _
        exact fst_pair _ _
        exact snd_pair _ _))

theorem cutoff_error (p A B x : PTm n) (h : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] distanceBounded (raw p A B) (ap2 remainderF p (remainderData A B x)) (num 46) (unit p) := by
  let N := steps p
  let u := unit p
  let panelInput := panelsData N A B
  let endpointInput := GaussianStirlingTelescopeName.endpointData N A B
  let r := limitRemainderData A B x
  let s := remainderData A B x
  have hu := unit_positive (Γ := Γ) p
  have den := positive_product u u hu hu
  have panelCross := GaussianStirlingAllOrderFirstPanelFiniteSum.endpoint_cross N A B h
  have a := distance_radius_mono _ _ _ _ two u den hu (by unfold u; ipra_le 0)
    (cross_at panelsF endpointF panelInput endpointInput p p panelCross)
  have rate := translated_rate A B x h increment_rate
  have b := endpoint_close A B x (num 30) p h (rate_at A B x (num 30) p rate)
  have hc := remainder_cross A B x h (GaussianStirlingConstantIdentification.identification x x)
  have c := distance_radius_mono _ _ _ _ two u den hu (by unfold u; ipra_le 0)
    (cross_at limitRemainderF remainderF r s p p hc)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hu (distance_triangle_same _ _ _ _ _ _ hu a b) c)

private theorem raw_observations (p q A B x : PTm n) (h : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] distanceBounded (raw p A B) (raw q A B) (num 47*(unit p+unit q)) (unit p*unit q) := by
  let u := unit p
  let v := unit q
  let d := u*v
  have hu := unit_positive (Γ := Γ) p
  have hv := unit_positive (Γ := Γ) q
  have hd := positive_product _ _ hu hv
  have a := distance_radius_mono _ _ _ _ (num 46*v) d hu hd (by unfold d; ipra_le 0) (cutoff_error p A B x h)
  have b := point_at remainderF (remainderData A B x) p q (remainder_regular A B x h)
  have c := distance_radius_mono _ _ _ _ (num 46*u) d hv hd (by unfold d; ipra_le 0)
    (distance_symmetric _ _ _ _ hv (cutoff_error q A B x h))
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold u v; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hd (distance_triangle_same _ _ _ _ _ _ hd a b) c)

theorem raw_regular (A B x : PTm n) (h : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] GaussianFastValueCut.regular rawF (num 47) (rawData A B) := by
  refine .allI (.allI ?_)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let a := Syn.shift (Syn.shift A)
  let b := Syn.shift (Syn.shift B)
  let c := Syn.shift (Syn.shift x)
  have hs : Δ ⊢[PRAAx] source a b := by simpa [a,b,Δ,Fm.shift,Syn.shift] using h.shift.shift
  simpa [GaussianFastValueCut.regular,a,b,c,Δ,Syn.shift,GaussianCoefficientNameBounds.unit,GaussianEuclideanPointDistance.unit] using
    distance_congr (raw_at (var 1) a b).eqSymm (raw_at (var 0) a b).eqSymm (.eqRefl _) (.eqRefl _)
      (raw_observations (var 1) (var 0) a b c hs)

theorem name_regular (A B x : PTm n) (h : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] pointCN nameF (data A B) :=
  GaussianFastValueCut.name_fast rawF (num 47) _ (raw_regular A B x h)

private theorem normalized_error (p A B x : PTm n) (h : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data A B)) (ap2 remainderF p (remainderData A B x)) (num 94) (unit p) := by
  have e := GaussianNameRingLaws.normalized_to_sample rawF (num 47) (rawData A B) p (raw_regular A B x h)
  have a := distance_congr (.eqRefl _) (raw_at p A B) (.eqRefl _) (.eqRefl _) e
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) a (cutoff_error p A B x h))

theorem original_improper_cross (A B x : PTm n) (h : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] crossEquivalent nameF remainderF (data A B) (remainderData A B x) := by
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (num 94)
    (name_regular A B x h) (remainder_regular A B x h)
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let a := Syn.shift A
  let b := Syn.shift B
  let c := Syn.shift x
  have hs : Δ ⊢[PRAAx] source a b := by simpa [a,b,Δ,Fm.shift,Syn.shift] using h.shift
  simpa [rawDiagonal,a,b,c,Δ,Syn.shift,GaussianCoefficientNameBounds.unit,GaussianEuclideanPointDistance.unit] using
    normalized_error (var 0) a b c hs

theorem actual_first_periodic_improper_remainder_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source (var 0) (var 1) ⟶ crossEquivalent nameF remainderF (data (var 0) (var 1))
        (remainderData (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (original_improper_cross _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderFirstPanelImproper

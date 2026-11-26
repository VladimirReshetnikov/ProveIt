import IPRADerivations.Analysis.Stirling.AllOrders.PanelParts.GaussianStirlingAllOrderPanelPartsBinding

/-!
# Original primitive-recursive names for the full Bernoulli kernels

Each name evaluates the actual finite weighted prefix at its common
cofinal grid. The finite integration-by-parts recurrence certifies
its equality to the original Stirling remainder and its named
algebraic successors.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderImproperName

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianStirlingNames (source)
open GaussianStirlingAllOrderPanelPartsBinding (requiredMesh prefixAt radius actual_prefix_distance)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianFastValueCut (regular)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent point_at)
open GaussianValueNormalizerExtensionality (rawDiagonal normalized_names_equivalent)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "T" => GaussianStirlingAllOrderPanelPartsNames.nameF
local notation "TData" => GaussianStirlingAllOrderPanelPartsNames.nameData

def raw (m : ℕ) (p A B : PTm n) : PTm n := prefixAt m A B (requiredMesh m A B p) p
def rawF (m : ℕ) : PR 2 := PTm.toPR (raw m (var 0) (fstT (var 1)) (sndT (var 1)))
def rawData (A B : PTm n) : PTm n := pairT A B
def rate (m : ℕ) (B : PTm n) : PTm n := radius m B+one
def nameF (m : ℕ) : PR 2 := GaussianFastValueCut.nameF (rawF m)
def data (m : ℕ) (A B : PTm n) : PTm n := GaussianFastValueCut.nameData (rate m B) (rawData A B)

@[simp] theorem subst_raw {l : ℕ} (σ : Fin n → PTm l) (m : ℕ) (p A B : PTm n) :
    Syn.subst σ (raw m p A B) = raw m (Syn.subst σ p) (Syn.subst σ A) (Syn.subst σ B) := by simp [raw]
@[simp] theorem subst_rawData {l : ℕ} (σ : Fin n → PTm l) (A B : PTm n) :
    Syn.subst σ (rawData A B) = rawData (Syn.subst σ A) (Syn.subst σ B) := by simp [rawData]
@[simp] theorem subst_rate {l : ℕ} (σ : Fin n → PTm l) (m : ℕ) (B : PTm n) :
    Syn.subst σ (rate m B) = rate m (Syn.subst σ B) := by simp [rate]
@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (m : ℕ) (A B : PTm n) :
    Syn.subst σ (data m A B) = data m (Syn.subst σ A) (Syn.subst σ B) := by simp [data]

theorem raw_at (m : ℕ) (p A B : PTm n) : Γ ⊢[PRAAx] ap2 (rawF m) p (rawData A B) ≐ raw m p A B := by
  let x := rawData A B
  have c : Γ ⊢[PRAAx] ap2 (rawF m) p x ≐ raw m p (fstT x) (sndT x) := by
    simpa [rawF,ap2] using toPR_eq (Γ := Γ)
      (raw m (var 0) (fstT (var 1)) (sndT (var 1)) : PTm 2) ![p,x]
  exact c.eqTrans (by
    simpa only [subst_raw,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
        Prf.eqCongr (Γ := Γ) (raw m (var 0) (var 1) (var 2) : PTm 3)
          (σ := ![p,fstT x,sndT x]) (σ' := ![p,A,B])
          (fun i => by fin_cases i; exact .eqRefl _; exact fst_pair _ _; exact snd_pair _ _))

theorem raw_distance (m : ℕ) (p A B x : PTm n) (hs : Γ ⊢[PRAAx] source A B) : Γ ⊢[PRAAx]
    distanceBounded (raw m p A B) (ap2 (T m) p (TData m A B x)) (radius m B) (unit p) :=
  actual_prefix_distance m A B (requiredMesh m A B p) p x hs (le_refl _)

theorem raw_observations (m : ℕ) (p q A B x : PTm n) (hs : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] distanceBounded (raw m p A B) (raw m q A B) (rate m B*(unit p+unit q)) (unit p*unit q) := by
  let u := unit p
  let v := unit q
  let d := u*v
  let r := radius m B
  have hu := unit_positive (Γ := Γ) p
  have hv := unit_positive (Γ := Γ) q
  have hd := positive_product _ _ hu hv
  have a := distance_radius_mono _ _ _ _ (r*v) d hu hd (by unfold d; ipra_le 0) (raw_distance m p A B x hs)
  have b := point_at (T m) (TData m A B x) p q (GaussianStirlingAllOrderPanelPartsNames.name_regular m A B x hs)
  have c := distance_radius_mono _ _ _ _ (r*u) d hv hd (by unfold d; ipra_le 0)
    (distance_symmetric _ _ _ _ hv (raw_distance m q A B x hs))
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold u v r rate; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hd (distance_triangle_same _ _ _ _ _ _ hd a b) c)

theorem raw_regular (m : ℕ) (A B x : PTm n) (hs : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] regular (rawF m) (rate m B) (rawData A B) := by
  refine .allI (.allI ?_)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let a := Syn.shift (Syn.shift A)
  let b := Syn.shift (Syn.shift B)
  let c := Syn.shift (Syn.shift x)
  have h : Δ ⊢[PRAAx] source a b := by simpa [Δ,a,b,Fm.shift,Syn.shift] using hs.shift.shift
  have r := raw_observations m (var 1) (var 0) a b c h
  simpa [regular,a,b,c,Δ,Syn.shift,GaussianCoefficientNameBounds.unit,GaussianEuclideanPointDistance.unit] using
    distance_congr (raw_at m (var 1) a b).eqSymm (raw_at m (var 0) a b).eqSymm (.eqRefl _) (.eqRefl _) r

theorem name_regular (m : ℕ) (A B x : PTm n) (hs : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] pointCN (nameF m) (data m A B) :=
  GaussianFastValueCut.name_fast (rawF m) _ _ (raw_regular m A B x hs)

private theorem normalized_error (m : ℕ) (p A B x : PTm n) (hs : Γ ⊢[PRAAx] source A B) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (nameF m) p (data m A B)) (ap2 (T m) p (TData m A B x))
      (rate m B+one+radius m B) (unit p) := by
  have e := GaussianNameRingLaws.normalized_to_sample (rawF m) _ _ p (raw_regular m A B x hs)
  exact distance_triangle_same _ _ _ _ _ _ (unit_positive p)
    (distance_congr (.eqRefl _) (raw_at m p A B) (.eqRefl _) (.eqRefl _) e) (raw_distance m p A B x hs)

theorem original_improper_cross (m : ℕ) (A B x : PTm n) (hs : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] crossEquivalent (nameF m) (T m) (data m A B) (TData m A B x) := by
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (rate m B+one+radius m B)
    (name_regular m A B x hs) (GaussianStirlingAllOrderPanelPartsNames.name_regular m A B x hs)
  refine .allI ?_
  let a := Syn.shift A
  let b := Syn.shift B
  let c := Syn.shift x
  let Δ := Γ.map Fm.shift
  have h : Δ ⊢[PRAAx] source a b := by simpa [Δ,a,b,Fm.shift,Syn.shift] using hs.shift
  simpa [rawDiagonal,a,b,c,Δ,Syn.shift,GaussianCoefficientNameBounds.unit,GaussianEuclideanPointDistance.unit] using
    normalized_error m (var 0) a b c h

theorem actual_all_order_periodic_improper_closed (m : ℕ) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source (var 0) (var 1) ⟶
        pointCN (nameF m) (data m (var 0) (var 1)) ⋏
        crossEquivalent (nameF m) (T m) (data m (var 0) (var 1)) (TData m (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (.andI (name_regular m _ _ (var 2) Prf.hyp0) (original_improper_cross m _ _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderImproperName

import IPRADerivations.Analysis.GaussianDigammaBernoulliName
import IPRADerivations.Analysis.GaussianDigammaFirstBernoulliImproper

/-!
# The original digamma improper names at all fixed orders

The first weighted prefix is identified with the original digamma
and harmonic logarithm. Propagate that rate through the exact
subtractive recurrence, and independently normalize the literal
cofinal weighted folds.
-/

set_option autoImplicit false
set_option maxHeartbeats 1050000

namespace LeanProofs.IPRA.Analysis.GaussianDigammaBernoulliImproperName

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.PTm (num)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianDigammaBernoulliRecurrence (prefixAt)
open GaussianDigammaFirstBernoulliImproper (baseF baseData meshDemand base_regular original_base_rate)
open GaussianStirlingNames (source)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianFastValueCut (regular)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent point_at)
open GaussianValueNormalizerExtensionality (rawDiagonal)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def recurrenceF (m : ℕ) : PR 2 := GaussianDigammaBernoulliName.nameF baseF m

def recurrenceData (m : ℕ) (A B : PTm n) : PTm n :=
  GaussianDigammaBernoulliName.nameData m A B (baseData A B)

def mesh (m : ℕ) (A B p : PTm n) : PTm n :=
  GaussianDigammaBernoulliName.requiredMesh m A B p (meshDemand p A B)

def radius (m : ℕ) (A B : PTm n) : PTm n :=
  GaussianDigammaBernoulliName.radius m B (two*A+num 36)

theorem recurrence_regular (m : ℕ) (A B : PTm n) (hs : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] pointCN (recurrenceF m) (recurrenceData m A B) :=
  GaussianDigammaBernoulliName.name_regular baseF m A B _ (base_regular A B hs)

theorem actual_prefix_distance (m : ℕ) (A B Q p : PTm n)
    (hs : Γ ⊢[PRAAx] source A B) (hQ : Γ ⊢[PRAAx] le (mesh m A B p) Q) :
    Γ ⊢[PRAAx] distanceBounded (prefixAt m A B Q p)
      (ap2 (recurrenceF m) p (recurrenceData m A B)) (radius m A B) (unit p) := by
  have base := le_trans (GaussianDigammaBernoulliName.base_le_requiredMesh m A B p (meshDemand p A B)) hQ
  exact GaussianDigammaBernoulliName.prefix_distance baseF m A B Q p (baseData A B) (meshDemand p A B)
    (two*A+num 36) hs (base_regular A B hs) hQ (original_base_rate p A B Q hs base)

def raw (m : ℕ) (p A B : PTm n) : PTm n := prefixAt m A B (mesh m A B p) p
def rawF (m : ℕ) : PR 2 := PTm.toPR (raw m (var 0) (fstT (var 1)) (sndT (var 1)))
def rawData (A B : PTm n) : PTm n := pairT A B
def rate (m : ℕ) (A B : PTm n) : PTm n := radius m A B+one
def nameF (m : ℕ) : PR 2 := GaussianFastValueCut.nameF (rawF m)
def data (m : ℕ) (A B : PTm n) : PTm n := GaussianFastValueCut.nameData (rate m A B) (rawData A B)

@[simp] theorem subst_recurrenceData {l : ℕ} (σ : Fin n → PTm l) (m : ℕ) (A B : PTm n) :
    Syn.subst σ (recurrenceData m A B) = recurrenceData m (Syn.subst σ A) (Syn.subst σ B) := by
  simp [recurrenceData]

@[simp] theorem subst_raw {l : ℕ} (σ : Fin n → PTm l) (m : ℕ) (p A B : PTm n) :
    Syn.subst σ (raw m p A B) = raw m (Syn.subst σ p) (Syn.subst σ A) (Syn.subst σ B) := by simp [raw,mesh]
@[simp] theorem subst_rawData {l : ℕ} (σ : Fin n → PTm l) (A B : PTm n) :
    Syn.subst σ (rawData A B) = rawData (Syn.subst σ A) (Syn.subst σ B) := by simp [rawData]
@[simp] theorem subst_radius {l : ℕ} (σ : Fin n → PTm l) (m : ℕ) (A B : PTm n) :
    Syn.subst σ (radius m A B) = radius m (Syn.subst σ A) (Syn.subst σ B) := by simp [radius,two,one]
@[simp] theorem subst_rate {l : ℕ} (σ : Fin n → PTm l) (m : ℕ) (A B : PTm n) :
    Syn.subst σ (rate m A B) = rate m (Syn.subst σ A) (Syn.subst σ B) := by simp [rate,one]
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

theorem raw_distance (m : ℕ) (p A B : PTm n) (hs : Γ ⊢[PRAAx] source A B) : Γ ⊢[PRAAx]
    distanceBounded (raw m p A B) (ap2 (recurrenceF m) p (recurrenceData m A B)) (radius m A B) (unit p) :=
  actual_prefix_distance m A B (mesh m A B p) p hs (le_refl _)

theorem raw_observations (m : ℕ) (p q A B : PTm n) (hs : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] distanceBounded (raw m p A B) (raw m q A B) (rate m A B*(unit p+unit q)) (unit p*unit q) := by
  let u := unit p
  let v := unit q
  let d := u*v
  let r := radius m A B
  have hu := unit_positive (Γ := Γ) p
  have hv := unit_positive (Γ := Γ) q
  have hd := positive_product _ _ hu hv
  have a := distance_radius_mono _ _ _ _ (r*v) d hu hd (by unfold d; ipra_le 0) (raw_distance m p A B hs)
  have b := point_at (recurrenceF m) (recurrenceData m A B) p q (recurrence_regular m A B hs)
  have c := distance_radius_mono _ _ _ _ (r*u) d hv hd (by unfold d; ipra_le 0)
    (distance_symmetric _ _ _ _ hv (raw_distance m q A B hs))
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold u v r rate; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hd (distance_triangle_same _ _ _ _ _ _ hd a b) c)

theorem raw_regular (m : ℕ) (A B : PTm n) (hs : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] regular (rawF m) (rate m A B) (rawData A B) := by
  refine .allI (.allI ?_)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let a := Syn.shift (Syn.shift A)
  let b := Syn.shift (Syn.shift B)
  have h : Δ ⊢[PRAAx] source a b := by simpa [Δ,a,b,Fm.shift,Syn.shift] using hs.shift.shift
  have r := raw_observations m (var 1) (var 0) a b h
  simpa [regular,a,b,Δ,Syn.shift,GaussianCoefficientNameBounds.unit,GaussianEuclideanPointDistance.unit] using
    distance_congr (raw_at m (var 1) a b).eqSymm (raw_at m (var 0) a b).eqSymm (.eqRefl _) (.eqRefl _) r

theorem name_regular (m : ℕ) (A B : PTm n) (hs : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] pointCN (nameF m) (data m A B) :=
  GaussianFastValueCut.name_fast (rawF m) _ _ (raw_regular m A B hs)

private theorem normalized_error (m : ℕ) (p A B : PTm n) (hs : Γ ⊢[PRAAx] source A B) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (nameF m) p (data m A B)) (ap2 (recurrenceF m) p (recurrenceData m A B))
      (rate m A B+one+radius m A B) (unit p) := by
  have e := GaussianNameRingLaws.normalized_to_sample (rawF m) _ _ p (raw_regular m A B hs)
  exact distance_triangle_same _ _ _ _ _ _ (unit_positive p)
    (distance_congr (.eqRefl _) (raw_at m p A B) (.eqRefl _) (.eqRefl _) e) (raw_distance m p A B hs)

theorem original_improper_cross (m : ℕ) (A B : PTm n) (hs : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] crossEquivalent (nameF m) (recurrenceF m) (data m A B) (recurrenceData m A B) := by
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (rate m A B+one+radius m A B)
    (name_regular m A B hs) (recurrence_regular m A B hs)
  refine .allI ?_
  let a := Syn.shift A
  let b := Syn.shift B
  let Δ := Γ.map Fm.shift
  have h : Δ ⊢[PRAAx] source a b := by simpa [Δ,a,b,Fm.shift,Syn.shift] using hs.shift
  simpa [rawDiagonal,a,b,Δ,Syn.shift,GaussianCoefficientNameBounds.unit,GaussianEuclideanPointDistance.unit] using
    normalized_error m (var 0) a b h

theorem actual_original_all_order_digamma_improper_closed (m : ℕ) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (source (var 0) (var 1) ⟶
        pointCN (nameF m) (data m (var 0) (var 1)) ⋏
        crossEquivalent (nameF m) (recurrenceF m) (data m (var 0) (var 1)) (recurrenceData m (var 0) (var 1))) :=
  closeUniv 2 (.impI (.andI (name_regular m _ _ Prf.hyp0) (original_improper_cross m _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianDigammaBernoulliImproperName

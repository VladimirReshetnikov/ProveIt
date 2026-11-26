import IPRADerivations.Analysis.Trigonometry.MultipleAngles.GaussianSineMultipleAngleContinuity

/-!
# Regular named evaluation of the multiple-angle trace recurrence

The raw program evaluates the zero-safe recurrence on a genuine trace
observation. Its explicit continuity bound determines the precision of
the canonical name for this recurrence value.
-/

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace LeanProofs.IPRA.Analysis.GaussianSineTraceName

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (point_at)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianSineMultipleAngleContinuity (growth value_distance)
open GaussianSineMultipleAngleRecurrence (value)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def raw (f : PR 2) (p k x : PTm n) : PTm n := value (ap2 f p x) k
def rawData (k x : PTm n) : PTm n := pairT k x
def rawF (f : PR 2) : PR 2 := PTm.toPR (raw f (var 0) (fstT (var 1)) (sndT (var 1)) : PTm 2)
def modulus (f : PR 2) (k x : PTm n) : PTm n := growth (GaussianNameBounds.U f x) k
def nameF (f : PR 2) : PR 2 := GaussianFastValueCut.nameF (rawF f)
def data (f : PR 2) (k x : PTm n) : PTm n := GaussianFastValueCut.nameData (modulus f k x) (rawData k x)

@[simp] theorem subst_rawData {m : ℕ} (σ : Fin n → PTm m) (k x : PTm n) :
    Syn.subst σ (rawData k x) = rawData (Syn.subst σ k) (Syn.subst σ x) := by simp [rawData]
@[simp] theorem subst_modulus {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (k x : PTm n) :
    Syn.subst σ (modulus f k x) = modulus f (Syn.subst σ k) (Syn.subst σ x) := by simp [modulus]
@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (k x : PTm n) :
    Syn.subst σ (data f k x) = data f (Syn.subst σ k) (Syn.subst σ x) := by simp [data]

theorem raw_at (f : PR 2) (k p x : PTm n) : Γ ⊢[PRAAx] ap2 (rawF f) p (rawData k x) ≐ raw f p k x := by
  refine (show Γ ⊢[PRAAx] ap2 (rawF f) p (rawData k x) ≐ raw f p (fstT (rawData k x)) (sndT (rawData k x)) by
    have e := toPR_eq (Γ := Γ) (raw f (var 0) (fstT (var 1)) (sndT (var 1)) : PTm 2) ![p,rawData k x]
    simp only [raw,GaussianSineMultipleAngleRecurrence.subst_value,subst_ap2,subst_fstT,subst_sndT,
      Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] at e
    simpa only [raw,rawF,ap2] using e).eqTrans ?_
  exact congrSnd (congrAp2 GaussianSineMultipleAngleRecurrence.stateF (fst_pair k x)
    (congrAp2 f (.eqRefl p) (snd_pair k x)))

theorem raw_regular_at (f : PR 2) (k p q x : PTm n) (h : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (rawF f) p (rawData k x)) (ap2 (rawF f) q (rawData k x))
      (modulus f k x*(unit p+unit q)) (unit p*unit q) := by
  have hp := unit_positive (Γ := Γ) p
  have hq := unit_positive (Γ := Γ) q
  have d := value_distance (ap2 f p x) (ap2 f q x) (GaussianNameBounds.U f x) _ _ k (positive_product _ _ hp hq)
    (GaussianNameBounds.sample_bound f x p h) (GaussianNameBounds.sample_bound f x q h) (point_at f x p q h)
  exact distance_congr (raw_at f k p x).eqSymm (raw_at f k q x).eqSymm
    (by unfold modulus; ipra_ring) (.eqRefl _) d

theorem raw_regular (f : PR 2) (k x : PTm n) (h : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] GaussianFastValueCut.regular (rawF f) (modulus f k x) (rawData k x) := by
  refine .allI (.allI ?_)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] pointCN f (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,GaussianEuclideanDistanceName.subst_pointCN,Syn.shift] using h.shift.shift
  simpa only [GaussianFastValueCut.regular,Syn.shift,subst_modulus,subst_rawData] using
    raw_regular_at f (Syn.shift (Syn.shift k)) (var 1) (var 0) (Syn.shift (Syn.shift x)) hs

theorem name_regular (f : PR 2) (k x : PTm n) (h : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] pointCN (nameF f) (data f k x) :=
  GaussianFastValueCut.name_fast _ _ _ (raw_regular f k x h)

theorem sample_error (f : PR 2) (k p x : PTm n) (h : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f) p (data f k x)) (raw f p k x) (modulus f k x+one) (unit p) :=
  distance_congr (.eqRefl _) (raw_at f k p x) (.eqRefl _) (.eqRefl _)
    (GaussianNameRingLaws.normalized_to_sample _ _ _ p (raw_regular f k x h))

end LeanProofs.IPRA.Analysis.GaussianSineTraceName

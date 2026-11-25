import IPRADerivations.Analysis.GaussianDigammaBernoulliRecurrence

/-!
# Propagating the digamma improper approximation to higher orders

A checked first-order improper approximation anchors the exact
subtractive recurrence. Every higher named observation is tied
to the literal weighted prefix on the same mesh and cutoff.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianDigammaBernoulliName

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.PTm (num)
open ConciseIPRA.PTm (zero succ)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianDigammaBernoulliRecurrence
  (meshCost prefixAt weightedPrimitive stepRadius step_distance)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalPowerDifference (distance_refl_zero)
open GaussianRationalSyntheticDivision (qsub_congr)
open GaussianStirlingNames (source)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "subF" => GaussianNamedDifference.nameF
local notation "subData" => GaussianNamedDifference.data

def nameF (initial : PR 2) : ℕ → PR 2
  | 0 => initial
  | m+1 => subF constantF (nameF initial m)

def nameData : ℕ → PTm n → PTm n → PTm n → PTm n
  | 0,_,_,x => x
  | m+1,A,B,x => subData (weightedPrimitive m A B) (nameData m A B x)

def requiredMesh : ℕ → PTm n → PTm n → PTm n → PTm n → PTm n
  | 0,_,_,_,base => base
  | m+1,A,B,p,base => requiredMesh m A B p base+unit p*succ (meshCost m A B p)

def radius : ℕ → PTm n → PTm n → PTm n
  | 0,_,initial => initial
  | m+1,B,initial => stepRadius m B+(radius m B initial+num 6)

@[simp] theorem subst_nameData {l : ℕ} (σ : Fin n → PTm l) (m : ℕ) (A B x : PTm n) :
    Syn.subst σ (nameData m A B x) = nameData m (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ x) := by
  induction m with
  | zero => rfl
  | succ m ih => simp [nameData,ih]

@[simp] theorem subst_radius {l : ℕ} (σ : Fin n → PTm l) (m : ℕ) (B initial : PTm n) :
    Syn.subst σ (radius m B initial) = radius m (Syn.subst σ B) (Syn.subst σ initial) := by
  induction m with
  | zero => rfl
  | succ m ih => simp [radius,ih]

@[simp] theorem subst_requiredMesh {l : ℕ} (σ : Fin n → PTm l) (m : ℕ) (A B p base : PTm n) :
    Syn.subst σ (requiredMesh m A B p base) =
      requiredMesh m (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ p) (Syn.subst σ base) := by
  induction m with
  | zero => rfl
  | succ m ih => simp [requiredMesh,ih,meshCost]

theorem base_le_requiredMesh (m : ℕ) (A B p base : PTm n) :
    Γ ⊢[PRAAx] le base (requiredMesh m A B p base) := by
  induction m with
  | zero => exact le_refl base
  | succ m ih => exact le_trans ih (le_add_right _ _)

theorem name_regular (initial : PR 2) (m : ℕ) (A B x : PTm n)
    (h : Γ ⊢[PRAAx] pointCN initial x) :
    Γ ⊢[PRAAx] pointCN (nameF initial m) (nameData m A B x) := by
  induction m with
  | zero => exact h
  | succ m ih =>
    exact GaussianNamedDifference.name_regular _ _ _ _ (constant_regular _) ih

theorem prefix_distance (initial : PR 2) (m : ℕ) (A B Q p x base cost : PTm n)
    (hs : Γ ⊢[PRAAx] source A B) (hx : Γ ⊢[PRAAx] pointCN initial x)
    (hQ : Γ ⊢[PRAAx] le (requiredMesh m A B p base) Q)
    (hbase : Γ ⊢[PRAAx] distanceBounded (prefixAt 0 A B Q p) (ap2 initial p x) cost (unit p)) :
    Γ ⊢[PRAAx] distanceBounded (prefixAt m A B Q p)
      (ap2 (nameF initial m) p (nameData m A B x)) (radius m B cost) (unit p) := by
  induction m with
  | zero => exact hbase
  | succ m ih =>
    let U := requiredMesh m A B p base
    let R := radius m B cost
    let C := weightedPrimitive m A B
    let V := prefixAt m A B Q p
    let F := nameF initial m
    let X := nameData m A B x
    have hUp : Γ ⊢[PRAAx] le U Q := le_trans (le_add_right _ _) hQ
    have hMesh : Γ ⊢[PRAAx] le (unit p*succ (meshCost m A B p)) Q := le_trans (le_add_left _ _) hQ
    have hp := unit_positive (Γ := Γ) p
    have stepped := step_distance m A B Q p hs hMesh
    have prev := ih hUp
    have hF := name_regular initial m A B x hx
    have sr := GaussianNamedDifference.sample_error constantF F C X p (constant_regular C) hF
    have approximates := distance_congr (.eqRefl _)
      (qsub_congr (constant_at p C) (.eqRefl _)) (.eqRefl _) (.eqRefl _) sr
    have through := GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ hp
      (distance_refl_zero C (unit p) hp) prev
    have aligned := distance_congr (.eqRefl _) (.eqRefl _) (LeanProofs.IPRA.zero_add R) (.eqRefl _) through
    have result := distance_triangle_same _ _ _ _ _ _ hp aligned (distance_symmetric _ _ _ _ hp approximates)
    exact distance_triangle_same _ _ _ _ _ _ hp stepped result

end LeanProofs.IPRA.Analysis.GaussianDigammaBernoulliName

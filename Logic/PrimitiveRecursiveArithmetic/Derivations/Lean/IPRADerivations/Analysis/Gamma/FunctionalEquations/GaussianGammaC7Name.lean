import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaCanonicalExponent
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaEulerHead

/-!
# The original reciprocal Gamma constructor on a fixed disk

At cutoff 2R, the literal finite polynomial head multiplies the actual
exponential of the canonical exponent. The checked name operations compute
the needed retiming and return a regular name for the expression in C7.
The numerical disk bound below follows from the actual zeroth observation.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaC7Name

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaCanonicalExponent (source constantF constant_at constant_regular
  exponentialF exponentialData exponentialPoint exponential_regular)
open GaussianRationalHorner (qmul canonical)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalMetric (bounded)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def head (z R B : PTm n) : PTm n := GaussianGammaEulerHead.run z B (two*R)
def nameF : PR 2 := GaussianNameArithmetic.multiplyF constantF exponentialF
def data (z R B : PTm n) : PTm n :=
  GaussianNameArithmetic.multiplyData constantF exponentialF (head z R B) (exponentialData z R B)
def sample (p z R B : PTm n) : PTm n := ap2 nameF p (data z R B)
def samplePrecision (p z R B : PTm n) : PTm n := GaussianFastValueCut.exponent
  (GaussianNameArithmetic.multiplyModulus constantF exponentialF (head z R B) (exponentialData z R B)) p
def value (p z R B : PTm n) : PTm n := GaussianFastValueCut.recode
  (qmul (head z R B) (exponentialPoint (samplePrecision p z R B) z R B))
def diskBound (z R B : PTm n) : PTm n := GaussianNameBounds.U nameF (data z R B)

@[simp] theorem subst_head {m : ℕ} (σ : Fin n → PTm m) (z R B : PTm n) :
    Syn.subst σ (head z R B) = head (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) := by
  simp only [head,GaussianGammaEulerHead.run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> simp

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (z R B : PTm n) :
    Syn.subst σ (data z R B) = data (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) := by simp [data]

@[simp] theorem subst_sample {m : ℕ} (σ : Fin n → PTm m) (p z R B : PTm n) :
    Syn.subst σ (sample p z R B) = sample (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) := by
  simp [sample]

@[simp] theorem subst_diskBound {m : ℕ} (σ : Fin n → PTm m) (z R B : PTm n) :
    Syn.subst σ (diskBound z R B) = diskBound (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) := by simp [diskBound]

theorem sample_at (p z R B : PTm n) : Γ ⊢[PRAAx] sample p z R B ≐ value p z R B :=
  (GaussianNameArithmetic.multiply_at constantF exponentialF (head z R B) (exponentialData z R B) p).eqTrans
    (GaussianNameArithmetic.recode_congr (qmul_congr (constant_at _ _) (.eqRefl _)))

theorem sample_canonical (p z R B : PTm n) : Γ ⊢[PRAAx] canonical (sample p z R B) :=
  GaussianRationalHorner.canonical_congr (sample_at p z R B) (GaussianFastValueCut.recode_canonical _)

theorem name_regular (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx] pointCN nameF (data z R B) :=
  GaussianNameArithmetic.multiply_fast constantF exponentialF (head z R B) (exponentialData z R B)
    (constant_regular _) (exponential_regular z R B h)

theorem head_bound (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] bounded (head z R B) (R*pw (one+R) (two*R)) one :=
  GaussianGammaEulerHead.returned_head_bound _ _ _ _ h.andE₂.andE₁ h.andE₂.andE₂

theorem sample_bounded (p z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] bounded (sample p z R B) (diskBound z R B) one :=
  GaussianNameBounds.sample_bound nameF (data z R B) p (name_regular z R B h)

def output (p z R B : PTm n) : PTm n := pairT (sample p z R B) (pairT (head z R B) (diskBound z R B))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (p z R B : PTm n) : PTm n := ConciseIPRA.PTm.app outputF ![p,z,R,B]

@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (p z R B : PTm n) :
    Syn.subst σ (output p z R B) = output (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) := by
  simp [output]

theorem program_at (p z R B : PTm n) : Γ ⊢[PRAAx] run p z R B ≐ output p z R B := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![p,z,R,B]

theorem returned_sample (p z R B : PTm n) : Γ ⊢[PRAAx] fstT (run p z R B) ≐ value p z R B :=
  (congrFst (program_at p z R B)).eqTrans ((fst_pair _ _).eqTrans (sample_at p z R B))

theorem returned_head_and_radius (p z R B : PTm n) :
    Γ ⊢[PRAAx] sndT (run p z R B) ≐ pairT (head z R B) (diskBound z R B) :=
  (congrSnd (program_at p z R B)).eqTrans (snd_pair _ _)

theorem original_C7_regular_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) (var 2) ⟶ pointCN nameF (data (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (name_regular _ _ _ Prf.hyp0))

theorem actual_C7_returned_sample_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (fstT (run (var 0) (var 1) (var 2) (var 3)) ≐ value (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (returned_sample _ _ _ _)

theorem returned_bounded (p z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] bounded (fstT (run p z R B)) (sndT (sndT (run p z R B))) one :=
  GaussianRationalReciprocal.bound_congr
    ((congrFst (program_at p z R B)).eqTrans (fst_pair _ _)).eqSymm
    ((congrSnd (returned_head_and_radius p z R B)).eqTrans (snd_pair _ _)).eqSymm (.eqRefl _)
    (sample_bounded p z R B h)

theorem actual_C7_returned_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 1) (var 2) (var 3) ⟶ bounded (fstT (run (var 0) (var 1) (var 2) (var 3)))
      (sndT (sndT (run (var 0) (var 1) (var 2) (var 3)))) one) :=
  closeUniv 4 (.impI (returned_bounded _ _ _ _ Prf.hyp0))

theorem actual_C7_head_and_radius_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (sndT (run (var 0) (var 1) (var 2) (var 3)) ≐ pairT (head (var 1) (var 2) (var 3))
      (diskBound (var 1) (var 2) (var 3))) :=
  closeUniv 4 (returned_head_and_radius _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaC7Name

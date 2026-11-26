import IPRADerivations.Analysis.Exponential.GaussianSignedNameExponentialOrder
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianRationalPowerDifference
import IPRADerivations.Analysis.Names.GaussianNameArithmetic

/-!
# The original Barnes canonical factor

The polynomial term uses an integer power of (1+z/k).
The exponential uses the literal quadratic correction and a common
disk for its argument. Every positive index is admitted on the disk,
including the indices where the polynomial term vanishes.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFactor

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus multiply_at multiply_fast)
open GaussianRationalHorner (ofGaussian ofGaussian_represents qadd qmul qzero qmul_canonical positive_product)
open GaussianRationalMetric (bounded bounded_of_cleared qsub)
open GaussianRationalReciprocal (bound_congr bounded_sum bounded_product bounded_difference power powerF power_succ qone_bounded)
open GaussianRationalSyntheticDivision (qone qmul_congr qmul_zero_left qmul_zero_right)
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (pred)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (z R B k : PTm n) : Fm PTm n :=
  le one B ⋏ (le one k ⋏ ComplexLogarithmRemainder.bounded z (R*B))

def base (z B k : PTm n) : PTm n := qadd qone (ofGaussian z (B*k))

def powerValue (z B k : PTm n) : PTm n := power (base z B k) k

def correction (z B k : PTm n) : PTm n :=
  qsub (qmul (ofGaussian z B) (ofGaussian z (two*(B*k)))) (ofGaussian z B)

def exponentRadius (R : PTm n) : PTm n := R+R*R

abbrev exponentialF : PR 2 := GaussianRadiusExponentialName.nameF constantF

def exponentialData (z R B k : PTm n) : PTm n :=
  GaussianRadiusExponentialName.data (exponentRadius R) (correction z B k)

def nameF : PR 2 := multiplyF constantF exponentialF

def data (z R B k : PTm n) : PTm n :=
  multiplyData constantF exponentialF (powerValue z B k) (exponentialData z R B k)

def clock (p z R B k : PTm n) : PTm n := GaussianFastValueCut.exponent
  (multiplyModulus constantF exponentialF (powerValue z B k) (exponentialData z R B k)) p

def cap (R k : PTm n) : PTm n :=
  pw (R+one) k*GaussianRadiusExponentialLipschitzRate.factor (exponentRadius R)

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (z R B k : PTm n) :
    (source z R B k).subst σ = source (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ k) := by
  simp [source,one]

@[simp] theorem subst_base {m : ℕ} (σ : Fin n → PTm m) (z B k : PTm n) :
    Syn.subst σ (base z B k) = base (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ k) := by simp [base]

@[simp] theorem subst_powerValue {m : ℕ} (σ : Fin n → PTm m) (z B k : PTm n) :
    Syn.subst σ (powerValue z B k) = powerValue (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ k) := by simp [powerValue]

@[simp] theorem subst_correction {m : ℕ} (σ : Fin n → PTm m) (z B k : PTm n) :
    Syn.subst σ (correction z B k) = correction (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ k) := by
  simp [correction,two]

@[simp] theorem subst_exponentialData {m : ℕ} (σ : Fin n → PTm m) (z R B k : PTm n) :
    Syn.subst σ (exponentialData z R B k) =
      exponentialData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ k) := by
  simp [exponentialData,exponentRadius]

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (z R B k : PTm n) :
    Syn.subst σ (data z R B k) = data (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ k) := by
  simp [data]

@[simp] theorem subst_cap {m : ℕ} (σ : Fin n → PTm m) (R k : PTm n) :
    Syn.subst σ (cap R k) = cap (Syn.subst σ R) (Syn.subst σ k) := by
  simp [cap,exponentRadius,one]

private theorem fraction_bound (z R B D : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hD : Γ ⊢[PRAAx] le B D) (h : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) :
    Γ ⊢[PRAAx] bounded (ofGaussian z D) R one := by
  have pos := le_trans hB hD
  have disk := ComplexLogarithmRemainder.bounded_mono h
    (le_congr (mul_comm B R) (mul_comm D R) (mul_le_mul_right R hD))
  exact bounded_of_cleared _ _ _ _ _ pos (le_refl one) (ofGaussian_represents _ _ pos)
    (le_congr (by ipra_ring) (by ipra_ring) disk)

private theorem denominator_growth (B k : PTm n) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] le B (B*k) :=
  le_congr (one_mul B) (mul_comm k B) (mul_le_mul_right B hk)

theorem base_bound (z R B k : PTm n) (h : Γ ⊢[PRAAx] source z R B k) :
    Γ ⊢[PRAAx] bounded (base z B k) (R+one) one := by
  have r := fraction_bound z R B (B*k) h.andE₁ (denominator_growth B k h.andE₂.andE₁) h.andE₂.andE₂
  exact bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring)
    (bounded_sum qone (ofGaussian z (B*k)) one one R one (le_refl one) (le_refl one) qone_bounded r)

theorem correction_bound (z R B k : PTm n) (h : Γ ⊢[PRAAx] source z R B k) :
    Γ ⊢[PRAAx] bounded (correction z B k) (exponentRadius R) one := by
  let a := ofGaussian z B
  let b := ofGaussian z (two*(B*k))
  have grow := le_trans (denominator_growth B k h.andE₂.andE₁)
    (le_congr (one_mul (B*k)) (.eqRefl _) (mul_le_mul_right (B*k) (le_succ_self one)))
  have ha := fraction_bound z R B B h.andE₁ (le_refl _) h.andE₂.andE₂
  have hb := fraction_bound z R B (two*(B*k)) h.andE₁ grow h.andE₂.andE₂
  have hp := bounded_product a b R one R one (le_refl one) (le_refl one) ha hb
  exact bound_congr (.eqRefl _) (by unfold exponentRadius; ipra_ring) (by ipra_ring)
    (bounded_difference (qmul a b) a (R*R) (one*one) R one
      (positive_product _ _ (le_refl one) (le_refl one)) (le_refl one) hp ha)

theorem exponential_input (z R B k : PTm n) (h : Γ ⊢[PRAAx] source z R B k) :
    Γ ⊢[PRAAx] GaussianRadiusExponentialName.input constantF (exponentRadius R) (correction z B k) :=
  GaussianSignedNameExponentialOrder.constant_input _ _ (correction_bound z R B k h)

theorem regular (z R B k : PTm n) (h : Γ ⊢[PRAAx] source z R B k) :
    Γ ⊢[PRAAx] pointCN nameF (data z R B k) :=
  multiply_fast constantF exponentialF _ _ (constant_regular _)
    (GaussianRadiusExponentialName.name_regular _ _ _ (exponential_input z R B k h))

theorem sample_at (p z R B k : PTm n) :
    Γ ⊢[PRAAx] ap2 nameF p (data z R B k) ≐
      qmul (powerValue z B k) (ap2 exponentialF (clock p z R B k) (exponentialData z R B k)) := by
  let a := powerValue z B k
  let x := exponentialData z R B k
  let s := clock p z R B k
  have e := multiply_at (Γ := Γ) constantF exponentialF a x p
  exact e.eqTrans ((GaussianExponentialReference.recode_fixed _ (qmul_canonical _ _)).eqTrans
    (qmul_congr (constant_at s a) (.eqRefl _)))

theorem sample_bound (p z R B k : PTm n) (h : Γ ⊢[PRAAx] source z R B k) :
    Γ ⊢[PRAAx] bounded (ap2 nameF p (data z R B k)) (cap R k) one := by
  let S := exponentRadius R
  let x := correction z B k
  let s := clock p z R B k
  let q := GaussianRadiusExponentialName.query constantF S s x
  have b := GaussianPositiveExponentialMajorant.disk_bound q S (GaussianRadiusExponentialName.index S s)
    (GaussianRadiusExponentialName.query_bound constantF S x s (exponential_input z R B k h))
  have exp := bound_congr (GaussianRadiusExponentialName.sample_at constantF S s x).eqSymm (.eqRefl _) (.eqRefl _) b
  have poly := GaussianRationalPowerDifference.bounded_power_integer (base z B k) (R+one) k (base_bound z R B k h)
  exact bound_congr (sample_at p z R B k).eqSymm (.eqRefl _) (by ipra_ring)
    (bounded_product _ _ _ one _ one (le_refl one) (le_refl one) poly exp)

theorem zero_sample (p z R B k : PTm n) (hk : Γ ⊢[PRAAx] le one k)
    (h : Γ ⊢[PRAAx] base z B k ≐ qzero) : Γ ⊢[PRAAx] ap2 nameF p (data z R B k) ≐ qzero := by
  have e : Γ ⊢[PRAAx] k ≐ succ (pred k) := AnalyticNumberTheory.PNTStageStep.pos_of_one_le hk
  have power_zero : Γ ⊢[PRAAx] powerValue z B k ≐ qzero :=
    (congrAp2 powerF e h).eqTrans ((power_succ qzero (pred k)).eqTrans (qmul_zero_right _))
  exact (sample_at p z R B k).eqTrans ((qmul_congr power_zero (.eqRefl _)).eqTrans (qmul_zero_left _))

theorem actual_original_Barnes_factor_regular_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (source (var 0) (var 1) (var 2) (var 3) ⟶ pointCN nameF (data (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (regular _ _ _ _ Prf.hyp0))

theorem actual_original_Barnes_factor_zero_sample_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (le one (var 4) ⟶ (base (var 1) (var 3) (var 4) ≐ qzero) ⟶
        ap2 nameF (var 0) (data (var 1) (var 2) (var 3) (var 4)) ≐ qzero) :=
  closeUniv 5 (.impI (.impI (zero_sample _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFactor

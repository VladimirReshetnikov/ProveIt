import IPRADerivations.Analysis.GaussianGammaEulerRationalLogHead
import IPRADerivations.Analysis.GaussianGammaEulerRationalLogPower
import IPRADerivations.Analysis.GaussianGammaEulerRationalLogOrder

/-!
# Weighted convexity of the actual finite Euler logarithm

The Euler power contribution is affine, so the weighted logarithm
inequality is exactly the corresponding inequality for the reciprocal head.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianGammaEulerRationalLogConvexity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaEulerRationalHeadConvexity (weight barycenter)
open GaussianGammaEulerRationalLog (nameF data name_regular powerF powerData power_regular headLogData head_log_source)
open GaussianGammaEulerRationalLogOrder (add_order add_interleave order_refl)
open GaussianGammaEulerRationalLogPower (weighted_power_balance)
open GaussianNameArithmetic (addF addData add_fast multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans cross_symm)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianRationalHorner (positive_product)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "S" => GaussianNaturalScaleProductName.productF
local notation "sd" => GaussianNaturalScaleProductName.productData
local notation "L" => GaussianPositiveRationalLogarithm.logF
local notation "Q" => S nameF
local notation "H" => S L
local notation "P" => S powerF

def centerData (N a d b r s : PTm n) : PTm n :=
  sd nameF (weight r s) (data N (barycenter a d r s) (weight r s*b))
def weightedData (N a d b r s : PTm n) : PTm n :=
  addData (sd nameF (succ r) (data N a b)) (sd nameF s (data N d b))
def centerPowerData (N a d b r s : PTm n) : PTm n :=
  sd powerF (weight r s) (powerData N (barycenter a d r s) (weight r s*b))
def centerHeadData (N a d b r s : PTm n) : PTm n :=
  sd L (weight r s) (headLogData N (barycenter a d r s) (weight r s*b))
def weightedHeadData (N a d b r s : PTm n) : PTm n :=
  addData (sd L (succ r) (headLogData N a b)) (sd L s (headLogData N d b))

@[simp] theorem subst_centerData {m : ℕ} (σ : Fin n → PTm m) (N a d b r s : PTm n) :
    Syn.subst σ (centerData N a d b r s) =
      centerData (Syn.subst σ N) (Syn.subst σ a) (Syn.subst σ d) (Syn.subst σ b) (Syn.subst σ r) (Syn.subst σ s) :=
  by simp [centerData,weight,barycenter]
@[simp] theorem subst_weightedData {m : ℕ} (σ : Fin n → PTm m) (N a d b r s : PTm n) :
    Syn.subst σ (weightedData N a d b r s) =
      weightedData (Syn.subst σ N) (Syn.subst σ a) (Syn.subst σ d) (Syn.subst σ b) (Syn.subst σ r) (Syn.subst σ s) :=
  by simp [weightedData]

theorem center_positive (a d r s : PTm n) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] le one (barycenter a d r s) :=
  le_trans (positive_product _ _ (zero_lt_succ r) ha) (le_add_right _ _)

theorem center_denominator_positive (b r s : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] le one (weight r s*b) :=
  positive_product _ _ (zero_lt_succ (r+s)) hb

theorem scaled_regular (f : PR 2) (i x : PTm n) (h : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] pointCN (S f) (sd f i x) :=
  multiply_fast constantF f _ _ (constant_regular _) h

theorem scaled_log_split (N a b i : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] crossEquivalent Q (addF P H)
      (sd nameF i (data N a b)) (addData (sd powerF i (powerData N a b)) (sd L i (headLogData N a b))) :=
  GaussianNameRingLaws.distributive constantF powerF L _ _ _
    (constant_regular _) (power_regular N a b hN)
    (GaussianPositiveRationalLogarithm.name_regular _ _ (head_log_source N a b ha hb))

private theorem endpoint_split (N a d b r s : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (ha : Γ ⊢[PRAAx] le one a) (hd : Γ ⊢[PRAAx] le one d) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] crossEquivalent (addF Q Q) (addF (addF P P) (addF H H)) (weightedData N a d b r s)
      (addData (addData (sd powerF (succ r) (powerData N a b)) (sd powerF s (powerData N d b)))
        (weightedHeadData N a d b r s)) := by
  let rP := sd powerF (succ r) (powerData N a b)
  let sP := sd powerF s (powerData N d b)
  let rH := sd L (succ r) (headLogData N a b)
  let sH := sd L s (headLogData N d b)
  have pa := scaled_regular powerF (succ r) (powerData N a b) (power_regular N a b hN)
  have pd := scaled_regular powerF s (powerData N d b) (power_regular N d b hN)
  have la := scaled_regular L (succ r) (headLogData N a b)
    (GaussianPositiveRationalLogarithm.name_regular _ _ (head_log_source N a b ha hb))
  have ld := scaled_regular L s (headLogData N d b)
    (GaussianPositiveRationalLogarithm.name_regular _ _ (head_log_source N d b hd hb))
  have first := add_cross Q (addF P H) Q (addF P H) (sd nameF (succ r) (data N a b)) (addData rP rH)
    (sd nameF s (data N d b)) (addData sP sH)
    (scaled_regular _ _ _ (name_regular N a b hN ha hb)) (add_fast _ _ _ _ pa la)
    (scaled_regular _ _ _ (name_regular N d b hN hd hb)) (add_fast _ _ _ _ pd ld)
    (scaled_log_split N a b (succ r) hN ha hb) (scaled_log_split N d b s hN hd hb)
  exact cross_trans _ _ _ _ _ _ first (add_interleave P H P H rP rH sP sH pa la pd ld)

theorem weighted_convexity_of_head_order (N a d b r s : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (ha : Γ ⊢[PRAAx] le one a) (hd : Γ ⊢[PRAAx] le one d) (hb : Γ ⊢[PRAAx] le one b)
    (head : Γ ⊢[PRAAx] realOrder H (addF H H) (centerHeadData N a d b r s) (weightedHeadData N a d b r s)) :
    Γ ⊢[PRAAx] realOrder Q (addF Q Q) (centerData N a d b r s) (weightedData N a d b r s) := by
  let W := weight r s
  let A := barycenter a d r s
  let u := centerPowerData N a d b r s
  let v := centerHeadData N a d b r s
  let rhs := weightedHeadData N a d b r s
  let x := sd powerF (succ r) (powerData N a b)
  let y := sd powerF s (powerData N d b)
  have pa := scaled_regular powerF (succ r) (powerData N a b) (power_regular N a b hN)
  have pd := scaled_regular powerF s (powerData N d b) (power_regular N d b hN)
  have pc := scaled_regular powerF W (powerData N A (W*b)) (power_regular N A (W*b) hN)
  have la := scaled_regular L (succ r) (headLogData N a b)
    (GaussianPositiveRationalLogarithm.name_regular _ _ (head_log_source N a b ha hb))
  have ld := scaled_regular L s (headLogData N d b)
    (GaussianPositiveRationalLogarithm.name_regular _ _ (head_log_source N d b hd hb))
  have headReg : Γ ⊢[PRAAx] pointCN (addF H H) rhs := add_fast _ _ _ _ la ld
  have split := endpoint_split N a d b r s hN ha hd hb
  have remove := add_cross (addF P P) P (addF H H) (addF H H) (addData x y) u rhs rhs
    (add_fast _ _ _ _ pa pd) pc headReg headReg (weighted_power_balance N a d b r s hN hb) (cross_refl _ _ headReg)
  have endpoint := cross_trans _ _ _ _ _ _ split remove
  have center := scaled_log_split N A (W*b) W hN (center_positive a d r s ha) (center_denominator_positive b r s hb)
  have ordered := add_order P P H (addF H H) u u v rhs (order_refl P u pc) head
  exact GaussianNamedRealOrderTransport.transport Q (addF P H) (addF P (addF H H)) (addF Q Q)
    (centerData N a d b r s) (addData u v) (addData u rhs) (weightedData N a d b r s)
    center (cross_symm _ _ _ _ endpoint) ordered

theorem weighted_convexity (N a d b r s : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (ha : Γ ⊢[PRAAx] le one a) (hd : Γ ⊢[PRAAx] le one d) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] realOrder Q (addF Q Q) (centerData N a d b r s) (weightedData N a d b r s) :=
  weighted_convexity_of_head_order N a d b r s hN ha hd hb
    (GaussianGammaEulerRationalLogHead.weighted_head_log_order N a d b r s ha hd hb)

theorem actual_finite_Euler_log_weighted_convexity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((le one (var 0) ⋏ (le one (var 1) ⋏ (le one (var 2) ⋏ le one (var 3)))) ⟶
      realOrder Q (addF Q Q)
        (centerData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
        (weightedData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))) :=
  closeUniv 6 (.impI (weighted_convexity _ _ _ _ _ _
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaEulerRationalLogConvexity

import IPRADerivations.Analysis.Gamma.EulerProducts.Convexity.GaussianGammaEulerMidpointLogHeadGap

/-!
# Quantitative midpoint log convexity of the actual finite Euler names

The affine power terms cancel at the midpoint while the reciprocal
head retains its positive rational margin.
-/

set_option autoImplicit false
set_option maxHeartbeats 1250000

namespace LeanProofs.IPRA.Analysis.GaussianGammaEulerMidpointLogGap

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaEulerMidpointLogHeadGap (margin head_log_order fraction_congr)
open GaussianGammaEulerRationalHeadConvexity (weight barycenter)
open GaussianGammaEulerRationalLog (nameF data name_regular powerF powerData power_regular headLogData head_log_source)
open GaussianGammaEulerRationalLogConvexity (scaled_regular scaled_log_split)
open GaussianGammaEulerRationalLogOrder (add_order order_refl add_interleave)
open GaussianGammaEulerRationalLogPower (scaled_power_cross weighted_power_balance positive_power_cross positivePowerF positivePowerData)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNaturalScaleProductName (productF productData)
open GaussianPositiveRationalLogarithm (logF fraction)
open GaussianRationalHorner (positive_product)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "P" => productF powerF
local notation "H" => productF logF
local notation "E" => productF nameF
local notation "C" => constantF

def centerData (N a d b : PTm n) : PTm n :=
  addData (margin a d) (productData nameF two (data N (a+d) (two*b)))
def weightedData (N a d b : PTm n) : PTm n := addData (data N a b) (data N d b)

@[simp] theorem subst_centerData {m : ℕ} (σ : Fin n → PTm m) (N a d b : PTm n) :
    Syn.subst σ (centerData N a d b) = centerData (Syn.subst σ N) (Syn.subst σ a) (Syn.subst σ d) (Syn.subst σ b) := by
  simp [centerData]
@[simp] theorem subst_weightedData {m : ℕ} (σ : Fin n → PTm m) (N a d b : PTm n) :
    Syn.subst σ (weightedData N a d b) = weightedData (Syn.subst σ N) (Syn.subst σ a) (Syn.subst σ d) (Syn.subst σ b) := by
  simp [weightedData]

private theorem scale_one (N a b : PTm n) (hN : Γ ⊢[PRAAx] le one N) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] crossEquivalent P powerF (productData powerF one (powerData N a b)) (powerData N a b) := by
  have e := fraction_congr (a := one*a) (c := a) (b := b) (d := b) (Γ := Γ) (by ipra_ring) (.eqRefl _)
  let L := GaussianGammaFiniteApproximantName.logF
  have hx := GaussianGammaFiniteApproximantName.log_regular N hN
  have middle := GaussianGammaAdjacentCutoff.multiply_cross C C L L (fraction (one*a) b) (fraction a b) N N
    (constant_regular _) (constant_regular _) hx hx
    (GaussianGammaWeierstrassApproximant.constant_data_cross _ _ e) (cross_refl _ _ hx)
  exact cross_trans _ _ _ _ _ _ (scaled_power_cross N a b one hN hb)
    (cross_trans _ _ _ _ _ _ middle (cross_symm _ _ _ _ (positive_power_cross N a b hN hb)))

private theorem power_data_congr (N k l a b c d : PTm n) (h : Γ ⊢[PRAAx] k ≐ l)
    (e : Γ ⊢[PRAAx] a ≐ c) (f : Γ ⊢[PRAAx] b ≐ d) :
    Γ ⊢[PRAAx] productData powerF k (powerData N a b) ≐ productData powerF l (powerData N c d) := by
  simpa only [GaussianNaturalScaleProductName.subst_productData,GaussianGammaEulerRationalLog.subst_powerData,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx)
      (productData powerF (var 0) (powerData (var 1) (var 2) (var 3)) : PTm 4)
      (σ := ![k,N,a,b]) (σ' := ![l,N,c,d]) (fun i => by fin_cases i; exact h; exact .eqRefl N; exact e; exact f)

theorem midpoint_power_balance (N a d b : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] crossEquivalent (addF powerF powerF) P
      (addData (powerData N a b) (powerData N d b)) (productData powerF two (powerData N (a+d) (two*b))) := by
  let x := powerData N a b
  let y := powerData N d b
  let X := productData powerF one x
  let Y := productData powerF one y
  let j : PTm n := weight zero one
  have px := power_regular N a b hN
  have py := power_regular N d b hN
  have l := scale_one N a b hN hb
  have r := scale_one N d b hN hb
  have sums := add_cross powerF P powerF P x X y Y px (scaled_regular powerF one x px) py (scaled_regular powerF one y py)
    (cross_symm _ _ _ _ l) (cross_symm _ _ _ _ r)
  have law := weighted_power_balance N a d b zero one hN hb
  have e : Γ ⊢[PRAAx] j ≐ two := by dsimp [j,weight]; ipra_ring
  have f : Γ ⊢[PRAAx] barycenter a d zero one ≐ a+d := by unfold barycenter; ipra_ring
  have moved := GaussianGammaCompactCutoffAlignment.cross_data_congr (addF P P) P _ _ _ _ (.eqRefl _)
    (power_data_congr _ _ _ _ _ _ _ e f (congrMul e (.eqRefl _))) law
  exact cross_trans _ _ _ _ _ _ sums moved

private theorem swap_first (F G J : PR 2) (x y z : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN F x) (hg : Γ ⊢[PRAAx] pointCN G y) (hh : Γ ⊢[PRAAx] pointCN J z) :
    Γ ⊢[PRAAx] crossEquivalent (addF F (addF G J)) (addF G (addF F J))
      (addData x (addData y z)) (addData y (addData x z)) := by
  have a := cross_symm _ _ _ _ (GaussianNameRingLaws.add_associative F G J x y z hf hg hh)
  have b := add_cross (addF F G) (addF G F) J J _ _ z z
    (add_fast _ _ _ _ hf hg) (add_fast _ _ _ _ hg hf) hh hh
    (GaussianNameRingLaws.add_commutative F G x y hf hg) (cross_refl _ _ hh)
  have c := GaussianNameRingLaws.add_associative G F J y x z hg hf hh
  exact cross_trans _ _ _ _ _ _ a (cross_trans _ _ _ _ _ _ b c)

theorem midpoint_order (N a d b : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (ha : Γ ⊢[PRAAx] le one a) (hd : Γ ⊢[PRAAx] le one d) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] realOrder (addF C E) (addF nameF nameF) (centerData N a d b) (weightedData N a d b) := by
  let c := margin a d
  let A := a+d
  let B := two*b
  let xf := powerData N a b
  let yf := powerData N d b
  let xh := headLogData N a b
  let yh := headLogData N d b
  let zp := productData powerF two (powerData N A B)
  let zh := productData logF two (headLogData N A B)
  let z := productData nameF two (data N A B)
  have hA := le_trans ha (le_add_right a d)
  have hB := positive_product _ _ RationalAlgebra.two_positive hb
  have hc := constant_regular (Γ := Γ) c
  have hxf := power_regular N a b hN
  have hyf := power_regular N d b hN
  have hxh := GaussianPositiveRationalLogarithm.name_regular _ _ (head_log_source N a b ha hb)
  have hyh := GaussianPositiveRationalLogarithm.name_regular _ _ (head_log_source N d b hd hb)
  have hzp := scaled_regular powerF two (powerData N A B) (power_regular N A B hN)
  have hzh := scaled_regular logF two (headLogData N A B) (GaussianPositiveRationalLogarithm.name_regular _ _ (head_log_source N A B hA hB))
  have hz := scaled_regular nameF two (data N A B) (name_regular N A B hN hA hB)
  have hl := add_cross C C E (addF P H) c c z (addData zp zh) hc hc hz
    (add_fast _ _ _ _ hzp hzh) (cross_refl _ _ hc) (scaled_log_split N A B two hN hA hB)
  have left := cross_trans _ _ _ _ _ _ hl (swap_first C P H c zp zh hc hzp hzh)
  have r₁ := add_interleave powerF logF powerF logF xf xh yf yh hxf hxh hyf hyh
  have hsum := add_fast logF logF xh yh hxh hyh
  have r₂ := add_cross (addF powerF powerF) P (addF logF logF) (addF logF logF)
    (addData xf yf) zp (addData xh yh) (addData xh yh) (add_fast _ _ _ _ hxf hyf) hzp hsum hsum
    (midpoint_power_balance N a d b hN hb) (cross_refl _ _ hsum)
  have right := cross_trans _ _ _ _ _ _ r₁ r₂
  have mid := add_order P P (addF C H) (addF logF logF) zp zp (addData c zh) (addData xh yh)
    (order_refl _ _ hzp) (head_log_order N a d b ha hd hb)
  exact GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _ left (cross_symm _ _ _ _ right) mid

end LeanProofs.IPRA.Analysis.GaussianGammaEulerMidpointLogGap

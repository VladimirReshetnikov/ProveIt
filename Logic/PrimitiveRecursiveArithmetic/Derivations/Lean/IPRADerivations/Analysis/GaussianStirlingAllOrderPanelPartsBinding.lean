import IPRADerivations.Analysis.GaussianStirlingAllOrderPanelPartsNames
import IPRADerivations.Analysis.GaussianStirlingAllOrderPowerIntegralCofinal

/-!
# Binding every actual centered Bernoulli prefix to its original value

The induction is on the externally fixed order. Each internal query
uses the same cofinal cutoff and a single actual mesh, with a finite
term that dominates all mesh requirements up to the chosen order.
The induction operates on explicit iPRA distance judgments.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPanelPartsBinding

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianStirlingNames (source)
open GaussianStirlingGlobalBounds (steps remainderF remainderData remainder_regular)
open GaussianStirlingAllOrderFirstPanelPrefix (halfPrefix rowClock)
open GaussianStirlingAllOrderPanelPartsNames (nameF nameData name_regular initial derivativeRatio weightedPrimitive constantCap
  fixed_product_distance normalized_product_error difference_error)
open GaussianStirlingAllOrderPanelPartsSolve (estimate ratio embed_sub finite_solve_distance)
open GaussianStirlingAllOrderPanelPartsOuterFold (panelPrefix massPrefix)
open GaussianStirlingAllOrderPanelPartsRecurrence (errorCoefficient)
open GaussianStirlingAllOrderReciprocalWeightError (power)
open GaussianStirlingAllOrderPanelDerivative (signedMean)
open GaussianStirlingAllOrderPowerIntegralCofinal (cofinal_mass_distance)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianRationalPowerDifference (distance_refl_zero)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open RationalArithmetic (multiply)
open RationalAlgebra (multiply_congr multiply_associative multiply_commutative)
open RationalGaussianEmbedding (embed embed_multiply)
open RationalGaussianRealPart (embed_congr)
open RationalSumConstants (multiply_one_right)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)
local notation "subF" => GaussianNamedDifference.nameF
local notation "subData" => GaussianNamedDifference.data

def recurrenceCost (m : ℕ) (A B p : PTm n) : PTm n :=
  steps p*errorCoefficient (m+1) (2*m+2) (A+B*steps p) B

def requiredMesh : ℕ → PTm n → PTm n → PTm n → PTm n
  | 0,A,B,p => unit (rowClock A B (steps p) p)
  | m+1,A,B,p => requiredMesh m A B p+unit p*succ (recurrenceCost m A B p)

def prefixAt (m : ℕ) (A B Q p : PTm n) : PTm n := embed (panelPrefix m (2*m+1) A B (B*Q) (steps p))

def meanPoint (m : ℕ) : PTm n := embed (signedMean (m+1))

def radius : ℕ → PTm n → PTm n
  | 0,_ => constantCap initial*num 51+(constantCap initial+one)
  | m+1,B =>
    let c := constantCap (derivativeRatio m)
    let u := constantCap (meanPoint m)*(power (2*m+2) B+one)
    one+(c*(u+radius m B+num 6)+(c+one))

@[simp] theorem subst_recurrenceCost {l : ℕ} (σ : Fin n → PTm l) (m : ℕ) (A B p : PTm n) :
    Syn.subst σ (recurrenceCost m A B p) = recurrenceCost m (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ p) :=
  by simp [recurrenceCost]
@[simp] theorem subst_requiredMesh {l : ℕ} (σ : Fin n → PTm l) (m : ℕ) (A B p : PTm n) :
    Syn.subst σ (requiredMesh m A B p) = requiredMesh m (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ p) := by
  induction m with
  | zero => simp [requiredMesh]
  | succ m ih => simp [requiredMesh,ih]
@[simp] theorem subst_prefixAt {l : ℕ} (σ : Fin n → PTm l) (m : ℕ) (A B Q p : PTm n) :
    Syn.subst σ (prefixAt m A B Q p) = prefixAt m (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ Q) (Syn.subst σ p) :=
  by simp [prefixAt]
@[simp] theorem subst_meanPoint {l : ℕ} (σ : Fin n → PTm l) (m : ℕ) :
    Syn.subst σ (meanPoint m : PTm n) = (meanPoint m : PTm l) := by
  simp [meanPoint,signedMean,GaussianStirlingAllOrderPanelDerivative.meanNumerator,BernoulliBounds.zint]
@[simp] theorem subst_radius {l : ℕ} (σ : Fin n → PTm l) (m : ℕ) (B : PTm n) :
    Syn.subst σ (radius m B) = radius m (Syn.subst σ B) := by
  induction m with
  | zero => simp [radius]
  | succ m ih => simp [radius,ih,power]

private theorem double_half (A B Q p : PTm n) : Γ ⊢[PRAAx]
    qmul initial (halfPrefix A B Q (steps p)) ≐ prefixAt 0 A B Q p := by
  let v := panelPrefix 0 1 A B (B*Q) (steps p)
  have e : Γ ⊢[PRAAx] multiply (fraction two one : PTm n) (fraction one two) ≐ fraction one one := by
    have h₂ : Γ ⊢[PRAAx] le one (two : PTm n) := by ipra_le 1
    have hD := positive_product _ _ (le_refl one) h₂
    refine (RationalNonnegativePowers.fraction_multiply two one one two (le_refl one) h₂).eqTrans ?_
    apply RationalFiniteSum.canonical_equal _ _ _ _ _ _
      (RationalNormalForm.normalize_well_formed _ _ hD) (RationalNormalForm.normalize_well_formed _ _ (le_refl one))
      (fraction_represents _ _ hD) (fraction_represents _ _ (le_refl one)) hD (le_refl one)
    apply ZT.derive
    simp only [ZT.toZ_mul,ZT.toZ_ofNat]
    ipra_simps
    ring
  have z : Γ ⊢[PRAAx] multiply (fraction two one) (multiply (fraction one two) v) ≐ v :=
    (multiply_associative _ _ _).eqSymm.eqTrans ((multiply_congr e (.eqRefl _)).eqTrans
      ((multiply_commutative _ _).eqTrans (multiply_one_right v (RationalFiniteSum.sum_well_formed _ _ _))))
  exact (embed_multiply (fraction two one) (multiply (fraction one two) v)).eqSymm.eqTrans (embed_congr z)

private theorem initial_distance (A B Q p x : PTm n) (hs : Γ ⊢[PRAAx] source A B)
    (hQ : Γ ⊢[PRAAx] le (requiredMesh 0 A B p) Q) : Γ ⊢[PRAAx]
    distanceBounded (prefixAt 0 A B Q p) (ap2 (nameF 0) p (nameData 0 A B x)) (radius 0 B) (unit p) := by
  have hp := unit_positive (Γ := Γ) p
  have h := GaussianStirlingAllOrderFirstPanelPrefix.cutoff_distance A B Q p x hs hQ
  have g := fixed_product_distance initial _ _ _ _ hp h
  have t := normalized_product_error remainderF initial (remainderData A B x) p (remainder_regular A B x hs)
  exact distance_triangle_same _ _ _ _ _ _ hp (distance_congr (double_half A B Q p) (.eqRefl _) (.eqRefl _) (.eqRefl _) g)
    (distance_symmetric _ _ _ _ hp t)

private theorem step_distance (m : ℕ) (A B Q p x : PTm n) (hs : Γ ⊢[PRAAx] source A B)
    (hq : Γ ⊢[PRAAx] le (requiredMesh (m+1) A B p) Q)
    (ih : Γ ⊢[PRAAx] distanceBounded (prefixAt m A B Q p) (ap2 (nameF m) p (nameData m A B x))
      (radius m B) (unit p)) : Γ ⊢[PRAAx]
    distanceBounded (prefixAt (m+1) A B Q p) (ap2 (nameF (m+1)) p (nameData (m+1) A B x))
      (radius (m+1) B) (unit p) := by
  let e := 2*m+2
  let L := steps p
  let M := B*Q
  let R := recurrenceCost m A B p
  let W := massPrefix e A B M L
  let P := GaussianStirlingAllOrderPowerIntegralMeshCells.primitive e A B
  let f := nameF m
  let d := nameData m A B x
  let c := derivativeRatio (n := n) m
  let v := meanPoint (n := n) m
  let g := subF constantF f
  let w := subData (weightedPrimitive m A B) d
  have hp := unit_positive (Γ := Γ) p
  have hcut : Γ ⊢[PRAAx] le (unit p) L :=
    le_trans (GaussianStirlingIntegerLimit.index_dominates_unit p) (le_succ_self _)
  have hq' : Γ ⊢[PRAAx] le (unit p*succ R) Q :=
    le_trans (le_add_left _ (requiredMesh m A B p)) hq
  have mlarge : Γ ⊢[PRAAx] le Q M := by unfold M; ipra_le 𝔞 Q*sl hs.andE₂
  have hb : Γ ⊢[PRAAx] le (unit p) (unit p*succ R) := by ipra_le 𝔞 (unit p)*𝔞 R
  have munit := le_trans hb (le_trans hq' mlarge)
  have hM := le_trans hp munit
  have mbudget : Γ ⊢[PRAAx] le (R*unit p) (one*M) := by
    have h := le_trans hq' mlarge
    ipra_le sl h+𝔞 (unit p)
  have he : 2≤e := by unfold e; omega
  have hcEq : e+1=2*(m+1)+1 := by unfold e; omega
  have hlEq : e-1=2*m+1 := by unfold e; omega
  have h := finite_solve_distance (m+1) e (by omega) he A B M L hs.andE₁ hM
  have h0 := distance_symmetric _ _ _ _ hp
    (distance_radius_mono _ _ _ _ one (unit p) hM hp mbudget h)
  have first : Γ ⊢[PRAAx] distanceBounded (prefixAt (m+1) A B Q p) (embed (estimate (m+1) e A B M L)) one (unit p) := by
    simpa only [prefixAt,←hcEq,M,L] using h0
  have mass := cofinal_mass_distance e he A B M L (unit p) hs.andE₁ hp munit hcut
  have scaled := fixed_product_distance v (embed W) (embed P) (power e B+one) (unit p) hp mass
  have rowTarget := distance_congr (.eqRefl _) (embed_multiply (signedMean (m+1)) P).eqSymm
    (.eqRefl _) (.eqRefl _) scaled
  have row := GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ hp rowTarget ih
  have ideal := distance_triangle_same _ _ _ _ _ _ hp row
    (distance_symmetric _ _ _ _ hp (difference_error m A B x p hs))
  have transported := fixed_product_distance c _ _ _ _ hp ideal
  have eq : Γ ⊢[PRAAx] embed (estimate (m+1) e A B M L) ≐
      qmul c (qsub (qmul v (embed W)) (prefixAt m A B Q p)) := by
    unfold estimate
    rw [Nat.succ_sub_one,hlEq]
    exact (embed_multiply _ _).eqTrans
      (qmul_congr (.eqRefl _) ((embed_sub _ _).eqTrans (qsub_congr (embed_multiply _ _) (.eqRefl _))))
  have left := distance_congr eq.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) transported
  have hg := GaussianNamedDifference.name_regular constantF f (weightedPrimitive m A B) d
    (constant_regular _) (name_regular m A B x hs)
  have target := normalized_product_error g c w p hg
  exact distance_triangle_same _ _ _ _ _ _ hp first
    (distance_triangle_same _ _ _ _ _ _ hp left (distance_symmetric _ _ _ _ hp target))

theorem actual_prefix_distance (m : ℕ) (A B Q p x : PTm n) (hs : Γ ⊢[PRAAx] source A B)
    (hQ : Γ ⊢[PRAAx] le (requiredMesh m A B p) Q) : Γ ⊢[PRAAx]
    distanceBounded (prefixAt m A B Q p) (ap2 (nameF m) p (nameData m A B x)) (radius m B) (unit p) := by
  induction m with
  | zero => exact initial_distance A B Q p x hs hQ
  | succ m ih =>
    have h := le_trans (le_add_right (requiredMesh m A B p) (unit p*succ (recurrenceCost m A B p))) hQ
    exact step_distance m A B Q p x hs hQ (ih h)

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPanelPartsBinding

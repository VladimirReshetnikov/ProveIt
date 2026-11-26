import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalNormalizedExponentAlgebra
import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalPrefactorShiftBinding
import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalPrefixShift
import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalCombinedRemainder
import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalAdjacentLog

/-!
# The original normalized exponent equals the three Barnes remainders

The original finite shift exponent is combined with the terminal
logarithm and the finite Gauss normalization at the same cutoff.
The result is exactly the combined harmonic, terminal, and Stirling
remainder, with independent precision on the actual names.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNormalizedExponent

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalCorrectionShift (halfShift)
open GaussianBarnesCanonicalPrefactorShiftBinding (Observation leaf const product difference)
open GaussianBarnesCanonicalTerminalRemainder (source scaledF scaledData scaled_regular)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_regular gammaF gamma_regular harmonicPoint)
open GaussianGammaEulerHeadLower (translated)
open GaussianGammaFiniteApproximantName (logF log_regular)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData)
open GaussianNameEquivalence (crossEquivalent cross_at cross_refl cross_trans)
open GaussianNameRingLaws (oneF one_at one_fast negativeF negativeData negative_fast)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (qadd qzero positive_product ofGaussian ofGaussian_represents ofGaussian_canonical
  represents_congr canonical_unique qadd_represents qadd_canonical represents_rescale)
open GaussianRationalMetric (qsub qnegative qnegative_canonical)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianRationalSyntheticDivision (qone qzero_add qadd_congr qsub_congr)
open GaussianRootAlgebra (equal_of_values equal_refl re_add im_add re_scale im_scale)
open GaussianNamedGammaHalfShift (add_cross)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "C" => constantF
local notation "Add" => GaussianBarnesCanonicalPrefactorShiftBinding.sum
local notation "F" => GaussianBarnesCanonicalPrefixShift.exponentF
local notation "fd" => GaussianBarnesCanonicalPrefixShift.exponentData
local notation "Q" => GaussianBarnesCanonicalPrefactorShiftBinding.nameF
local notation "qd" => GaussianBarnesCanonicalPrefactorShiftBinding.data
local notation "S" => GaussianStirlingConstant.nameF
local notation "sd" => GaussianStirlingConstant.nameData
local notation "G" => GaussianStirlingNames.logGammaF
local notation "gd" => GaussianStirlingNames.logGammaData
local notation "D" => GaussianNamedDifference.nameF
local notation "dd" => GaussianNamedDifference.data

def offset (z B K : PTm n) : PTm n := qsub (naturalPoint K) (ofGaussian (translated z B one) B)
abbrev offsetF : PR 2 := multiplyF C logF
def offsetData (z B K : PTm n) : PTm n := multiplyData C logF (offset z B K) K
abbrev nameF : PR 2 := D (addF (addF F scaledF) offsetF) G
def data (z R B K : PTm n) : PTm n :=
  dd (addData (addData (fd z B K) (scaledData (translated z B one) R B K)) (offsetData z B K)) (gd K one)

private abbrev simplifiedF : PR 2 := D (addF (addF (addF Q C) scaledF) offsetF) G
private def simplifiedData (z R B K : PTm n) : PTm n :=
  dd (addData (addData (addData (qd z B) (GaussianBarnesCanonicalCorrectionShift.exponent z B K))
    (scaledData (translated z B one) R B K)) (offsetData z B K)) (gd K one)

private theorem midpoint (z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    ofGaussian (translated z B one) B ≐ qadd (halfShift z B) (fraction one two) := by
  let w := translated z B one
  let a := translated (ComplexLogarithmRemainder.scale two z) B one
  let s : PTm n → PTm n → PTm n := ComplexLogarithmRemainder.scale
  let i : PTm n := ComplexLogarithmRemainder.oneCode
  let T := two*B
  have ht := positive_product two B (le_succ_self one) hB
  have lhs := GaussianRationalSyntheticDivision.rescale_to (ofGaussian w B) w B two T
    (ofGaussian_represents w B hB) (mul_comm _ _)
  have half := represents_rescale (Γ := Γ) (fraction one two) (s one i) two B
    (ofGaussian_represents _ _ (le_succ_self one))
  have rhs := qadd_represents _ _ a (s B (s one i)) T ht (ofGaussian_represents a T ht) half
  apply canonical_unique _ _ _ T (ofGaussian_canonical _ _ hB) (qadd_canonical _ _) ht lhs
  apply represents_congr (.eqRefl _) _ (.eqRefl _) rhs
  apply equal_of_values <;> simp only [a,w,s,translated,re_add,im_add,re_scale,im_scale] <;> ipra_simps <;> ring

private def negative (a : Observation Γ) : Observation Γ where
  f := negativeF a.f
  x := negativeData a.x
  value p := qnegative (a.value p)
  cost := GaussianNameRingLaws.three+a.cost
  radius := a.radius
  reg := negative_fast _ _ a.reg
  close p := GaussianRationalDistanceOrder.distance_triangle_same _ _ _ _ _ _ (unit_positive p)
    (distance_congr (.eqRefl _) (qzero_add _ (qnegative_canonical _)) (.eqRefl _) (.eqRefl _)
      (GaussianNameRingLaws.negative_sample_error a.f a.x p a.reg))
    (GaussianNamedDifference.negative_distance _ _ _ _ (unit_positive p) (a.close p))
  bound p := GaussianRationalReciprocal.bounded_negative _ _ _ (le_refl one) (a.bound p)

private def observedOne : Observation Γ where
  f := oneF
  x := zero
  value _ := qone
  cost := zero
  radius := one
  reg := one_fast zero
  close p := distance_congr (one_at p zero).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (GaussianRationalPowerDifference.distance_refl_zero _ _ (unit_positive p))
  bound _ := GaussianRationalReciprocal.qone_bounded

private def stirling : Observation Γ := leaf S (sd zero) (GaussianStirlingConstant.name_regular zero)
private def euler : Observation Γ := leaf gammaF zero gamma_regular
private def factorialLog (K : PTm n) (h : Γ ⊢[PRAAx] le one K) : Observation Γ :=
  leaf G (gd K one) (GaussianStirlingNames.log_gamma_regular K one (.andI h (le_refl one)))
private def gaussLog (K : PTm n) (h : Γ ⊢[PRAAx] le one K) : Observation Γ := leaf logF K (log_regular K h)
private def stirlingLog (K : PTm n) (h : Γ ⊢[PRAAx] le one K) : Observation Γ where
  f := GaussianHarmonicLogarithmName.nameF
  x := GaussianHarmonicLogarithmName.data K one
  value p := ap2 logF p K
  cost := two
  radius := GaussianNameBounds.U logF K
  reg := GaussianHarmonicLogarithmName.name_regular K one (.andI h (le_refl one))
  close p := by
    have d := cross_at _ _ _ _ p p (GaussianBarnesCanonicalAdjacentLog.harmonic_log_cross K h)
    have hp := unit_positive (Γ := Γ) p
    exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hp hp) hp (le_of_eq_add (d := zero) (by ipra_ring)) d
  bound p := GaussianNameBounds.sample_bound logF K p (log_regular K h)

private def terminal (z R B K : PTm n) (h : Γ ⊢[PRAAx] source (translated z B one) R B K) : Observation Γ :=
  leaf scaledF (scaledData (translated z B one) R B K) (scaled_regular _ _ _ _ h)

private def left (z R B K : PTm n) (h : Γ ⊢[PRAAx] source (translated z B one) R B K) : Observation Γ :=
  let s := stirling (Γ := Γ)
  let c := const (qnegative (halfShift z B))
  let g := Add observedOne euler
  let pref := Add s (Add (const GaussianBarnesCanonicalPrefactor.negativeHalf) (product c g))
  let shift := Add pref (const (GaussianBarnesCanonicalCorrectionShift.exponent z B K))
  difference (Add (Add shift (terminal z R B K h)) (product (const (offset z B K)) (gaussLog K h.andE₂.andE₁)))
    (factorialLog K h.andE₂.andE₁)

private def right (z R B K : PTm n) (h : Γ ⊢[PRAAx] source (translated z B one) R B K) : Observation Γ :=
  let hK := h.andE₂.andE₁
  let w := ofGaussian (translated z B one) B
  let c := const (Γ := Γ) (halfShift z B)
  let harm := product (difference (Add (negative euler) (const (harmonicPoint K))) (gaussLog K hK)) c
  let t := difference (terminal z R B K h) (const w)
  let st := Add (Add (factorialLog K hK)
    (negative (product (const (GaussianStirlingNames.offset K one)) (stirlingLog K hK)))) (const (naturalPoint K))
  difference (Add harm t) (difference st stirling)

private def cost (z R B K : PTm n) (h : Γ ⊢[PRAAx] source (translated z B one) R B K) : PTm n :=
  (left z R B K h).cost+(right z R B K h).cost

private theorem subst_cost {m : ℕ} (σ : Fin n → PTm m) {Δ : List (Fm PTm m)} (z R B K : PTm n)
    (h : Γ ⊢[PRAAx] source (translated z B one) R B K)
    (h' : Δ ⊢[PRAAx] source (translated (Syn.subst σ z) (Syn.subst σ B) one) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ K)) :
    Syn.subst σ (cost z R B K h) = cost _ _ _ _ h' := by
  simp [cost,left,right,stirling,euler,factorialLog,gaussLog,stirlingLog,terminal,negative,observedOne,
    leaf,const,GaussianBarnesCanonicalPrefactorShiftBinding.sum,product,difference,
    offset,scaledData,GaussianBarnesCanonicalPrefactor.negativeHalf,GaussianNameRingLaws.three,one,two]

private theorem shift_simplifiedData {m : ℕ} (σ : Fin n → PTm m) (z R B K : PTm n) :
    Syn.subst σ (simplifiedData z R B K) = simplifiedData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ K) := by
  simp [simplifiedData,scaledData,offsetData,offset,one]

private theorem values (z R B K p : PTm n) (h : Γ ⊢[PRAAx] source (translated z B one) R B K) :
    Γ ⊢[PRAAx] (left z R B K h).value p ≐ (right z R B K h).value p := by
  let w := ofGaussian (translated z B one) B
  let c := halfShift z B
  let b : PTm n := fraction one two
  let s := ap2 S p (sd zero)
  let g := ap2 gammaF p zero
  let k := naturalPoint K
  let H := harmonicPoint K
  let l := ap2 logF p K
  let t := ap2 scaledF p (scaledData (translated z B one) R B K)
  let u := ap2 G p (gd K one)
  let x := GaussianBarnesCanonicalNormalizedExponentAlgebra.prefixShift s b c g H k
  have mw := midpoint z B h.andE₁
  have lhs : Γ ⊢[PRAAx] (left z R B K h).value p ≐ GaussianBarnesCanonicalNormalizedExponentAlgebra.normalized s b c g H k t l u := by
    change Γ ⊢[PRAAx] qsub (qadd (qadd x t) (GaussianRationalHorner.qmul (qsub k w) l)) u ≐
      qsub (qadd (qadd x t) (GaussianRationalHorner.qmul (qsub k (qadd c b)) l)) u
    exact qsub_congr (qadd_congr (.eqRefl _) (GaussianRationalSyntheticDivision.qmul_congr (qsub_congr (.eqRefl _) mw) (.eqRefl _))) (.eqRefl _)
  have rhs : Γ ⊢[PRAAx] (right z R B K h).value p ≐ GaussianBarnesCanonicalNormalizedExponentAlgebra.remainder s b c g H k t l u := by
    exact qsub_congr (qadd_congr (.eqRefl _) (qsub_congr (.eqRefl t) mw)) (.eqRefl _)
  exact lhs.eqTrans ((GaussianBarnesCanonicalNormalizedExponentAlgebra.normalize s b c g H k t l u).eqTrans rhs.eqSymm)

private theorem observation (p z R B K : PTm n) (h : Γ ⊢[PRAAx] source (translated z B one) R B K) : Γ ⊢[PRAAx]
    GaussianRationalMetric.distanceBounded (ap2 simplifiedF p (simplifiedData z R B K))
      (ap2 GaussianBarnesCanonicalCombinedRemainder.nameF p
        (GaussianBarnesCanonicalCombinedRemainder.data (halfShift z B) (translated z B one) R B K)) (cost z R B K h) (unit p) :=
  GaussianNameRingLaws.through_identity _ _ _ _ _ _ _ (unit_positive p) ((left z R B K h).close p)
    ((right z R B K h).close p) (values z R B K p h)

private theorem simplified_cross (z R B K : PTm n) (h : Γ ⊢[PRAAx] source (translated z B one) R B K) : Γ ⊢[PRAAx]
    crossEquivalent simplifiedF GaussianBarnesCanonicalCombinedRemainder.nameF (simplifiedData z R B K)
      (GaussianBarnesCanonicalCombinedRemainder.data (halfShift z B) (translated z B one) R B K) := by
  refine GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (cost z R B K h) (left z R B K h).reg (right z R B K h).reg (.allI ?_)
  let Δ := Γ.map Fm.shift
  let sh (t : PTm n) := Syn.shift t
  have hs : Δ ⊢[PRAAx] source (translated (sh z) (sh B) one) (sh R) (sh B) (sh K) := by
    simpa [Fm.shift,Syn.shift,Δ,sh,one] using h.shift
  have cs := subst_cost (Δ := Δ) (fun i => var i.succ) z R B K h hs
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,shift_simplifiedData,
    GaussianBarnesCanonicalCombinedRemainder.subst_data,GaussianBarnesCanonicalCorrectionShift.subst_halfShift,
    GaussianGammaEulerHeadLower.subst_translated,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,
    cs,Δ,sh,Syn.shift,one] using observation (var 0) (sh z) (sh R) (sh B) (sh K) hs

theorem normalized_cross (z R B K : PTm n) (h : Γ ⊢[PRAAx] source (translated z B one) R B K) : Γ ⊢[PRAAx]
    crossEquivalent nameF GaussianBarnesCanonicalCombinedRemainder.nameF (data z R B K)
      (GaussianBarnesCanonicalCombinedRemainder.data (halfShift z B) (translated z B one) R B K) := by
  let a := GaussianBarnesCanonicalPrefactorShift.differenceData z B
  let b := qd z B
  let c := GaussianBarnesCanonicalCorrectionShift.exponent z B K
  let t := scaledData (translated z B one) R B K
  let u := offsetData z B K
  let g := gd K one
  let P := GaussianBarnesCanonicalPrefactorShift.differenceF
  let F' := addF Q C
  let x := fd z B K
  let y := addData b c
  have ha := GaussianBarnesCanonicalPrefactorShift.difference_regular (Γ := Γ) z B
  have hb := GaussianBarnesCanonicalPrefactorShiftBinding.regular (Γ := Γ) z B
  have hc := constant_regular (Γ := Γ) c
  have ht := scaled_regular (translated z B one) R B K h
  have hu := GaussianNameArithmetic.multiply_fast C logF (offset z B K) K
    (constant_regular (offset z B K)) (log_regular K h.andE₂.andE₁)
  have hg := GaussianStirlingNames.log_gamma_regular K one (.andI h.andE₂.andE₁ (le_refl one))
  have e : Γ ⊢[PRAAx] crossEquivalent F F' x y := add_cross P Q C C a b c c ha hb hc hc
    (GaussianBarnesCanonicalPrefactorShiftBinding.difference_cross z B h.andE₁) (cross_refl _ _ hc)
  have hx := add_fast P C a c ha hc
  have hy := add_fast Q C b c hb hc
  have first := add_cross F F' scaledF scaledF x y t t hx hy ht ht e (cross_refl _ _ ht)
  have last := add_cross (addF F scaledF) (addF F' scaledF) offsetF offsetF (addData x t) (addData y t) u u
    (add_fast _ _ _ _ hx ht) (add_fast _ _ _ _ hy ht) hu hu first (cross_refl _ _ hu)
  have align := GaussianNamedDifferenceQuotientProperness.difference_proper (addF (addF F scaledF) offsetF)
    (addF (addF F' scaledF) offsetF) G G (addData (addData x t) u) (addData (addData y t) u) g g
    (add_fast _ _ _ _ (add_fast _ _ _ _ hx ht) hu) (add_fast _ _ _ _ (add_fast _ _ _ _ hy ht) hu)
    hg hg last (cross_refl _ _ hg)
  exact cross_trans _ _ _ _ _ _ align (simplified_cross z R B K h)

theorem actual_Barnes_original_normalized_exponent_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (let z := var 0
     let R := var 1
     let B := var 2
     let K := var 3
     source (translated z B one) R B K ⟶ crossEquivalent nameF GaussianBarnesCanonicalCombinedRemainder.nameF (data z R B K)
       (GaussianBarnesCanonicalCombinedRemainder.data (halfShift z B) (translated z B one) R B K)) :=
  closeUniv 4 (.impI (normalized_cross _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNormalizedExponent

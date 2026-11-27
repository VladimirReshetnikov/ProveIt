import IPRADerivations.Analysis.Barnes.FunctionalEquations.UnitShift.GaussianBarnesCanonicalFiniteGaussIdentity
import IPRADerivations.Analysis.Barnes.Logarithms.CofinalTails.GaussianBarnesCanonicalCombinedRemainderRate
import IPRADerivations.Analysis.Barnes.TailControl.GaussianBarnesCanonicalUniformCutoff
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaEulerInverseConvergence
import IPRADerivations.Analysis.Names.FiniteOperations.Products.Bounds.GaussianNamedMultiplyRate
import IPRADerivations.Analysis.Names.FiniteOperations.Sums.GaussianNamedAddRate

/-!
# Uniform rates for the two sides of the original finite Barnes identity

The normalized multiplier and the additional rational factor tend
to one at common cutoffs. The original finite Gauss and Barnes
samplers compare simultaneously with their canonical limits.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteGaussRate

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianBarnesCanonicalHead (source)
open GaussianBarnesCanonicalProduct (literalData literal_regular)
open GaussianBarnesCanonicalValue (prefixF)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular constant_at)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaEulerHeadLower (translated)
open GaussianGammaFiniteApproximantName (qF qData q_regular exponential_input)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast add_fast)
open GaussianNameBounds (U)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNamedInverseRate (independentRate diagonal_rate)
open GaussianNamedMultiplyRate (sampleBound leadingNumerator leadingDenominator)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (ofGaussian ofGaussian_canonical ofGaussian_represents positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr qone)
open GaussianRationalSyntheticDivision (qadd_sub_cancel)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "C" => constantF
local notation "V" => GaussianBarnesCanonicalValue.nameF
local notation "vd" => GaussianBarnesCanonicalValue.data
local notation "A" => GaussianGammaC7Name.nameF
local notation "ad" => GaussianGammaC7Name.data
local notation "E" => GaussianBarnesCanonicalNormalizedMultiplier.nameF
local notation "ed" => GaussianBarnesCanonicalNormalizedMultiplier.data
local notation "X" => GaussianBarnesCanonicalNormalizedExponent.nameF
local notation "xd" => GaussianBarnesCanonicalNormalizedExponent.data
local notation "Exp" => GaussianRadiusExponentialName.nameF
local notation "C1" => GaussianBarnesCanonicalFiniteGaussIdentity.base

abbrev targetF : PR 2 := multiplyF V A
def targetData (z S B : PTm n) : PTm n :=
  multiplyData V A (vd (translated z B one) S B) (ad (translated z B one) S B)

@[simp] theorem subst_targetData {m : ℕ} (σ : Fin n → PTm m) (z S B : PTm n) :
    Syn.subst σ (targetData z S B) = targetData (Syn.subst σ z) (Syn.subst σ S) (Syn.subst σ B) := by
  simp [targetData,one]

def remainderGain (S M : PTm n) : PTm n := GaussianRadiusExponentialLipschitzRate.factor
  (GaussianBarnesCanonicalCombinedRemainderRate.radius S M)*GaussianBarnesCanonicalCombinedRemainderRate.coefficient S M
def expCap (S M : PTm n) : PTm n := U C qone+remainderGain S M+two
def gammaCap (w S B : PTm n) : PTm n := U A (ad w S B)+GaussianGammaEulerApproximationName.rate S+two
def leftGain (z S B : PTm n) : PTm n :=
  gammaCap (translated z B one) S B*one+U V (vd (translated z B one) S B)*one
def rightGain (z R S B M : PTm n) : PTm n :=
  (S+one)*(expCap S M*one+U V (vd z R B)*one)+U (multiplyF V C) (multiplyData V C (vd z R B) qone)*one

private theorem cap_at (f g : PR 2) (x y A' K p : PTm n) (hK : Γ ⊢[PRAAx] le one K)
    (hg : Γ ⊢[PRAAx] pointCN g y) (h : Γ ⊢[PRAAx] independentRate f g x y A' K) : Γ ⊢[PRAAx]
    bounded (ap2 f p x) (U g y+A'+two) one := by
  let D := unit p
  have hu := unit_positive (Γ := Γ) p
  have hD := positive_product K D hK hu
  have close := diagonal_rate f g x y A' K p hK h
  have clear : Γ ⊢[PRAAx] le ((A'*D+two*K)*one) ((A'+two)*(K*D)) := by
    ipra_le 𝔞 A'*𝔞 D*sl hK+2*𝔞 K*sl hu
  have small := distance_radius_mono _ _ _ _ (A'+two) one hD (le_refl one) clear close
  exact bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring)
    (GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _ (le_refl one) (le_refl one) small
      (GaussianNameBounds.sample_bound g y p hg))

private theorem cap (f g : PR 2) (x y A' K : PTm n) (hK : Γ ⊢[PRAAx] le one K) (hg : Γ ⊢[PRAAx] pointCN g y)
    (h : Γ ⊢[PRAAx] independentRate f g x y A' K) : Γ ⊢[PRAAx] sampleBound f x (U g y+A'+two) := by
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let sh (t : PTm n) := Syn.shift t
  have k : Δ ⊢[PRAAx] le one (sh K) := by simpa [Fm.shift,Syn.shift,Δ,sh,one] using hK.shift
  have r : Δ ⊢[PRAAx] pointCN g (sh y) := by simpa [Fm.shift,Syn.shift,Δ,sh] using hg.shift
  have e : Δ ⊢[PRAAx] independentRate f g (sh x) (sh y) (sh A') (sh K) := by simpa [Fm.shift,Syn.shift,Δ,sh] using h.shift
  simpa [sampleBound,Syn.shift,Δ,sh,one,two] using cap_at f g (sh x) (sh y) (sh A') (sh K) (var 0) k r e

private theorem budget_product (F G H J : PR 2) (x y v w A' C' M R d : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hf : Γ ⊢[PRAAx] pointCN F x) (hg : Γ ⊢[PRAAx] pointCN G y)
    (hh : Γ ⊢[PRAAx] pointCN H v) (hj : Γ ⊢[PRAAx] pointCN J w)
    (gm : Γ ⊢[PRAAx] sampleBound G y M) (hr : Γ ⊢[PRAAx] sampleBound H v R)
    (fh : Γ ⊢[PRAAx] independentRate F H x v A' d) (gj : Γ ⊢[PRAAx] independentRate G J y w C' d) : Γ ⊢[PRAAx]
    independentRate (multiplyF F G) (multiplyF H J) (multiplyData F G x y) (multiplyData H J v w) (M*A'+R*C') d := by
  have p := GaussianNamedMultiplyRate.independent_rate F G H J x y v w A' d C' d M R hd hd hf hg hh hj gm hr fh gj
  exact GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ (positive_product _ _ hd hd) hd
    (le_of_eq_add (d := zero) (by unfold leadingNumerator; ipra_ring)) p

private theorem base_error (z S B K : PTm n) (h : Γ ⊢[PRAAx] source (translated z B one) S B)
    (hK : Γ ⊢[PRAAx] le one K) : Γ ⊢[PRAAx] distanceBounded (C1 z B K) qone S K := by
  let w := translated z B one
  let D := B*K
  have hd := positive_product B K h.andE₁ hK
  have clear : Γ ⊢[PRAAx] le ((K*K)*ComplexLogarithmRemainder.normSq w) ((S*S)*(D*D)) :=
    le_congr (.eqRefl _) (by dsimp only [D]; ipra_ring) (le_mul_mono (le_refl (K*K)) h.andE₂)
  have b := GaussianRationalMetric.bounded_of_cleared (ofGaussian w D) w D S K hd hK (ofGaussian_represents _ _ hd) clear
  exact bound_congr (qadd_sub_cancel qone (ofGaussian w D) (ofGaussian_canonical _ _ hd)).eqSymm (.eqRefl _) (.eqRefl _) b

private theorem base_cap (z S B K : PTm n) (hw : Γ ⊢[PRAAx] source (translated z B one) S B)
    (hK : Γ ⊢[PRAAx] le one K) : Γ ⊢[PRAAx] sampleBound C (C1 z B K) (S+one) := by
  let w := translated z B one
  have b := GaussianBarnesCanonicalFactor.base_bound w S B K (.andI hw.andE₁ (.andI hK hw.andE₂))
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  have h : Δ ⊢[PRAAx] bounded (Syn.shift (C1 z B K)) (Syn.shift (S+one)) one := by
    simpa [GaussianBarnesCanonicalFiniteGaussIdentity.base,Fm.shift,Syn.shift,w,Δ,one] using b.shift
  simpa [sampleBound,Syn.shift,Δ,one] using bound_congr (constant_at (var 0) (Syn.shift (C1 z B K))).eqSymm (.eqRefl _) (.eqRefl _) h

private theorem regular_exponent (z S B K : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianBarnesCanonicalTerminalRemainder.source (translated z B one) S B K) :
    Γ ⊢[PRAAx] pointCN X (xd z S B K) := by
  let w := translated z B one
  let hK := hs.andE₂.andE₁
  exact GaussianNamedDifference.name_regular _ _ _ _ (add_fast _ _ _ _ (add_fast _ _ _ _
    (add_fast _ _ _ _ (GaussianBarnesCanonicalPrefactorShift.difference_regular z B) (constant_regular _))
    (GaussianBarnesCanonicalTerminalRemainder.scaled_regular w S B K hs))
    (multiply_fast C _ (GaussianBarnesCanonicalNormalizedExponent.offset z B K) K (constant_regular _)
      (GaussianGammaFiniteApproximantName.log_regular K hK)))
    (GaussianStirlingGammaLogarithm.log_gamma_regular K one (.andI hK (le_refl one)))

private theorem normalized_rate (z S B M K : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianBarnesCanonicalTerminalRemainder.source (translated z B one) S B K)
    (hm : Γ ⊢[PRAAx] bounded (GaussianBarnesCanonicalCorrectionShift.halfShift z B) M one) : Γ ⊢[PRAAx]
    independentRate E C (ed z S B K) qone (remainderGain S M) K := by
  let w := translated z B one
  let c := GaussianBarnesCanonicalCorrectionShift.halfShift z B
  let f := GaussianBarnesCanonicalCombinedRemainder.nameF
  let x := xd z S B K
  let y := GaussianBarnesCanonicalCombinedRemainder.data c w S B K
  let R := GaussianBarnesCanonicalCombinedRemainderRate.radius S M
  have hK := hs.andE₂.andE₁
  have raw := GaussianBarnesCanonicalCombinedRemainderRate.exponential_rate c M w S B K hs hm
  have xl := regular_exponent z S B K hs
  have bound := GaussianBarnesCanonicalCombinedRemainderRate.exponential_input c M w S B K hs hm
  have eq := GaussianExponentialRadiusIndependence.independent_radii_proper X f (U X x) R x y
    (exponential_input X x xl) bound (GaussianBarnesCanonicalNormalizedExponent.normalized_cross z S B K hs)
  exact GaussianNamedRateTransport.transport (Exp f) C E C (GaussianRadiusExponentialName.data R y) qone (ed z S B K) qone
    (remainderGain S M) K hK raw eq (cross_refl _ _ (constant_regular _))

private theorem pay (f g : PR 2) (x y a K p : PTm n) (hK : Γ ⊢[PRAAx] le one K)
    (h : Γ ⊢[PRAAx] le (a*unit p) K) (r : Γ ⊢[PRAAx] independentRate f g x y a K) : Γ ⊢[PRAAx]
    independentRate f g x y one (unit p) :=
  GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ hK (unit_positive p)
    (le_congr (.eqRefl _) (by ipra_ring) h) r

theorem left_rate (z S B K p : PTm n) (hK : Γ ⊢[PRAAx] le one K)
    (h : Γ ⊢[PRAAx] GaussianGammaEulerConvergence.source (translated z B one) S B K)
    (hCut : Γ ⊢[PRAAx] le (GaussianBarnesCanonicalUniformCutoff.cutoff S p) K)
    (hRate : Γ ⊢[PRAAx] le (GaussianGammaEulerApproximationName.rate S*unit p) K) : Γ ⊢[PRAAx]
    independentRate GaussianBarnesCanonicalFiniteGaussIdentity.leftF targetF
      (GaussianBarnesCanonicalFiniteGaussIdentity.leftData z S B K) (targetData z S B) (leftGain z S B) (unit p) := by
  let w := translated z B one
  let x := literalData w S B K
  let y := qData w B K
  let v := vd w S B
  let a := ad w S B
  have hs : Γ ⊢[PRAAx] source w S B := h.andE₁.andE₂
  have hr := GaussianBarnesCanonicalUniformCutoff.uniform_rate w S B p K hs hCut
  have hg := GaussianGammaEulerInverseConvergence.direct_rate w S B K h
  have g := GaussianGammaC7Name.name_regular w S B h.andE₁
  have f := GaussianBarnesCanonicalValue.regular w S B hs
  exact budget_product prefixF qF V A x y v a one one (gammaCap w S B) (U V v) (unit p) (unit_positive p)
    (literal_regular w S B K hs) (q_regular w B K hK) f g (cap qF A y a _ K hK g hg)
    (GaussianNameBounds.all_samples_bounded V v f) hr (pay qF A y a _ K p hK hRate hg)

private theorem drop_one (F : PR 2) (x : PTm n) (h : Γ ⊢[PRAAx] pointCN F x) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF F C) F (multiplyData F C x qone) x := by
  let O := GaussianNameRingLaws.oneF
  have e := multiply_cross F F C O x x qone x h h (constant_regular _) (GaussianNameRingLaws.one_fast x)
    (cross_refl _ _ h) (GaussianArctangentExponentialPeriod.constant_one_cross x)
  exact cross_trans _ _ _ _ _ _ e (GaussianNameRingLaws.multiply_one F x h)

theorem right_rate (z R S B M K p : PTm n) (h : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] GaussianBarnesCanonicalTerminalRemainder.source (translated z B one) S B K)
    (hm : Γ ⊢[PRAAx] bounded (GaussianBarnesCanonicalCorrectionShift.halfShift z B) M one)
    (hCut : Γ ⊢[PRAAx] le (GaussianBarnesCanonicalUniformCutoff.cutoff R p) K)
    (hExp : Γ ⊢[PRAAx] le (remainderGain S M*unit p) K) (hBase : Γ ⊢[PRAAx] le (S*unit p) K) : Γ ⊢[PRAAx]
    independentRate GaussianBarnesCanonicalFiniteGaussIdentity.rightF V (GaussianBarnesCanonicalFiniteGaussIdentity.rightData z R S B K)
      (vd z R B) (rightGain z R S B M) (unit p) := by
  let hK := hw.andE₂.andE₁
  let w := translated z B one
  let x := literalData z R B K
  let y := ed z S B K
  let v := vd z R B
  let c := C1 z B K
  let T := multiplyF prefixF E
  let t := multiplyData prefixF E x y
  let W := multiplyF V C
  let s := multiplyData V C v qone
  have ev := normalized_rate z S B M K hw hm
  have source_w : Γ ⊢[PRAAx] source w S B := .andI hw.andE₁ hw.andE₂.andE₂.andE₁
  have base := GaussianNamedAddRate.constant_rate c qone S K hK (base_error z S B K source_w hK)
  have line := GaussianBarnesCanonicalUniformCutoff.uniform_rate z R B p K h hCut
  have hx := literal_regular z R B K h
  have hv := GaussianBarnesCanonicalValue.regular z R B h
  have hy := GaussianRadiusExponentialName.name_regular X _ (xd z S B K) (exponential_input _ _
    (regular_exponent z S B K hw))
  have h1 := constant_regular (Γ := Γ) (qone : PTm n)
  have hQ := unit_positive (Γ := Γ) p
  have e := budget_product prefixF E V C x y v qone one one (expCap S M) (U V v) (unit p) hQ hx hy hv h1
    (cap E C y qone _ K hK h1 ev) (GaussianNameBounds.all_samples_bounded V v hv) line (pay E C y qone _ K p hK hExp ev)
  have ht := multiply_fast prefixF E x y hx hy
  have hs := multiply_fast V C v qone hv h1
  have m := budget_product T C W C t c s qone (expCap S M*one+U V v*one) one (S+one) (U W s) (unit p) hQ
    ht (constant_regular _) hs h1 (base_cap z S B K source_w hK)
    (GaussianNameBounds.all_samples_bounded W s hs) e (pay C C c qone S K p hK hBase base)
  have eq := cross_trans _ _ _ _ _ _ (drop_one W s hs) (drop_one V v hv)
  exact GaussianNamedRateTransport.transport _ _ _ _ _ _ _ _ _ _ hQ m
    (cross_refl _ _ (multiply_fast _ _ _ _ ht (constant_regular _))) (cross_symm _ _ _ _ eq)

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteGaussRate

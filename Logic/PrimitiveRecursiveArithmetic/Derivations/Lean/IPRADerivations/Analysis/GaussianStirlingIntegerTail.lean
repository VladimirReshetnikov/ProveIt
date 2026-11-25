import IPRADerivations.Analysis.GaussianStirlingTelescopeName
import IPRADerivations.Analysis.GaussianStirlingRationalTelescopers
import IPRADerivations.Analysis.RationalGaussianNameEmbedding
import IPRADerivations.Analysis.GaussianGammaHalfSqrtBrackets

/-!
# Integer Stirling tail distances from finite named order

The explicit uniform contract records the two finite telescoped
inequalities at positive integers. Actual (A) samples are compared
at the same or independent observation precisions with all rounding
errors included.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingIntegerTail

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianStirlingNames (nameData source name_regular name_real add_real)
open GaussianStirlingTelescope (shifted shifted_source)
open GaussianStirlingTelescopeName (endpointData)
open GaussianStirlingRationalTelescopers (upperDifference upper_den_positive)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianNameRingLaws (negativeF negativeData)
open GaussianNameEquivalence (point_at)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalHorner (qzero canonical positive_product)
open GaussianRationalMetric (qsub distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_radius_mono distance_triangle_same)
open GaussianRationalReciprocal (bound_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNamedPositiveExponentialOrder (realOrder real_order_at)
open GaussianSignedNameExponentialOrder (realSamples real_sample_at)
open RationalGaussianEmbedding (canonical_axis_roundtrip axis_zero scalarZero scalar_zero_represents)
open RationalValueBounds (upper upper_congr upper_triangle upper_mono radius_of_upper)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "A" => GaussianStirlingNames.nameF
local notation "G" => GaussianNamedDifference.nameF A A
local notation "C" => constantF

def integerTailLaw (i N : PTm n) : Fm PTm n :=
  realOrder C G qzero (endpointData N i one) ⋏
    realOrder G C (endpointData N i one) (upperDifference i one N)
def integerTailContract : Fm PTm n := .all (.all (le one (var 1) ⟶ integerTailLaw (var 1) (var 0)))

@[simp] theorem subst_integerTailLaw {l : ℕ} (σ : Fin n → PTm l) (i N : PTm n) :
    (integerTailLaw i N).subst σ = integerTailLaw (Syn.subst σ i) (Syn.subst σ N) := by
  simp [integerTailLaw,one,GaussianRationalHorner.qzero,ComplexLogarithmRemainder.zeroCode,
    ComplexLogarithmRemainder.code,ZT.ofNat]
@[simp] theorem subst_integerTailContract {l : ℕ} (σ : Fin n → PTm l) :
    (integerTailContract : Fm PTm n).subst σ = (integerTailContract : Fm PTm l) := by
  simp [integerTailContract,one,Syn.up_zero,Syn.up_one,Syn.up_succ]

theorem tail_at (i N : PTm n) (hi : Γ ⊢[PRAAx] le one i) (h : Γ ⊢[PRAAx] integerTailContract) :
    Γ ⊢[PRAAx] integerTailLaw i N := by
  have first : Γ ⊢[PRAAx] .all (le one (Syn.shift i) ⟶ integerTailLaw (Syn.shift i) (var 0)) := by
    simpa [integerTailContract,one,Syn.shift,Syn.up_zero,Syn.up_one,Syn.up_succ] using h.allE i
  have second : Γ ⊢[PRAAx] le one i ⟶ integerTailLaw i N := by
    simpa [one] using first.allE N
  exact .impE second hi

theorem contract_of_law (tail : ∀ {l : ℕ} {Δ : List (Fm PTm l)} (i N : PTm l),
    (Δ ⊢[PRAAx] le one i) → (Δ ⊢[PRAAx] integerTailLaw i N)) : Γ ⊢[PRAAx] integerTailContract :=
  .allI (.allI (.impI (tail _ _ Prf.hyp0)))

def point (p i : PTm n) : PTm n := ap2 A p (nameData i one)
def after (i N : PTm n) : PTm n := shifted i one N
def tailDen (i : PTm n) : PTm n := num 12*i

@[simp] theorem subst_point {l : ℕ} (σ : Fin n → PTm l) (p i : PTm n) :
    Syn.subst σ (point p i) = point (Syn.subst σ p) (Syn.subst σ i) := by simp [point,one]
@[simp] theorem subst_after {l : ℕ} (σ : Fin n → PTm l) (i N : PTm n) :
    Syn.subst σ (after i N) = after (Syn.subst σ i) (Syn.subst σ N) := by simp [after,one]
@[simp] theorem subst_tailDen {l : ℕ} (σ : Fin n → PTm l) (i : PTm n) :
    Syn.subst σ (tailDen i) = tailDen (Syn.subst σ i) := by simp [tailDen]

theorem integer_source (i : PTm n) (hi : Γ ⊢[PRAAx] le one i) : Γ ⊢[PRAAx] source i one :=
  .andI hi (le_refl one)
theorem after_positive (i N : PTm n) (hi : Γ ⊢[PRAAx] le one i) : Γ ⊢[PRAAx] le one (after i N) :=
  (shifted_source i one N (integer_source i hi)).andE₁
theorem den_positive (i : PTm n) (hi : Γ ⊢[PRAAx] le one i) : Γ ⊢[PRAAx] le one (tailDen i) :=
  upper_den_positive i hi

theorem after_congr (i j : PTm n) (h : Γ ⊢[PRAAx] le i j) : Γ ⊢[PRAAx] after i (monus j i) ≐ j :=
  (show Γ ⊢[PRAAx] after i (monus j i) ≐ i+monus j i from by unfold after shifted; ipra_ring).eqTrans
    (eq_add_of_le h).eqSymm

theorem point_congr (p : PTm n) {i j : PTm n} (h : Γ ⊢[PRAAx] i ≐ j) : Γ ⊢[PRAAx] point p i ≐ point p j := by
  simpa using Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (point (var 0) (var 1) : PTm 2)
    (σ := ![p,i]) (σ' := ![p,j]) (fun k => by fin_cases k; exact .eqRefl _; exact h)

theorem point_distance (p q i : PTm n) (hi : Γ ⊢[PRAAx] le one i) :
    Γ ⊢[PRAAx] distanceBounded (point p i) (point q i) (unit p+unit q) (unit p*unit q) :=
  point_at A (nameData i one) p q (name_regular i one (integer_source i hi))

private theorem zero_represents : Γ ⊢[PRAAx] RationalArithmetic.represents (fstT (qzero : PTm n)) (ZT.ofNat zero) one := by
  have eq : Γ ⊢[PRAAx] fstT (qzero : PTm n) ≐ scalarZero :=
    (congrFst (RationalGaussianEmbedding.embed_zero (Γ := Γ))).eqSymm.eqTrans
      (fst_pair _ _ |>.eqTrans RationalGaussianEmbedding.scalar_recode_zero)
  exact GaussianRationalHorner.scalar_congr eq.eqSymm (.eqRefl _) (.eqRefl _) (scalar_zero_represents one)

private theorem cap_to_zero (i N : PTm n) (hi : Γ ⊢[PRAAx] le one i) :
    Γ ⊢[PRAAx] upper (fstT (upperDifference i one N)) (fstT qzero) one (tailDen i) := by
  let D := tailDen i
  let E := num 12*i*(i+one*N)
  let T : PTm n := one*one*N
  have d := den_positive (Γ := Γ) i hi
  have e : Γ ⊢[PRAAx] le one E := positive_product _ _ d (le_trans hi (le_add_right i (one*N)))
  have clear : Γ ⊢[PRAAx] le (D*T) E := by
    dsimp only [D,E,T,tailDen]
    ipra_le 𝔞 (num 12*i)*𝔞 i
  apply RationalRepresentedUpper.from_signed _ _ (ZT.ofNat T) (ZT.ofNat zero) E one one D e (le_refl one)
    (GaussianGammaHalfSqrtBrackets.fraction_first_represents T E e) zero_represents
  apply zle_of_toZ (monus E (D*T))
  have exactValue := natEq (eq_add_of_le clear)
  simp only [RationalRepresentedUpper.left,RationalRepresentedUpper.right,ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat]
  ipra_simps
  linear_combination -exactValue

private theorem difference_real (i N : PTm n) (hi : Γ ⊢[PRAAx] le one i) : Γ ⊢[PRAAx] realSamples G (endpointData N i one) :=
  add_real A (negativeF A) (nameData i one) (negativeData (nameData (after i N) one))
    (name_real i one (integer_source i hi))
    (GaussianNamedDampingPowerRealSamples.negative_real A (nameData (after i N) one)
      (name_real (after i N) one (integer_source _ (after_positive i N hi))))

private theorem named_distance_zero (p i N : PTm n) (hi : Γ ⊢[PRAAx] le one i) (h : Γ ⊢[PRAAx] integerTailLaw i N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 G p (endpointData N i one)) qzero (unit p+two*tailDen i) (tailDen i*unit p) := by
  let U := unit p
  let D := tailDen i
  let X := endpointData N i one
  let W := ap2 G p X
  let Z : PTm n := qzero
  let M := upperDifference i one N
  have hp := unit_positive (Γ := Γ) p
  have hd := den_positive (Γ := Γ) i hi
  have lower : Γ ⊢[PRAAx] upper (fstT Z) (fstT W) two U := by
    have raw := real_order_at C G Z X p p h.andE₁
    have e := upper_congr (congrFst (constant_at p Z)) (.eqRefl _) (.eqRefl _) (.eqRefl _) raw
    exact upper_mono _ _ _ _ two U (positive_product _ _ hp hp) e (by ipra_le 0)
  have higher : Γ ⊢[PRAAx] upper (fstT W) (fstT M) two U := by
    have raw := real_order_at G C X M p p h.andE₂
    have e := upper_congr (.eqRefl _) (congrFst (constant_at p M)) (.eqRefl _) (.eqRefl _) raw
    exact upper_mono _ _ _ _ two U (positive_product _ _ hp hp) e (by ipra_le 0)
  have low : Γ ⊢[PRAAx] upper (fstT Z) (fstT W) (U+two*D) (D*U) :=
    upper_mono _ _ _ _ _ _ hp lower (by ipra_le 𝔞 U*𝔞 U)
  have high : Γ ⊢[PRAAx] upper (fstT W) (fstT Z) (U+two*D) (D*U) :=
    upper_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (mul_comm U D)
      (upper_triangle _ _ _ _ _ _ _ higher (cap_to_zero i N hi))
  have hw := real_sample_at G X p (difference_real i N hi)
  have wd := canonical_axis_roundtrip W hw.andE₁ hw.andE₂
  have zd := canonical_axis_roundtrip (Γ := Γ) Z GaussianRationalSyntheticDivision.qzero_canonical axis_zero
  exact distance_congr wd zd (.eqRefl _) (.eqRefl _)
    (RationalGaussianNameEmbedding.distance_from_radius _ _ _ _ (positive_product _ _ hd hp)
      (radius_of_upper _ _ _ _ high low))

theorem common_distance (p i N : PTm n) (hi : Γ ⊢[PRAAx] le one i) (h : Γ ⊢[PRAAx] integerTailContract) :
    Γ ⊢[PRAAx] distanceBounded (point p i) (point p (after i N)) (unit p+num 8*tailDen i) (tailDen i*unit p) := by
  let D := tailDen i
  let U := unit p
  let W := ap2 G p (endpointData N i one)
  let Z := qsub (point p i) (point p (after i N))
  have hp := unit_positive (Γ := Γ) p
  have hd := den_positive (Γ := Γ) i hi
  have hu := positive_product (Γ := Γ) _ _ hd hp
  have e : Γ ⊢[PRAAx] distanceBounded W Z (num 6) U :=
    GaussianNamedDifference.sample_error A A (nameData i one) (nameData (after i N) one) p
      (name_regular i one (integer_source i hi)) (name_regular _ _ (integer_source _ (after_positive i N hi)))
  have first : Γ ⊢[PRAAx] distanceBounded Z W (num 6*D) (D*U) :=
    distance_radius_mono _ _ _ _ _ _ hp hu (by ipra_le 0) (distance_symmetric _ _ _ _ hp e)
  have second := named_distance_zero p i N hi (tail_at i N hi h)
  have combined := distance_triangle_same Z W qzero _ _ _ hu first second
  exact bound_congr
    (GaussianRationalReconstruction.qsub_zero_right Z (GaussianRationalMetric.qsub_canonical _ _))
    (by ipra_ring) (.eqRefl _) combined

def mixedNumerator (s t i : PTm n) : PTm n := unit s*unit t+tailDen i*(unit s+num 9*unit t)
def mixedDenominator (s t i : PTm n) : PTm n := tailDen i*(unit s*unit t)

theorem mixed_den_positive (s t i : PTm n) (hi : Γ ⊢[PRAAx] le one i) : Γ ⊢[PRAAx] le one (mixedDenominator s t i) :=
  positive_product _ _ (den_positive i hi) (positive_product _ _ (unit_positive s) (unit_positive t))

private theorem lift_common (s t i N : PTm n) (hi : Γ ⊢[PRAAx] le one i) (h : Γ ⊢[PRAAx] integerTailContract) :
    Γ ⊢[PRAAx] distanceBounded (point s i) (point s (after i N))
      ((unit s+num 8*tailDen i)*unit t) (mixedDenominator s t i) :=
  distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (den_positive i hi) (unit_positive s))
    (mixed_den_positive s t i hi) (by unfold mixedDenominator; ipra_le 0) (common_distance s i N hi h)

private theorem lift_point (s t i j : PTm n) (hi : Γ ⊢[PRAAx] le one i) (hj : Γ ⊢[PRAAx] le one j) :
    Γ ⊢[PRAAx] distanceBounded (point s j) (point t j) (tailDen i*(unit s+unit t)) (mixedDenominator s t i) :=
  distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive s) (unit_positive t))
    (mixed_den_positive s t i hi) (by unfold mixedDenominator; ipra_le 0) (point_distance s t j hj)

theorem anchored_left (s t i N : PTm n) (hi : Γ ⊢[PRAAx] le one i) (h : Γ ⊢[PRAAx] integerTailContract) :
    Γ ⊢[PRAAx] distanceBounded (point s i) (point t (after i N)) (mixedNumerator s t i) (mixedDenominator s t i) :=
  distance_congr (.eqRefl _) (.eqRefl _) (by unfold mixedNumerator; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (mixed_den_positive s t i hi)
      (lift_common s t i N hi h) (lift_point s t i (after i N) hi (after_positive i N hi)))

theorem anchored_right (s t i N : PTm n) (hi : Γ ⊢[PRAAx] le one i) (h : Γ ⊢[PRAAx] integerTailContract) :
    Γ ⊢[PRAAx] distanceBounded (point t i) (point s (after i N)) (mixedNumerator s t i) (mixedDenominator s t i) := by
  have e := distance_symmetric _ _ _ _ (mixed_den_positive s t i hi) (lift_point s t i i hi hi)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold mixedNumerator; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (mixed_den_positive s t i hi) e (lift_common s t i N hi h))

end LeanProofs.IPRA.Analysis.GaussianStirlingIntegerTail

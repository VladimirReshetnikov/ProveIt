import IPRADerivations.Analysis.GaussianGammaEulerReflectionName
import IPRADerivations.Analysis.GaussianGammaEulerApproximationName
import IPRADerivations.Analysis.GaussianSineProductName

/-!
# Cofinal reflection of the original reciprocal Gamma names

A common numerical Euler cutoff serves both arguments and the literal
sine product. Comparing the original name observations at this cutoff
passes the finite paired Euler identity to the reciprocal Gamma names.
The identity is cleared and therefore applies even on the integer axis.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaEulerReflectionLimit

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaEulerReflectionHead (negativeSquare denominator sineProduct)
open GaussianGammaEulerReflectionName (qPairF qPairData reciprocal_Euler_pair)
open GaussianGammaEulerApproximationName (cutoff_guards)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaFiniteApproximantName (qF qData)
open GaussianNamedSmallPerturbationTransport (budgetNumerator budgetDenominator denominator_positive)
open GaussianRationalHorner (qmul qmul_canonical positive_product)
open GaussianRationalReciprocal (bound_congr bounded_product bounded_negative)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same distance_symmetric)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus multiply_at multiply_fast product_distance)
open GaussianNameRingLaws (multiply_sample_error equivalent_of_envelope)
open GaussianNameEquivalence (crossEquivalent cross_at)
open GaussianBalancedRadiusArithmetic (unit_monotone)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "gneg" => ComplexLogarithmRemainder.neg
local notation "H" => GaussianGammaC7Name.nameF
local notation "D" => GaussianGammaC7Name.data
local notation "S" => GaussianSineProductName.nameF
local notation "V" => GaussianSineProductName.data
local notation "mu" => GaussianGammaC9Bound.majorant
local notation "a" => GaussianGammaPerturbationExponent.numerator

def cutoff (R p : PTm n) : PTm n :=
  GaussianGammaEulerApproximationName.cutoff p R+GaussianSineProductName.cutoff R p

theorem cutoff_bounds (R p : PTm n) :
    Γ ⊢[PRAAx] le (two*R) (cutoff R p) ⋏ (le (a R) (cutoff R p) ⋏
      (le (GaussianGammaEulerApproximationName.rate R*unit p) (cutoff R p) ⋏
       le (GaussianSineProductName.cutoff R p) (cutoff R p))) := by
  let E := GaussianGammaEulerApproximationName.cutoff p R
  let T := GaussianSineProductName.cutoff R p
  have h := cutoff_guards (Γ := Γ) p R
  have e : Γ ⊢[PRAAx] le E (cutoff R p) := le_add_right E T
  have t : Γ ⊢[PRAAx] le T (cutoff R p) := le_add_left T E
  have u := mul_le_mul_right (Γ := Γ) (GaussianGammaEulerApproximationName.rate R)
    (unit_monotone p (succ p) (le_succ_self p))
  have scaled := le_congr (mul_comm _ _) (mul_comm _ _) u
  exact .andI (le_trans h.andE₁ e) (.andI (le_trans h.andE₂.andE₁ e)
    (.andI (le_trans scaled (le_trans h.andE₂.andE₂ e)) t))

theorem opposite_source (z R B : PTm n) (h : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R B) :
    Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source (gneg z) R B :=
  .andI h.andE₁ (.andI h.andE₂.andE₁ (ComplexLogarithmRemainder.bounded_neg h.andE₂.andE₂))

theorem euler_source (z R B p : PTm n) (h : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R B) :
    Γ ⊢[PRAAx] GaussianGammaEulerConvergence.source z R B (cutoff R p) := by
  have g := cutoff_bounds (Γ := Γ) R p
  exact .andI h (.andI g.andE₁ g.andE₂.andE₁)

theorem cofinal_Q_error (z R B p q : PTm n) (h : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R B)
    (hq : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] distanceBounded (ap2 qF q (qData z B (cutoff R p))) (ap2 H p (D z R B))
      (num 3) (unit p) := by
  let N := cutoff R p
  have g := cutoff_bounds (Γ := Γ) R p
  have hs := euler_source z R B p h
  have hn := (GaussianGammaEulerConvergence.local_source z R B N hs).andE₂.andE₁
  have um : Γ ⊢[PRAAx] le (unit p) (unit q) := unit_monotone p q hq
  have nh : Γ ⊢[PRAAx] le (GaussianGammaEulerApproximationName.rate R*unit p) N := g.andE₂.andE₂.andE₁
  have comparison : Γ ⊢[PRAAx] le (budgetNumerator q p (a R) N (mu R)*unit p)
      (num 3*budgetDenominator q p N) := by
    ipra_le 𝔞 (unit q)*𝔞 (unit p)*sl nh + 𝔞 N*𝔞 (unit p)*sl um using
      unfold budgetNumerator budgetDenominator GaussianGammaEulerApproximationName.rate
      ipra_simps
      ring
  exact distance_radius_mono _ _ _ _ _ _ (denominator_positive q p N hn) (unit_positive p)
    comparison (GaussianGammaEulerConvergence.observation_error q p z R B N hs)

theorem cofinal_Q_bound (z R B p q : PTm n) (h : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R B)
    (hq : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] bounded (ap2 qF q (qData z B (cutoff R p))) (mu R+num 3) one := by
  have u := unit_positive (Γ := Γ) p
  have source := GaussianGammaC9Bound.reciprocal_sample_bound p z R B h
  have compare : Γ ⊢[PRAAx] le (num 3*one) (num 3*unit p) :=
    le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right (num 3) u)
  have close := distance_radius_mono _ _ _ _ (num 3) one u (le_refl one)
    compare (cofinal_Q_error z R B p q h hq)
  have nb := GaussianReconstructionRoots.norm_from_distance _ _ (num 3) one (mu R) one
    (le_refl one) (le_refl one) close source
  exact bound_congr (.eqRefl _) (by ipra_ring) (one_mul one) nb

def pairF : PR 2 := multiplyF H H
def pairData (z R B : PTm n) : PTm n := multiplyData H H (D z R B) (D (gneg z) R B)
def scaledF : PR 2 := multiplyF constantF S
def scaledData (z R B : PTm n) : PTm n := multiplyData constantF S (negativeSquare z B) (V z R B)

theorem fixed_product_error (z R B p : PTm n) (h : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R B) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (multiplyF H H) p (pairData z R B)) (denominator z B (cutoff R p))
      ((multiplyModulus H H (D z R B) (D (gneg z) R B)+one) +
       ((num 3*(mu R+num 3)+mu R*num 3)+two)) (unit p) := by
  let N := cutoff R p
  let Y := qData z B N
  let Z := qData (gneg z) B N
  let k := GaussianFastValueCut.exponent (multiplyModulus qF qF Y Z) p
  let Q := qmul (ap2 qF k Y) (ap2 qF k Z)
  let P := qmul (ap2 H p (D z R B)) (ap2 H p (D (gneg z) R B))
  let hq := ap2 qPairF p (qPairData z B N)
  let d := denominator z B N
  have hb := h.andE₂.andE₁
  have hs := opposite_source z R B h
  have hn := (GaussianGammaEulerConvergence.local_source z R B N (euler_source z R B p h)).andE₂.andE₁
  have uq : Γ ⊢[PRAAx] le p k := le_add_right _ _
  have u := unit_positive (Γ := Γ) p
  have hQ : Γ ⊢[PRAAx] hq ≐ Q :=
    (multiply_at qF qF Y Z p).eqTrans (GaussianExponentialReference.recode_fixed _ (qmul_canonical _ _))
  have pair := cross_at _ _ _ _ p p (reciprocal_Euler_pair z B N hb hn)
  have finite := distance_radius_mono hq d _ _ two (unit p) (positive_product _ _ u u) u
    (le_of_eq_add (d := ConciseIPRA.PTm.zero) (by ipra_ring))
    (distance_congr (.eqRefl hq) (constant_at p d) (.eqRefl _) (.eqRefl _) pair)
  have left : Γ ⊢[PRAAx] distanceBounded Q P (num 3*(mu R+num 3)+mu R*num 3) (unit p) :=
    product_distance _ _ _ _ _ _ _ _ _ u (cofinal_Q_error z R B p k h uq)
      (cofinal_Q_error (gneg z) R B p k hs uq) (cofinal_Q_bound (gneg z) R B p k hs uq)
      (GaussianGammaC9Bound.reciprocal_sample_bound p z R B h)
  have left' := distance_symmetric Q P _ _ u left
  have raw := distance_triangle_same P Q d _ _ _ u left'
    (distance_congr hQ (.eqRefl _) (.eqRefl _) (.eqRefl _) finite)
  exact distance_triangle_same _ P d _ _ _ u
    (multiply_sample_error H H (D z R B) (D (gneg z) R B) p
      (GaussianGammaC7Name.name_regular z R B h) (GaussianGammaC7Name.name_regular (gneg z) R B hs)) raw

theorem coefficient_norm (z R B : PTm n) (h : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R B) :
    Γ ⊢[PRAAx] bounded (negativeSquare z B) (R*R) one := by
  have disk := GaussianGammaEulerHead.fraction_disk z R B h.andE₂.andE₁ h.andE₂.andE₂
  have sq := bound_congr (.eqRefl _) (.eqRefl _) (one_mul one)
    (bounded_product _ _ _ _ _ _ (le_refl _) (le_refl _) disk disk)
  exact bounded_negative _ _ one (le_refl _) sq

theorem fixed_scaled_error (z R B p : PTm n) (h : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R B) :
    Γ ⊢[PRAAx] distanceBounded (ap2 scaledF p (scaledData z R B)) (denominator z B (cutoff R p))
      ((multiplyModulus constantF S (negativeSquare z B) (V z R B)+one)+R*R) (unit p) := by
  let c := negativeSquare z B
  let d := sineProduct z B (cutoff R p)
  let v := ap2 S p (V z R B)
  let u := unit p
  have up := unit_positive (Γ := Γ) p
  have hb := h.andE₂.andE₁
  have hz := h.andE₂.andE₂
  have old := GaussianSineProductName.cofinal_error z R B p (cutoff R p) hb hz
    (cutoff_bounds (Γ := Γ) R p).andE₂.andE₂.andE₂
  have near : Γ ⊢[PRAAx] bounded (qmul c (qsub v d)) (R*R) u :=
    bound_congr (.eqRefl _) (by ipra_ring : Γ ⊢[PRAAx] (R*R)*one ≐ R*R) (one_mul u)
      (bounded_product c (qsub v d) (R*R) one one u (le_refl _) up
        (coefficient_norm z R B h) (distance_symmetric d v one u up old))
  have exactNear := bound_congr (GaussianRationalRoundedPower.multiplication_difference c v d).eqSymm
    (.eqRefl _) (.eqRefl _) near
  have step := multiply_sample_error constantF S c (V z R B) p (constant_regular c)
    (GaussianSineProductName.name_regular z R B hb hz)
  exact distance_triangle_same _ (qmul c v) (qmul c d) _ _ _ up
    (distance_congr (.eqRefl _) (GaussianRationalSyntheticDivision.qmul_congr (constant_at p c) (.eqRefl _))
      (.eqRefl _) (.eqRefl _) step) exactNear

def envelope (z R B : PTm n) : PTm n :=
  ((multiplyModulus H H (D z R B) (D (gneg z) R B)+one) +
    ((num 3*(mu R+num 3)+mu R*num 3)+two)) +
    ((multiplyModulus constantF S (negativeSquare z B) (V z R B)+one)+R*R)

@[simp] theorem subst_pairData {l : ℕ} (σ : Fin n → PTm l) (z R B : PTm n) :
    Syn.subst σ (pairData z R B) = pairData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) := by
  simp [pairData]

@[simp] theorem subst_scaledData {l : ℕ} (σ : Fin n → PTm l) (z R B : PTm n) :
    Syn.subst σ (scaledData z R B) = scaledData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) := by
  simp [scaledData,GaussianGammaEulerReflectionHead.negativeSquare,GaussianSineProductName.data]

@[simp] theorem subst_envelope {l : ℕ} (σ : Fin n → PTm l) (z R B : PTm n) :
    Syn.subst σ (envelope z R B) = envelope (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) := by
  simp [envelope,GaussianGammaEulerReflectionHead.negativeSquare,GaussianSineProductName.data]

theorem original_reciprocal_reflection_product (z R B : PTm n)
    (h : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R B) :
    Γ ⊢[PRAAx] crossEquivalent pairF scaledF (pairData z R B) (scaledData z R B) := by
  have hs := opposite_source z R B h
  have lp := GaussianGammaC7Name.name_regular z R B h
  have rp := GaussianGammaC7Name.name_regular (gneg z) R B hs
  have sp := GaussianSineProductName.name_regular z R B h.andE₂.andE₁ h.andE₂.andE₂
  apply equivalent_of_envelope pairF scaledF (pairData z R B) (scaledData z R B) (envelope z R B)
    (multiply_fast _ _ _ _ lp rp) (multiply_fast _ _ _ _ (constant_regular _) sp)
  refine .allI ?_
  let z' := Syn.shift z
  let R' := Syn.shift R
  let B' := Syn.shift B
  have h' : Γ.map Fm.shift ⊢[PRAAx] GaussianGammaCanonicalExponent.source z' R' B' := by
    simpa only [z',R',B',Syn.shift,Fm.shift,GaussianGammaCanonicalExponent.subst_source] using h.shift
  have l := fixed_product_error z' R' B' (var 0) h'
  have r := fixed_scaled_error z' R' B' (var 0) h'
  have d : Γ.map Fm.shift ⊢[PRAAx] distanceBounded
      (ap2 pairF (var 0) (pairData z' R' B')) (ap2 scaledF (var 0) (scaledData z' R' B'))
      (envelope z' R' B') (unit (var 0)) :=
    distance_triangle_same _ _ _ _ _ _ (unit_positive (var 0)) l
      (distance_symmetric _ _ _ _ (unit_positive (var 0)) r)
  change Γ.map Fm.shift ⊢[PRAAx] distanceBounded
    (ap2 pairF (var 0) (Syn.shift (pairData z R B))) (ap2 scaledF (var 0) (Syn.shift (scaledData z R B)))
    (Syn.shift (envelope z R B)) (unit (var 0))
  simp only [Syn.shift,subst_pairData,subst_scaledData,subst_envelope]
  exact d

theorem actual_original_reciprocal_Gamma_reflection_product_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (GaussianGammaCanonicalExponent.source (var 0) (var 1) (var 2) ⟶
        crossEquivalent pairF scaledF (pairData (var 0) (var 1) (var 2)) (scaledData (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (original_reciprocal_reflection_product _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaEulerReflectionLimit

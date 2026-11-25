import IPRADerivations.Analysis.GaussianBinetLaplaceDomination
import IPRADerivations.Analysis.GaussianCompactScalarMajorant

/-!
# A scalar majorant for the original Binet Laplace samples

The explicit rational majorant is the actual nonnegative real decay
sample divided by twelve, with nine dyadic observation errors. Its
embedding differs from one twelfth of the original decay observation
by at most ten dyadic errors.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceScalarMajorant

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianBinetLaplaceDomination (realDecay realNumerator realDenominator)
open GaussianBinetLaplaceIntegrand (input cofinalF cofinalData)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEulerDecayMesh (observation)
open GaussianEulerDecayOrder (signedTime original_decay_nonnegative_representative)
open GaussianEulerIntegrandName (decayPoint decayF decayData)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianPositiveRealArithmetic (positive natural_representation)
open GaussianRationalHorner (positive_product qadd qmul qzero)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalSumMajorant (majorized from_representation)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalSyntheticBounds (natCode natCode_represents)
open GaussianRealExponentialPositiveRepresentative
  (positiveF positiveData sample_nonnegative sample_canonical)
open RationalGaussianEmbedding (embed canonical_axis_roundtrip)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "twelve" => num 12
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

private theorem twelve_positive : Γ ⊢[PRAAx] le one (twelve : PTm n) := by ipra_le 11

def twelfth : PTm n := GaussianPositiveRationalLogarithm.fraction one twelve

theorem decay_nonpositive (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] RationalArgmin.rationalLE (fstT (decayPoint a b)) (natCode zero) := by
  let c := ComplexLogarithmRemainder.scale a ComplexLogarithmRemainder.oneCode
  have hr := GaussianRationalMetric.qnegative_represents (GaussianPositiveRationalLogarithm.fraction a b) c b
    (GaussianRationalHorner.ofGaussian_represents c b hb)
  have real : Γ ⊢[PRAAx] ZT.eq (ComplexLogarithmRemainder.re (ComplexLogarithmRemainder.neg c)) (-ZT.ofNat a) := by
    apply ZT.derive
    simp only [c,GaussianRootAlgebra.re_neg,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_one]
    ipra_simps
    ring
  have rep := GaussianRationalHorner.scalar_congr (.eqRefl _) real (.eqRefl _) hr.andE₁
  apply RationalArithmetic.order_of_representations _ _ _ _ b one rep (natCode_represents zero) hb (le_refl one)
  apply zle_of_toZ a
  simp only [ZT.toZ_mul, ZT.toZ_neg, ZT.toZ_ofNat]
  ipra_simps
  ring

theorem original_decay_unit_bound (p a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] bounded (observation a b p) (unit p+one) (unit p) :=
  GaussianBinetLaplaceExponential.original_unit_bound _ _ _
    (GaussianGammaFiniteApproximantName.exponential_input _ _
      (GaussianGammaCanonicalExponent.constant_regular _)) (decay_nonpositive a b hb)

private theorem representative_error (p a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] distanceBounded (realDecay p a b) (observation a b p) two (unit p) :=
  distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive p) (unit_positive p))
    (unit_positive p) (le_of_eq_add (d := zero) (by ipra_ring))
    (GaussianNameEquivalence.cross_at positiveF decayF (positiveData (signedTime a b))
      (decayData a b) p p (original_decay_nonnegative_representative a b hb))

private theorem representative_numerator_bound (p a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] le (realNumerator (realDecay p a b)) (num 4*realDenominator (realDecay p a b)) := by
  let z := realDecay p a b
  let M := realNumerator z
  let E := realDenominator z
  let U := unit p
  have hu := unit_positive (Γ := Γ) p
  have hE : Γ ⊢[PRAAx] le one E := RationalArgmin.denominator_positive _
  have hpos := sample_nonnegative (Γ := Γ) (signedTime a b) p
  have hcan := sample_canonical (Γ := Γ) (signedTime a b) p
  have re := RationalGaussianEmbedding.embed_from_representation (fstT z) (ZT.ofNat M) E
    (natural_representation _ hpos.andE₂)
  have rep := GaussianRationalHorner.represents_congr (canonical_axis_roundtrip z hcan hpos.andE₁)
    (GaussianRootAlgebra.equal_refl _) (.eqRefl _) re
  have raw := GaussianReconstructionRoots.norm_from_distance z (observation a b p) two U (U+one) U hu hu
    (representative_error p a b hb) (original_decay_unit_bound p a b hb)
  have small : Γ ⊢[PRAAx] bounded z (num 4) one := by
    apply bounded_radius_mono _ _ _ _ _ (positive_product _ _ hu hu) (le_refl one) ?_ raw
    ipra_le 3*𝔞(U)*sl hu
  have sq := GaussianRationalMetric.bounded_to_cleared _ _ _ _ _ hE (le_refl one) rep small
  have norm := GaussianDominantPairAlgebra.radius_numerator_norm (Γ := Γ) M
  exact nat_sqrt_mono
    (le_congr ((congrMul (.eqRefl _) norm).eqTrans (by ipra_ring)) (by ipra_ring) sq)

def scalar (p a b : PTm n) : PTm n :=
  RationalArithmetic.add (RationalArithmetic.multiply (fraction one twelve) (fstT (realDecay p a b)))
    (fraction (num 9) (unit p))

@[simp] theorem subst_scalar {m : ℕ} (σ : Fin n → PTm m) (p a b : PTm n) :
    Syn.subst σ (scalar p a b) = scalar (Syn.subst σ p) (Syn.subst σ a) (Syn.subst σ b) := by
  simp [scalar,realDecay,signedTime,one]

private theorem scalar_represents (p a b : PTm n) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (scalar p a b)
      (ZT.ofNat (realNumerator (realDecay p a b)*unit p+num 108*realDenominator (realDecay p a b)))
      ((twelve*realDenominator (realDecay p a b))*unit p) := by
  let z := realDecay p a b
  let M := realNumerator z
  let E := realDenominator z
  let U := unit p
  let f := fraction one (twelve : PTm n)
  let w := fraction (num 9) U
  have base := natural_representation (Γ := Γ) (fstT z) (sample_nonnegative (signedTime a b) p).andE₂
  have rate := fraction_represents (Γ := Γ) one (twelve : PTm n) twelve_positive
  have term := RationalRepresentations.represents_multiply f (fstT z) (ZT.ofNat one) (ZT.ofNat M) twelve E rate base
  have err := fraction_represents (Γ := Γ) (num 9) U (unit_positive p)
  have out := RationalRepresentations.represents_add (RationalArithmetic.multiply f (fstT z)) w _ _
    (twelve*E) U term err
  refine GaussianRationalHorner.scalar_congr (.eqRefl _) ?_ (.eqRefl _) out
  apply ZT.derive
  dsimp only [M,E,U,z]
  simp only [ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat]
  ipra_simps
  ring

theorem cofinal_majorized (p X Y D sign R T A B : PTm n)
    (h : Γ ⊢[PRAAx] input X Y D sign R T A B) :
    Γ ⊢[PRAAx] majorized (ap2 cofinalF p (cofinalData X Y D sign R T A B))
      (scalar p (X*A) (D*B)) := by
  let U := unit p
  let j := GaussianBinetLaplaceDomination.complexClock p X Y D sign R T A B
  let J := unit j
  let z := realDecay p (X*A) (D*B)
  let M := realNumerator z
  let E := realDenominator z
  have hu := unit_positive (Γ := Γ) p
  have hj := unit_positive (Γ := Γ) j
  have hE : Γ ⊢[PRAAx] le one E := RationalArgmin.denominator_positive _
  have hb := positive_product _ _ h.andE₁.andE₁.andE₂ h.andE₂.andE₁
  have hM : Γ ⊢[PRAAx] le M (num 4*E) := representative_numerator_bound p (X*A) (D*B) hb
  have hg : Γ ⊢[PRAAx] le U J := GaussianExponentialReference.unit_monotone
    (GaussianBinetLaplaceDomination.clock_later p X Y D sign R T A B)
  have hn := positive_product _ _ (positive_product _ _ twelve_positive hE) hu
  have raw := GaussianBinetLaplaceDomination.cofinal_observation_bound p p X Y D sign R T A B h
  have h1 : Γ ⊢[PRAAx] le (M*(J*U)+(num 3*U+J)*E) (J*(M*U+num 4*E)) := by
    ipra_le 3*𝔞(E)*sl hg
  have h2 : Γ ⊢[PRAAx] le (U*(J+twelve)) (J*(U+twelve)) := by
    ipra_le 12*sl hg
  have first : Γ ⊢[PRAAx] le (((M*(J*U)+(num 3*U+J)*E)*(J+twelve))*U)
      ((M*U+num 4*E)*(U+twelve)*J*J) :=
    le_congr (by ipra_ring) (by ipra_ring) (le_mul_mono h1 h2)
  have second : Γ ⊢[PRAAx] le ((M*U+num 4*E)*(U+twelve)) (U*(M*U+num 108*E)) := by
    ipra_le 12*𝔞(U)*sl hM + 48*𝔞(E)*sl hu + 8*𝔞(E)*𝔞(U)
  have tight : Γ ⊢[PRAAx] bounded (ap2 cofinalF p (cofinalData X Y D sign R T A B))
      (M*U+num 108*E) ((twelve*E)*U) := by
    apply bounded_radius_mono _ _ _ _ _ (positive_product _ _
      (positive_product _ _ hE (positive_product _ _ hj hu)) (positive_product _ _ twelve_positive hj)) hn ?_ raw
    change Γ ⊢[PRAAx] le (((M*(J*U)+(num 3*U+J)*E)*(J+twelve))*((twelve*E)*U))
      ((M*U+num 108*E)*((E*(J*U))*(twelve*J)))
    ipra_le 12*𝔞(E)*sl first + 12*𝔞(E)*𝔞(J)*𝔞(J)*sl second
  have rep := scalar_represents (Γ := Γ) p (X*A) (D*B)
  exact from_representation _ _ _ _ hn
    (GaussianRationalL1.nonnegative_of_representation _ _ _ hn rep) rep tight

theorem fraction_norm (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] bounded (GaussianPositiveRationalLogarithm.fraction a b) a b := by
  let c := ComplexLogarithmRemainder.scale a ComplexLogarithmRemainder.oneCode
  have norm : Γ ⊢[PRAAx] ComplexLogarithmRemainder.normSq c ≐ a*a :=
    (ComplexLogarithmRemainder.normSq_scale a ComplexLogarithmRemainder.oneCode).eqTrans
    ((congrMul (.eqRefl _) ComplexLogarithmRemainder.normSq_one).eqTrans (by ipra_ring))
  exact GaussianRationalMetric.bounded_of_cleared _ c b a b hb hb
    (GaussianRationalHorner.ofGaussian_represents _ _ hb)
    (le_congr (congrMul (.eqRefl _) norm.eqSymm) (by ipra_ring) (le_refl ((b*b)*(a*a))))

theorem scalar_observation_distance (p a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] distanceBounded (embed (scalar p a b))
      (qmul (twelfth : PTm n) (observation a b p)) (num 10) (unit p) := by
  let U := unit p
  let r := realDecay p a b
  let v := observation a b p
  let w := GaussianPositiveRationalLogarithm.fraction (num 9) U
  let L := (twelfth : PTm n)
  have hu := unit_positive (Γ := Γ) p
  have rep := sample_nonnegative (Γ := Γ) (signedTime a b) p
  have ec := canonical_axis_roundtrip r (sample_canonical (signedTime a b) p) rep.andE₁
  have bind : Γ ⊢[PRAAx] embed (scalar p a b) ≐ qadd (qmul L r) w :=
    (RationalGaussianEmbedding.embed_add _ _).eqTrans
      (GaussianRationalSyntheticDivision.qadd_congr
        ((RationalGaussianEmbedding.embed_multiply _ _).eqTrans (GaussianRationalSyntheticDivision.qmul_congr
          (GaussianEulerDecayOrder.fraction_embedding one twelve twelve_positive) ec))
        (GaussianEulerDecayOrder.fraction_embedding (num 9) U hu))
  have hL : Γ ⊢[PRAAx] bounded L one (twelve : PTm n) :=
    fraction_norm one twelve twelve_positive
  have prod := bounded_product L _ one twelve two U twelve_positive hu hL (representative_error p a b hb)
  have d := positive_product _ _ twelve_positive hu
  have near : Γ ⊢[PRAAx] distanceBounded (qmul L r) (qmul L v) one U :=
    distance_radius_mono _ _ _ _ _ _ d hu (by ipra_le 10*𝔞(U))
      (bound_congr (GaussianRationalRoundedPower.multiplication_difference L r v).eqSymm (.eqRefl _) (.eqRefl _) prod)
  have hw := fraction_norm (num 9) U hu
  have noise := (GaussianReconstructionRoots.distance_zero_iff w (num 9) U hu).iffMpr hw
  have full := GaussianNameArithmetic.sum_distance (qmul L r) (qmul L v) w qzero one (num 9) U hu near noise
  have rhs : Γ ⊢[PRAAx] qadd (qmul L v) qzero ≐ qmul L v :=
    GaussianReciprocalHorner.qadd_zero_right (qmul L v) (GaussianRationalHorner.qmul_canonical L v)
  exact distance_congr bind.eqSymm rhs (by ipra_ring) (.eqRefl _) full

theorem actual_Binet_Laplace_scalar_majorant_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (input (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      majorized (ap2 cofinalF (var 0) (cofinalData (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)))
        (scalar (var 0) (var 1*var 7) (var 3*var 8))) :=
  closeUniv 9 (.impI (cofinal_majorized _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceScalarMajorant

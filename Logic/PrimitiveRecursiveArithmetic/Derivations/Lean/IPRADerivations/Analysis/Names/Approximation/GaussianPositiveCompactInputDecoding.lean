import IPRADerivations.Analysis.Names.Approximation.GaussianUnitIntervalInputDecoding
import IPRADerivations.DiophantineNumberTheory.Coprime

/-!
# Actual positive rational decoding on an arbitrary compact

The decoder uses the SAME scalar numerator and denominator as the unit
input decoder. An exact reciprocal lower margin gives positivity; the
supplied Euclidean upper radius gives the genuine native upper endpoint.
The original raw code equals its decoded fraction after canonical
recoding, and equals that fraction literally whenever already canonical.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianPositiveCompactInputDecoding

open_ipra
open GaussianUnitIntervalInputDecoding (numerator denominator scalarNumerator denominator_positive)
open GaussianRationalHorner (positive_product canonical_unique)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianPositiveRationalLogarithm (fraction)
open RationalGaussianEmbedding (axis embed native)
open RationalValueBounds (upper)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def source (q E T : PTm n) : Fm PTm n := axis q ⋏ (le one E ⋏
  (upper (GaussianEuclideanDistanceName.fraction one E) (fstT q) zero one ⋏ bounded q T one))
ipra_subst source

theorem lower_native (q E T : PTm n) (hs : Γ ⊢[PRAAx] source q E T) : Γ ⊢[PRAAx]
    le (denominator q+E*(scalarNumerator q).neg) (E*(scalarNumerator q).pos) := by
  have actual := RationalUpperRepresentation.upper_from_representations _ _ E (denominator q) zero one
    (ZT.ofNat one) (scalarNumerator q) (GaussianEuclideanDistanceName.fraction_represents one E hs.andE₂.andE₁)
    (RationalRepresentations.represents_self (fstT q)) hs.andE₂.andE₂.andE₁
  have e := zle_toZ actual
  apply le_of_eq_add (d := PolynomialBisection.slack
    (ZT.ofNat (one*denominator q)*ZT.ofNat one)
    (ZT.ofNat (one*E)*scalarNumerator q+ZT.ofNat (zero*E*denominator q)))
  apply deriveNat
  simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat] at e
  simp only [PolynomialBisection.slack,scalarNumerator,ZT.toZ] at e ⊢
  ipra_simps
  linear_combination -e

theorem numerator_order (q E T : PTm n) (hs : Γ ⊢[PRAAx] source q E T) : Γ ⊢[PRAAx]
    le (scalarNumerator q).neg (scalarNumerator q).pos :=
  RationalValueBounds.positive_cancel hs.andE₂.andE₁ (le_trans (le_add_left _ _) (lower_native q E T hs))

theorem decoded_lower (q E T : PTm n) (hs : Γ ⊢[PRAAx] source q E T) : Γ ⊢[PRAAx]
    le (denominator q) (E*numerator q) := by
  unfold numerator
  ipra_le sl (lower_native q E T hs) with 𝔞 E*natEq (eq_add_of_le (numerator_order q E T hs))

theorem decoded_positive (q E T : PTm n) (hs : Γ ⊢[PRAAx] source q E T) : Γ ⊢[PRAAx]
    le one (numerator q) := by
  have bound := le_trans (denominator_positive q) (decoded_lower q E T hs)
  refine .orE (zero_or_succ (numerator q)) ?_ ?_
  · have e : (numerator q ≐ zero)::Γ ⊢[PRAAx] E*numerator q ≐ zero :=
      (congrMul (.eqRefl E) Prf.hyp0).eqTrans (mul_zero E)
    have bad : (numerator q ≐ zero)::Γ ⊢[PRAAx] le one zero := le_congr (.eqRefl _) e bound.wk
    exact .botE _ (succ_ne_zero ((monus_zero one).eqSymm.eqTrans bad))
  · exact Order.zero_lt_of_eq_succ Prf.hyp0

theorem fraction_recode (q E T : PTm n) (hs : Γ ⊢[PRAAx] source q E T) : Γ ⊢[PRAAx]
    fraction (numerator q) (denominator q) ≐ GaussianFastValueCut.recode q := by
  let a := numerator q
  let b := denominator q
  have hb := denominator_positive (Γ := Γ) q
  have sign := natEq (eq_add_of_le (numerator_order q E T hs))
  have nativeEq : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (native (scalarNumerator q))
      (ComplexLogarithmRemainder.scale a ComplexLogarithmRemainder.oneCode) := by
    apply GaussianRootAlgebra.equal_of_values
    · simp only [native,ComplexLogarithmRemainder.eval_re_code,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_one]
      dsimp only [a,numerator]
      simp only [scalarNumerator,ZT.toZ] at sign ⊢
      ipra_simps
      linear_combination sign
    · simp only [native,ComplexLogarithmRemainder.eval_im_code,GaussianRootAlgebra.im_scale,GaussianRootAlgebra.im_one,ZT.toZ_ofNat]
      ipra_simps
      ring
  have actual := RationalGaussianEmbedding.embed_from_representation (Γ := Γ) (fstT q) (scalarNumerator q) b (RationalRepresentations.represents_self _)
  have frac : Γ ⊢[PRAAx] fraction a b ≐ embed (fstT q) :=
    canonical_unique _ _ _ b (GaussianRationalHorner.ofGaussian_canonical _ _ hb) (RationalGaussianEmbedding.embed_canonical _) hb
      (GaussianRationalHorner.ofGaussian_represents _ _ hb)
      (GaussianRationalHorner.represents_congr (.eqRefl _) nativeEq (.eqRefl _) actual)
  have canonical : Γ ⊢[PRAAx] GaussianFastValueCut.recode q ≐ GaussianTranslatedNonconstant.recode q :=
    canonical_unique _ _ _ _ (GaussianFastValueCut.recode_canonical q) (GaussianTranslatedNonconstant.recode_canonical q)
      (GaussianRationalL1.raw_den_positive q) (GaussianFastValueCut.recode_represents q) (GaussianTranslatedNonconstant.recode_represents q)
  exact frac.eqTrans ((RationalGaussianEmbedding.axis_roundtrip q hs.andE₁).eqSymm.eqTrans canonical.eqSymm)

theorem decoded_upper (q E T : PTm n) (hs : Γ ⊢[PRAAx] source q E T) : Γ ⊢[PRAAx]
    le (numerator q) (T*denominator q) := by
  have hb := denominator_positive (Γ := Γ) q
  have bound := GaussianRationalReciprocal.bound_congr (fraction_recode q E T hs).eqSymm (.eqRefl _) (.eqRefl _)
    ((GaussianFastValueCut.recode_bound_iff q T one (le_refl one)).iffMpr hs.andE₂.andE₂.andE₂)
  have clear := GaussianRationalMetric.bounded_to_cleared _ _ (denominator q) T one hb (le_refl one)
    (GaussianRationalHorner.ofGaussian_represents _ _ hb) bound
  have norm : Γ ⊢[PRAAx] ComplexLogarithmRemainder.normSq (ComplexLogarithmRemainder.scale (numerator q) ComplexLogarithmRemainder.oneCode) ≐
      numerator q*numerator q :=
    (ComplexLogarithmRemainder.normSq_scale _ _).eqTrans
      ((congrMul (.eqRefl _) ComplexLogarithmRemainder.normSq_one).eqTrans (by ipra_ring))
  exact DiophantineNumberTheory.Coprime.le_of_sq_le (le_congr
    ((congrMul (.eqRefl _) norm).eqTrans (by ipra_ring)) (by ipra_ring) clear)

theorem decoded_source (q E T : PTm n) (hs : Γ ⊢[PRAAx] source q E T) : Γ ⊢[PRAAx]
    GaussianCompactLogarithmBounds.domain (numerator q) (denominator q) E T :=
  .andI (.andI (decoded_positive q E T hs) (denominator_positive q)) (.andI (decoded_lower q E T hs) (decoded_upper q E T hs))

theorem fraction_exact (q E T : PTm n) (hs : Γ ⊢[PRAAx] source q E T)
    (hc : Γ ⊢[PRAAx] GaussianRationalHorner.canonical q) : Γ ⊢[PRAAx]
    fraction (numerator q) (denominator q) ≐ q :=
  (fraction_recode q E T hs).eqTrans (GaussianExponentialReference.recode_fixed q hc)

theorem actual_positive_compact_raw_input_decoding_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) (var 2) ⟶ (GaussianCompactLogarithmBounds.domain
      (numerator (var 0)) (denominator (var 0)) (var 1) (var 2) ⋏
      fraction (numerator (var 0)) (denominator (var 0)) ≐ GaussianFastValueCut.recode (var 0))) :=
  closeUniv 3 (.impI (.andI (decoded_source _ _ _ Prf.hyp0) (fraction_recode _ _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianPositiveCompactInputDecoding

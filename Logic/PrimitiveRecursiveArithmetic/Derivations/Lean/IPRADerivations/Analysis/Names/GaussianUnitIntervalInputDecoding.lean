import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerUnitCompactTimeBounds
import IPRADerivations.Analysis.RationalArithmetic.RationalUpperRepresentation
import IPRADerivations.Analysis.RationalArithmetic.RationalGaussianEmbedding
import IPRADerivations.Analysis.Names.GaussianFastValueCut

/-!
# Decode arbitrary actual Gaussian observations on a positive unit compact

Only real-axis membership and the exact scalar inequalities 1/E <= q
and q <= 1-1/E are input. The original raw scalar denominator and the
positive difference of its signed numerator parts form a genuine
positive fraction. Its equality to the actual canonical recoding and
zero distance to the original raw observation are proved internally.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianUnitIntervalInputDecoding

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open RationalSupMetric (numeratorOf denominatorOf)
open RationalGaussianEmbedding (axis embed native)
open GaussianRationalHorner (represents canonical_unique positive_product)
open GaussianRationalMetric (distanceBounded)
open RationalValueBounds (upper)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def scalarNumerator (q : PTm n) : ZT n := numeratorOf (fstT q)
def numerator (q : PTm n) : PTm n := monus (scalarNumerator q).pos (scalarNumerator q).neg
def denominator (q : PTm n) : PTm n := denominatorOf (fstT q)
def lowerPoint (E : PTm n) : PTm n := GaussianEuclideanDistanceName.fraction one E
def upperPoint (E : PTm n) : PTm n := GaussianEuclideanDistanceName.fraction (monus E one) E
def source (q E : PTm n) : Fm PTm n := axis q ⋏ (le one E ⋏
  (upper (lowerPoint E) (fstT q) zero one ⋏ upper (fstT q) (upperPoint E) zero one))

@[simp] theorem subst_scalarNumerator {m : ℕ} (σ : Fin n → PTm m) (q : PTm n) :
    (scalarNumerator q).subst σ = scalarNumerator (Syn.subst σ q) := by simp [scalarNumerator,numeratorOf,ZT.subst]
@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (q : PTm n) :
    Syn.subst σ (numerator q) = numerator (Syn.subst σ q) := by simp [numerator,scalarNumerator,numeratorOf]
@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (q : PTm n) :
    Syn.subst σ (denominator q) = denominator (Syn.subst σ q) := by simp [denominator,denominatorOf]
@[simp] theorem subst_lowerPoint {m : ℕ} (σ : Fin n → PTm m) (E : PTm n) :
    Syn.subst σ (lowerPoint E) = lowerPoint (Syn.subst σ E) := by simp [lowerPoint]
@[simp] theorem subst_upperPoint {m : ℕ} (σ : Fin n → PTm m) (E : PTm n) :
    Syn.subst σ (upperPoint E) = upperPoint (Syn.subst σ E) := by simp [upperPoint]
@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (q E : PTm n) :
    (source q E).subst σ = source (Syn.subst σ q) (Syn.subst σ E) := by simp [source]

theorem denominator_positive (q : PTm n) : Γ ⊢[PRAAx] le one (denominator q) := RationalArgmin.denominator_positive _

private theorem lower_native (q E : PTm n) (h : Γ ⊢[PRAAx] source q E) : Γ ⊢[PRAAx]
    le (denominator q+E*(scalarNumerator q).neg) (E*(scalarNumerator q).pos) := by
  have actual := RationalUpperRepresentation.upper_from_representations _ _ E (denominator q) zero one
    (ZT.ofNat one) (scalarNumerator q) (GaussianEuclideanDistanceName.fraction_represents one E h.andE₂.andE₁)
    (RationalRepresentations.represents_self (fstT q)) h.andE₂.andE₂.andE₁
  have e := zle_toZ actual
  apply le_of_eq_add (d := PolynomialBisection.slack
    (ZT.ofNat (one * denominator q) * ZT.ofNat one)
    (ZT.ofNat (one * E) * scalarNumerator q + ZT.ofNat (zero * E * denominator q)))
  apply deriveNat
  simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat] at e
  simp only [PolynomialBisection.slack,scalarNumerator,ZT.toZ] at e ⊢
  ipra_simps
  linear_combination -e

theorem numerator_order (q E : PTm n) (h : Γ ⊢[PRAAx] source q E) : Γ ⊢[PRAAx]
    le (scalarNumerator q).neg (scalarNumerator q).pos :=
  RationalValueBounds.positive_cancel h.andE₂.andE₁
    (le_trans (le_add_left _ _) (lower_native q E h))

theorem decoded_lower (q E : PTm n) (h : Γ ⊢[PRAAx] source q E) : Γ ⊢[PRAAx]
    le (denominator q) (E*numerator q) := by
  have e := natEq (eq_add_of_le (numerator_order q E h))
  unfold numerator
  ipra_le sl (lower_native q E h) with 𝔞(E)*e

theorem decoded_positive (q E : PTm n) (h : Γ ⊢[PRAAx] source q E) : Γ ⊢[PRAAx] le one (numerator q) := by
  have bound := le_trans (denominator_positive q) (decoded_lower q E h)
  refine .orE (zero_or_succ (numerator q)) ?_ ?_
  · have e : (numerator q ≐ zero)::Γ ⊢[PRAAx] E*numerator q ≐ zero :=
      (congrMul (.eqRefl E) Prf.hyp0).eqTrans (mul_zero E)
    have bad : (numerator q ≐ zero)::Γ ⊢[PRAAx] le one zero := le_congr (.eqRefl _) e bound.wk
    exact .botE _ (succ_ne_zero ((monus_zero one).eqSymm.eqTrans bad))
  · exact le_congr (.eqRefl _) Prf.hyp0.eqSymm (zero_lt_succ (pred (numerator q)))

theorem decoded_upper (q E : PTm n) (h : Γ ⊢[PRAAx] source q E) : Γ ⊢[PRAAx]
    le (E*numerator q+denominator q) (E*denominator q) := by
  have actual := RationalUpperRepresentation.upper_from_representations _ _ (denominator q) E zero one
    (scalarNumerator q) (ZT.ofNat (monus E one)) (RationalRepresentations.represents_self (fstT q))
    (GaussianEuclideanDistanceName.fraction_represents _ E h.andE₂.andE₁) h.andE₂.andE₂.andE₂
  have e := zle_toZ actual
  have en := natEq (eq_add_of_le (numerator_order q E h))
  have ee := natEq (eq_add_of_le h.andE₂.andE₁)
  apply le_of_eq_add (d := PolynomialBisection.slack
    (ZT.ofNat (one * E) * scalarNumerator q)
    (ZT.ofNat (one * denominator q) * ZT.ofNat (monus E one) + ZT.ofNat (zero * denominator q * E)))
  apply deriveNat
  simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat] at e
  unfold numerator
  simp only [PolynomialBisection.slack,scalarNumerator,ZT.toZ] at e en ⊢
  ipra_simps
  linear_combination -e+𝔞(E)*en+𝔞(denominator q)*ee

theorem decoded_strict (q E : PTm n) (h : Γ ⊢[PRAAx] source q E) : Γ ⊢[PRAAx] lt (numerator q) (denominator q) := by
  have upperBound := decoded_upper q E h
  have hd := denominator_positive (Γ := Γ) q
  refine .orE (lt_or_le (numerator q) (denominator q)) Prf.hyp0 ?_
  have order : (le (denominator q) (numerator q))::Γ ⊢[PRAAx] le (E*denominator q) (E*numerator q) :=
    le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right E Prf.hyp0)
  have bad : (le (denominator q) (numerator q))::Γ ⊢[PRAAx] lt (E*denominator q) (E*denominator q) :=
    le_trans (le_congr (by ipra_ring) (.eqRefl _) (add_le_add₂ order hd.wk)) upperBound.wk
  exact le_lt_absurd _ (le_refl _) bad

theorem decoded_source (q E : PTm n) (h : Γ ⊢[PRAAx] source q E) : Γ ⊢[PRAAx]
    GaussianEulerUnitCompactTimeBounds.source (numerator q) (denominator q) E :=
  .andI (.andI (decoded_positive q E h) (decoded_strict q E h))
    (.andI h.andE₂.andE₁ (.andI (decoded_lower q E h) (decoded_upper q E h)))

theorem fraction_recode (q E : PTm n) (h : Γ ⊢[PRAAx] source q E) : Γ ⊢[PRAAx]
    GaussianPositiveRationalLogarithm.fraction (numerator q) (denominator q) ≐ GaussianFastValueCut.recode q := by
  let a := numerator q
  let b := denominator q
  have hb := denominator_positive (Γ := Γ) q
  have signed := natEq (eq_add_of_le (numerator_order q E h))
  have nativeEq : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (native (scalarNumerator q))
      (ComplexLogarithmRemainder.scale a ComplexLogarithmRemainder.oneCode) := by
    apply GaussianRootAlgebra.equal_of_values
    · simp only [native,ComplexLogarithmRemainder.eval_re_code,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_one]
      dsimp only [a,numerator]
      simp only [scalarNumerator,ZT.toZ] at signed ⊢
      ipra_simps
      linear_combination signed
    · simp only [native,ComplexLogarithmRemainder.eval_im_code,GaussianRootAlgebra.im_scale,GaussianRootAlgebra.im_one,ZT.toZ_ofNat]
      ipra_simps
      ring
  have actual := RationalGaussianEmbedding.embed_from_representation (Γ := Γ) (fstT q) (scalarNumerator q) b (RationalRepresentations.represents_self _)
  have frac : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.fraction a b ≐ embed (fstT q) :=
    canonical_unique _ _ _ b (GaussianRationalHorner.ofGaussian_canonical _ _ hb) (RationalGaussianEmbedding.embed_canonical _) hb
      (GaussianRationalHorner.ofGaussian_represents _ _ hb)
      (GaussianRationalHorner.represents_congr (.eqRefl _) nativeEq (.eqRefl _) actual)
  have canonical : Γ ⊢[PRAAx] GaussianFastValueCut.recode q ≐ GaussianTranslatedNonconstant.recode q :=
    canonical_unique _ _ _ _ (GaussianFastValueCut.recode_canonical q) (GaussianTranslatedNonconstant.recode_canonical q)
      (GaussianRationalL1.raw_den_positive q) (GaussianFastValueCut.recode_represents q) (GaussianTranslatedNonconstant.recode_represents q)
  exact frac.eqTrans ((RationalGaussianEmbedding.axis_roundtrip q h.andE₁).eqSymm.eqTrans canonical.eqSymm)

theorem decoded_distance (q E : PTm n) (h : Γ ⊢[PRAAx] source q E) : Γ ⊢[PRAAx]
    distanceBounded (GaussianPositiveRationalLogarithm.fraction (numerator q) (denominator q)) q zero one :=
  GaussianRationalDistanceOrder.distance_congr (fraction_recode q E h).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) (GaussianFastValueCut.recode_distance q)

theorem actual_unit_interval_raw_input_decoding_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (source (var 0) (var 1) ⟶ (GaussianEulerUnitCompactTimeBounds.source (numerator (var 0)) (denominator (var 0)) (var 1) ⋏
      GaussianPositiveRationalLogarithm.fraction (numerator (var 0)) (denominator (var 0)) ≐ GaussianFastValueCut.recode (var 0))) :=
  closeUniv 2 (.impI (.andI (decoded_source _ _ Prf.hyp0) (fraction_recode _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianUnitIntervalInputDecoding

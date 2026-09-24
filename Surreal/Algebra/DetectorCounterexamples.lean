import Surreal.Algebra.PolynomialConstantRigidity
import Surreal.Algebra.DiophantineConstants
import Surreal.Algebra.IntersectiveDetector

/-!
# Polynomial counterexamples to the constant-term detector

The polynomial models of `odg:def:rem:rootneeded`: the coefficient
pullback `ℤ + X ℚ[X]` has a root-free quotient at `X = -1`, although
`1 + X` has constant coefficient one. The integer polynomial ring gives
the second counterexample. Here `X` is a formal indeterminate; these
results do not require an identification with a surreal monomial.
-/

namespace Surreal.DetectorCounterexamples

open Polynomial IntersectivePolynomial

noncomputable section

/-- The rational polynomial ring with integer constant coefficient. -/
def rationalPullback : Subring ℚ[X] :=
  CoefficientPullback.subring (evalRingHom 0) (Int.castRingHom ℚ)

/-- The coefficient pullback is literally `ℤ + X ℚ[X]`. -/
theorem mem_rationalPullback_iff (p : ℚ[X]) :
    p ∈ rationalPullback ↔ ∃ n : ℤ, ∃ q : ℚ[X], p = C (n : ℚ) + X * q := by
  constructor
  · rintro ⟨n, hn⟩
    have hd : X ∣ p - C (n : ℚ) := by
      apply X_dvd_iff.mpr
      rw [coeff_sub, coeff_C_zero, coeff_zero_eq_eval_zero]
      exact sub_eq_zero.mpr hn.symm
    obtain ⟨q, hq⟩ := hd
    exact ⟨n, q, by rw [← hq]; ring⟩
  · rintro ⟨n, q, rfl⟩
    exact ⟨n, by simp⟩

/-- The ordinary integer constants in the rational pullback. -/
def integerConstants : ℤ →+* rationalPullback :=
  CoefficientPullback.sectionMap (evalRingHom (0 : ℚ)) (Int.castRingHom ℚ) C (by simp)

@[simp] theorem integerConstants_val (n : ℤ) :
    (integerConstants n).val = C (n : ℚ) := rfl

/-- The polynomial whose constant term is nonzero but which the detector rejects. -/
def generator : rationalPullback := ⟨1 + X, ⟨1, by simp⟩⟩

@[simp] theorem generator_eval_zero : generator.val.eval 0 = 1 := by
  simp [generator]

/-- Evaluation at minus one, restricted to the coefficient pullback. -/
def evaluateMinusOne : rationalPullback →+* ℚ :=
  (evalRingHom (-1)).comp rationalPullback.subtype

@[simp] theorem evaluateMinusOne_generator : evaluateMinusOne generator = 0 := by
  simp [evaluateMinusOne, generator]

/-- The explicit preimage of `q` is the polynomial `-q X`. -/
theorem evaluateMinusOne_surjective : Function.Surjective evaluateMinusOne := by
  intro q
  refine ⟨⟨-C q * X, ⟨0, by simp⟩⟩, ?_⟩
  simp [evaluateMinusOne]

/-- Dividing by `1 + X` preserves integrality of the constant coefficient. -/
theorem evaluateMinusOne_ker : RingHom.ker evaluateMinusOne = Ideal.span {generator} := by
  ext p
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  constructor
  · intro hp
    have hd : X - C (-1 : ℚ) ∣ p.val := dvd_iff_isRoot.mpr hp
    obtain ⟨q, hq⟩ := hd
    have hq' : p.val = (1 + X) * q := by simpa [add_comm] using hq
    have hct : q.eval 0 = p.val.eval 0 := by
      rw [hq']
      simp
    have hmem : q ∈ rationalPullback := by
      change q.eval 0 ∈ (Int.castRingHom ℚ).range
      rw [hct]
      exact p.property
    exact ⟨⟨q, hmem⟩, Subtype.ext hq'⟩
  · rintro ⟨q, rfl⟩
    rw [map_mul, evaluateMinusOne_generator, zero_mul]

/-- The principal quotient is the rational field. -/
def rationalQuotientEquiv : rationalPullback ⧸ Ideal.span {generator} ≃+* ℚ :=
  (Ideal.quotEquivOfEq evaluateMinusOne_ker.symm).trans
    (evaluateMinusOne.quotientKerEquivOfSurjective evaluateMinusOne_surjective)

/-- Lambda has no rational root. -/
theorem rational_value_ne_zero (q : ℚ) : value q ≠ 0 := by
  intro h
  have hm := congrArg (algebraMap ℚ ℂ) h
  rw [map_value, map_zero] at hm
  exact rational_complex_value_ne_zero q 0 (by simpa using hm)

/-- The quotient by `1 + X` has no root of Lambda. -/
theorem rational_quotient_root_free (t : rationalPullback ⧸ Ideal.span {generator}) :
    value t ≠ 0 := by
  intro ht
  have hm := congrArg rationalQuotientEquiv.toRingHom ht
  rw [map_value, map_zero] at hm
  exact rational_value_ne_zero _ hm

/-- Any root-free image detects the obstruction at an element in the kernel. -/
theorem not_detects_of_root_free_image {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (hno : ∀ t : S, value t ≠ 0) (a : R) (ha : φ a = 0) :
    ¬ Detects a := by
  intro h
  obtain ⟨s, t, ht⟩ := h.map φ
  rw [ha, zero_mul] at ht
  exact hno t ht.symm

/-- The detector fails although the constant coefficient is one. -/
theorem rational_generator_not_detects : ¬ Detects generator :=
  not_detects_of_root_free_image evaluateMinusOne rational_value_ne_zero generator
    evaluateMinusOne_generator

/-- The integer polynomial counterexample, independently of its ambient field. -/
theorem integer_polynomial_not_detects : ¬ Detects (1 + X : ℤ[X]) :=
  not_detects_of_root_free_image (evalRingHom (-1)) integer_value_ne_zero (1 + X)
    (by simp)

/-- The second rejected polynomial also has constant coefficient one. -/
theorem integer_polynomial_eval_zero : (1 + X : ℤ[X]).eval 0 = 1 := by simp

/-- Polynomial constancy and membership in the pullback give an integer constant. -/
theorem mem_integerConstants_of_constant (p : rationalPullback)
    (hp : p.val = C (p.val.eval 0)) : p ∈ integerConstants.range := by
  obtain ⟨n, hn⟩ := p.property
  refine ⟨n, Subtype.ext ?_⟩
  change C (n : ℚ) = p.val
  change (n : ℚ) = p.val.eval 0 at hn
  rw [hn, ← hp]

/-- Xi still defines exactly the ordinary integers in the rational pullback. -/
theorem rational_xi_iff (p : rationalPullback) :
    DiophantineConstants.Xi p ↔ p ∈ integerConstants.range := by
  apply DiophantineConstants.xi_iff_mem_range integerConstants
  · intro u v h
    apply mem_integerConstants_of_constant v
    have he := congrArg rationalPullback.subtype h
    have he' : u.val ^ 2 - C (2 : ℚ) * v.val ^ 2 = C (1 : ℚ) := by
      change u.val ^ 2 - 2 * v.val ^ 2 = 1 at he
      simpa only [map_ofNat, map_one] using he
    exact (PolynomialConstantRigidity.pell_constant 2 1 (by norm_num) (by norm_num)
      u.val v.val he').2
  · intro t ht
    have hm := congrArg evaluateMinusOne ht
    rw [map_value, map_zero] at hm
    exact rational_value_ne_zero _ hm
  · intro x w a ha h
    apply mem_integerConstants_of_constant x
    apply PolynomialConstantRigidity.unit_eq_constant
    have hunit : IsUnit (integerConstants a).val := by
      rw [integerConstants_val]
      apply Polynomial.isUnit_C.mpr
      apply isUnit_iff_ne_zero.mpr
      intro hz
      apply ha
      have ha0 : a = 0 := by exact_mod_cast hz
      rw [ha0, map_zero]
    have he := congrArg rationalPullback.subtype h
    change x.val * w.val = (integerConstants a).val at he
    exact isUnit_of_mul_isUnit_left (he.symm ▸ hunit)
  · exact DiophantineConstants.integer_xi

/-- The usual inclusion of integer polynomials into real polynomials. -/
def integerRealPolynomials : ℤ[X] →+* ℝ[X] := mapRingHom (Int.castRingHom ℝ)

theorem integerRealPolynomials_injective : Function.Injective integerRealPolynomials :=
  Polynomial.map_injective (Int.castRingHom ℝ) Int.cast_injective

/-- Every integer polynomial has integer constant coefficient in the ambient ring. -/
theorem integerRealPolynomials_le_pullback :
    integerRealPolynomials.range ≤
      CoefficientPullback.subring (evalRingHom 0) (Int.castRingHom ℝ) := by
  rintro _ ⟨p, rfl⟩
  refine ⟨p.coeff 0, ?_⟩
  change (p.coeff 0 : ℝ) = (p.map (Int.castRingHom ℝ)).eval 0
  rw [← coeff_zero_eq_eval_zero, coeff_map]
  rfl

/-- The polynomial `X / 2` belongs to the full pullback, but is not an integer polynomial. -/
theorem half_X_not_integer_polynomial :
    C (1 / 2 : ℝ) * X ∉ integerRealPolynomials.range := by
  rintro ⟨p, hp⟩
  have hc := congrArg (fun q : ℝ[X] => q.coeff 1) hp
  change (p.map (Int.castRingHom ℝ)).coeff 1 = (C (1 / 2 : ℝ) * X).coeff 1 at hc
  simp only [coeff_map, coeff_C_mul_X, if_true, Int.coe_castRingHom] at hc
  by_cases hn : p.coeff 1 ≤ 0
  · have hn' : (p.coeff 1 : ℝ) ≤ 0 := by exact_mod_cast hn
    linarith
  · have hn' : (1 : ℝ) ≤ (p.coeff 1 : ℝ) := by exact_mod_cast (by omega : 1 ≤ p.coeff 1)
    linarith

/-- The integer polynomial ring is strictly smaller than the full coefficient pullback. -/
theorem integerRealPolynomials_lt_pullback :
    integerRealPolynomials.range <
      CoefficientPullback.subring (evalRingHom 0) (Int.castRingHom ℝ) := by
  refine lt_of_le_of_ne integerRealPolynomials_le_pullback ?_
  intro he
  apply half_X_not_integer_polynomial
  rw [he]
  exact ⟨0, by simp⟩

/-- The ambient real coefficient field does contain a root of Lambda. -/
theorem real_coefficient_root : value (Real.sqrt 13) = 0 := by
  simp [value, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 13)]

/-- The same root is a constant polynomial in the ambient real polynomial ring. -/
theorem real_polynomial_root : value (C (Real.sqrt 13)) = (0 : ℝ[X]) := by
  rw [← map_value, real_coefficient_root, map_zero]

end
end Surreal.DetectorCounterexamples

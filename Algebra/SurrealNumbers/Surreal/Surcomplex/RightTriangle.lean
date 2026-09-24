import Surreal.Surcomplex.TriangleLaws

/-!
# Right triangles and all positive surreal slopes

The cosine law characterizes right triangles by Pythagoras. The exact
angle sum and sine law identify each acute angle with the inverse tangent
of the opposite-to-adjacent leg ratio, without a finite-slope hypothesis.
Explicit triangles realize every positive pair of legs and hence every
positive surreal slope. This proves `trigonometry:cor:right`.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- The only zero of cosine on the actual closed upper angle interval is the right angle. -/
theorem finiteCos_eq_zero_iff_of_mem_Icc (θ : SignSequence.FiniteElement.{u})
    (hθ : θ.val ∈ Set.Icc 0 (SignSequence.ofReal Real.pi)) :
    finiteCos θ = 0 ↔ θ = SignSequence.finiteOfReal (Real.pi / 2) := by
  have hp : (0 : SignSequence.{u}) < SignSequence.ofReal Real.pi := by
    simpa only [map_zero] using SignSequence.ofReal_strictMono Real.pi_pos
  have hm : (SignSequence.finiteOfReal (Real.pi / 2)).val ∈
      Set.Icc (0 : SignSequence.{u}) (SignSequence.ofReal Real.pi) := by
    change 0 ≤ SignSequence.ofReal (Real.pi / 2) ∧
      SignSequence.ofReal (Real.pi / 2) ≤ SignSequence.ofReal Real.pi
    rw [map_div₀, map_ofNat]
    constructor <;> linarith
  have hc : finiteCos (SignSequence.finiteOfReal (Real.pi / 2) :
      SignSequence.FiniteElement.{u}) = 0 := by simp [Real.cos_pi_div_two]
  constructor
  · intro he
    exact finiteCos_strictAntiOn.injOn hθ hm (he.trans hc.symm)
  · rintro rfl
    exact hc

namespace Triangle

/-- A triangle is right at its third vertex exactly when its sides satisfy Pythagoras. -/
theorem right_angleC_iff_pythagoras (T : Triangle.{u}) :
    T.angleC = SignSequence.finiteOfReal (Real.pi / 2) ↔
      T.sideC ^ 2 = T.sideA ^ 2 + T.sideB ^ 2 := by
  have hc := T.rotate.rotate.angleA_mem
  have he := T.rotate.rotate.cosine_law
  simp only [sideA_rotate, sideB_rotate, sideC_rotate, angleA_rotate, angleB_rotate] at he
  rw [← finiteCos_eq_zero_iff_of_mem_Icc T.angleC ⟨hc.1.le, hc.2.le⟩]
  constructor
  · intro h
    simpa only [h, mul_zero, sub_zero] using he
  · intro h
    have hp : 2 * T.sideA * T.sideB ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) T.sideA_pos.ne') T.sideB_pos.ne'
    apply (mul_eq_zero.mp (show (2 * T.sideA * T.sideB) * finiteCos T.angleC = 0 by
      linarith only [he, h])).resolve_left hp

/-- The two remaining angles of a right triangle are strictly acute actual surreal angles. -/
theorem acute_angles_of_right (T : Triangle.{u})
    (h : T.angleC = SignSequence.finiteOfReal (Real.pi / 2)) :
    T.angleA.val ∈ Set.Ioo 0 (SignSequence.ofReal (Real.pi / 2)) ∧
      T.angleB.val ∈ Set.Ioo 0 (SignSequence.ofReal (Real.pi / 2)) := by
  have he := congrArg (fun θ : SignSequence.FiniteElement.{u} => θ.val) T.angle_sum
  rw [h] at he
  change T.angleA.val + T.angleB.val + SignSequence.ofReal (Real.pi / 2) =
    SignSequence.ofReal Real.pi at he
  have hA := T.angleA_mem.1
  have hB : 0 < T.angleB.val := T.rotate.angleA_mem.1
  simp only [Set.mem_Ioo, map_div₀, map_ofNat] at he ⊢
  constructor <;> constructor <;> linarith

private theorem right_complement (T : Triangle.{u})
    (h : T.angleC = SignSequence.finiteOfReal (Real.pi / 2)) :
    T.angleB = SignSequence.finiteOfReal (Real.pi / 2) - T.angleA := by
  apply ArchimedeanClass.FiniteElement.ext
  have he := congrArg (fun θ : SignSequence.FiniteElement.{u} => θ.val) T.angle_sum
  rw [h] at he
  change T.angleA.val + T.angleB.val + SignSequence.ofReal (Real.pi / 2) =
    SignSequence.ofReal Real.pi at he
  change T.angleB.val = SignSequence.ofReal (Real.pi / 2) - T.angleA.val
  rw [map_div₀, map_ofNat] at he ⊢
  linarith

/-- The tangent of an acute angle is the exact actual opposite-to-adjacent leg ratio. -/
theorem tan_angleA_of_right (T : Triangle.{u})
    (h : T.angleC = SignSequence.finiteOfReal (Real.pi / 2)) :
    finiteTan T.angleA = T.sideA / T.sideB := by
  have hb : finiteSin T.angleB = finiteCos T.angleA := by
    rw [T.right_complement h, finiteSin_sub]
    simp only [finiteSin_constant, finiteCos_constant, Real.sin_pi_div_two,
      Real.cos_pi_div_two, map_one, map_zero, one_mul, zero_mul, sub_zero]
  have hcos : 0 < finiteCos T.angleA := by
    rw [← hb]
    exact T.rotate.sin_angleA_pos
  have he := (div_eq_div_iff T.sin_angleA_pos.ne' T.rotate.sin_angleA_pos.ne').mp
    T.sine_law_cyclic.1
  rw [angleA_rotate, hb] at he
  apply (div_eq_div_iff hcos.ne' T.sideB_pos.ne').mpr
  simpa only [mul_comm] using he.symm

/-- The acute angle opposite the first leg is inverse tangent of its ratio to the other leg. -/
theorem angleA_eq_arctan_of_right (T : Triangle.{u})
    (h : T.angleC = SignSequence.finiteOfReal (Real.pi / 2)) :
    T.angleA = arctan (T.sideA / T.sideB) := by
  have ha := (T.acute_angles_of_right h).1
  have hp : (0 : SignSequence.{u}) < SignSequence.ofReal (Real.pi / 2) := by
    simpa only [map_zero] using SignSequence.ofReal_strictMono (half_pos Real.pi_pos)
  have hi : T.angleA.val ∈ Set.Ioo (SignSequence.ofReal (-(Real.pi / 2)))
      (SignSequence.ofReal (Real.pi / 2)) := by
    rw [map_neg]
    exact ⟨by linarith [ha.1], ha.2⟩
  have he := arctan_finiteTan T.angleA hi
  rw [T.tan_angleA_of_right h] at he
  exact he.symm

/-- The other acute angle has the reciprocal positive leg ratio. -/
theorem angleB_eq_arctan_of_right (T : Triangle.{u})
    (h : T.angleC = SignSequence.finiteOfReal (Real.pi / 2)) :
    T.angleB = arctan (T.sideB / T.sideA) := by
  rw [T.right_complement h, T.angleA_eq_arctan_of_right h,
    ← arctan_inv_of_pos (T.sideA / T.sideB) (div_pos T.sideA_pos T.sideB_pos), inv_div]

/-- The triangle with vertices `p`, `i*q`, and `0` realizes arbitrary positive actual legs. -/
def fromPositiveLegs (p q : SignSequence.{u}) (hp : 0 < p) (hq : 0 < q) : Triangle.{u} where
  A := ofReal p
  B := ofReal q * I
  C := 0
  noncollinear := by
    have he : Complexify.cross (ofReal q * I - ofReal p) (0 - ofReal p) = p * q := by
      simp only [Complexify.cross_def, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub,
        mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im,
        QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero]
      ring
    rw [he]
    exact (mul_pos hp hq).ne'

@[simp] theorem sideA_fromPositiveLegs (p q : SignSequence.{u}) (hp : 0 < p) (hq : 0 < q) :
    (fromPositiveLegs p q hp hq).sideA = q := by
  change modulus (ofReal q * I - 0) = q
  rw [sub_zero, modulus_mul, modulus_ofReal, modulus_I, mul_one, abs_of_pos hq]

@[simp] theorem sideB_fromPositiveLegs (p q : SignSequence.{u}) (hp : 0 < p) (hq : 0 < q) :
    (fromPositiveLegs p q hp hq).sideB = p := by
  change modulus (0 - ofReal p) = p
  rw [zero_sub, modulus_neg, modulus_ofReal, abs_of_pos hp]

/-- The constructed triangle satisfies Pythagoras at the zero vertex. -/
theorem sideC_sq_fromPositiveLegs (p q : SignSequence.{u}) (hp : 0 < p) (hq : 0 < q) :
    (fromPositiveLegs p q hp hq).sideC ^ 2 = p ^ 2 + q ^ 2 := by
  change modulus (ofReal p - ofReal q * I) ^ 2 = _
  rw [modulus_sq, normSq_eq]
  simp only [QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, mul_re, mul_im,
    ofReal_re, ofReal_im, I_re, I_im]
  ring

/-- The constructed positive-leg triangle is right at its third vertex. -/
theorem right_fromPositiveLegs (p q : SignSequence.{u}) (hp : 0 < p) (hq : 0 < q) :
    (fromPositiveLegs p q hp hq).angleC = SignSequence.finiteOfReal (Real.pi / 2) := by
  apply (right_angleC_iff_pythagoras _).mpr
  rw [sideA_fromPositiveLegs, sideB_fromPositiveLegs, sideC_sq_fromPositiveLegs]
  ring

/-- The acute angle opposite `q` is exactly `arctan(q/p)` even for infinite ratios. -/
theorem angleA_fromPositiveLegs (p q : SignSequence.{u}) (hp : 0 < p) (hq : 0 < q) :
    (fromPositiveLegs p q hp hq).angleA = arctan (q / p) := by
  simpa only [sideA_fromPositiveLegs, sideB_fromPositiveLegs] using
    (fromPositiveLegs p q hp hq).angleA_eq_arctan_of_right (right_fromPositiveLegs p q hp hq)

/-- Every positive actual surreal is realized as a right triangle's leg ratio and acute tangent. -/
theorem exists_right_triangle_of_slope (t : SignSequence.{u}) (ht : 0 < t) :
    ∃ T : Triangle.{u}, T.angleC = SignSequence.finiteOfReal (Real.pi / 2) ∧
      T.sideA / T.sideB = t ∧ T.angleA = arctan t := by
  refine ⟨fromPositiveLegs 1 t (by norm_num) ht,
    right_fromPositiveLegs 1 t (by norm_num) ht, ?_, ?_⟩
  · simp only [sideA_fromPositiveLegs, sideB_fromPositiveLegs, div_one]
  · simpa only [div_one] using angleA_fromPositiveLegs 1 t (by norm_num) ht

end Triangle
end
end Surreal.Surcomplex

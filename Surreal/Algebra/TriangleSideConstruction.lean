import Surreal.Algebra.Geometry

/-!
# Reconstructing a triangle from its three side lengths

Heron's factorization makes the canonical height strictly positive when
three positive lengths satisfy the strict triangle inequalities. The
resulting point above the real axis has the two prescribed distances.
Any two points with those distances are equal or conjugate. These are the
ordered-field construction and uniqueness prerequisites for
`trigonometry:thm:sss` and `trigonometry:eq:heronfactor`.
-/

namespace Surreal.Complexify

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- The real coordinate in the canonical side-side-side construction. -/
def sssAbscissa (a b c : F) : F := (b ^ 2 + c ^ 2 - a ^ 2) / (2 * c)

/-- The square of the height in the canonical side-side-side construction. -/
def sssHeightSq (a b c : F) : F := b ^ 2 - sssAbscissa a b c ^ 2

/-- The manuscript's Heron factorization after substituting the canonical abscissa. -/
theorem sssHeightSq_factorization (a b c : F) (hc : c ≠ 0) :
    4 * c ^ 2 * sssHeightSq a b c =
      (a + b + c) * (-a + b + c) * (a - b + c) * (a + b - c) := by
  calc
    _ = 4 * b ^ 2 * c ^ 2 - (b ^ 2 + c ^ 2 - a ^ 2) ^ 2 := by
      dsimp only [sssHeightSq, sssAbscissa]
      field_simp [hc]
      ring
    _ = _ := (heron_factorization a b c).symm

/-- Positive side lengths satisfying the three strict inequalities give a positive squared height. -/
theorem sssHeightSq_pos (a b c : F) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a < b + c) (hbac : b < c + a) (hcab : c < a + b) :
    0 < sssHeightSq a b c := by
  have hp : 0 < (a + b + c) * (-a + b + c) * (a - b + c) * (a + b - c) :=
    mul_pos (mul_pos (mul_pos (by linarith only [ha, hb, hc])
      (by linarith only [habc])) (by linarith only [hbac])) (by linarith only [hcab])
  rw [← sssHeightSq_factorization a b c hc.ne'] at hp
  exact (mul_pos_iff_of_pos_left (mul_pos (by norm_num) (sq_pos_of_ne_zero hc.ne'))).mp hp

variable [HasNonnegSquareRoots F]

/-- The canonical height exists and is positive over any ordered field with nonnegative roots. -/
theorem exists_sssHeight (a b c : F) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a < b + c) (hbac : b < c + a) (hcab : c < a + b) :
    ∃ y : F, 0 < y ∧ y ^ 2 = sssHeightSq a b c := by
  have hp := sssHeightSq_pos a b c ha hb hc habc hbac hcab
  obtain ⟨y, hy, he⟩ := exists_nonneg_sq hp.le
  refine ⟨y, ?_, he⟩
  nlinarith only [hy, he, hp]

/-- Two prescribed distances force the real coordinate, without a choice of orientation. -/
theorem normalized_point_re (a b c : F) (hc : c ≠ 0) (p : Complexify F)
    (hb : modulus p = b) (ha : modulus (p - algebraMap F (Complexify F) c) = a) :
    p.re = sssAbscissa a b c := by
  have hb' := congrArg (fun r : F => r ^ 2) hb
  have ha' := congrArg (fun r : F => r ^ 2) ha
  rw [modulus_sq] at hb' ha'
  simp only [normSq, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub,
    QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, sub_zero] at hb' ha'
  rw [sssAbscissa]
  apply (eq_div_iff (mul_ne_zero (by norm_num) hc)).mpr
  nlinarith only [hb', ha']

/-- The same distances force the square of the imaginary coordinate. -/
theorem normalized_point_im_sq (a b c : F) (hc : c ≠ 0) (p : Complexify F)
    (hb : modulus p = b) (ha : modulus (p - algebraMap F (Complexify F) c) = a) :
    p.im ^ 2 = sssHeightSq a b c := by
  have hn := congrArg (fun r : F => r ^ 2) hb
  rw [modulus_sq, normSq, normalized_point_re a b c hc p hb ha] at hn
  dsimp only [sssHeightSq]
  linarith only [hn]

/-- The canonical upper point realizes all prescribed sides and has nonzero oriented area. -/
theorem exists_normalized_triangle_point (a b c : F) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a < b + c) (hbac : b < c + a) (hcab : c < a + b) :
    ∃ p : Complexify F, p.re = sssAbscissa a b c ∧ 0 < p.im ∧
      modulus p = b ∧ modulus (p - algebraMap F (Complexify F) c) = a ∧
      cross (algebraMap F (Complexify F) c) p ≠ 0 := by
  obtain ⟨y, hy, he⟩ := exists_sssHeight a b c ha hb hc habc hbac hcab
  let p : Complexify F := ⟨sssAbscissa a b c, y⟩
  have hm : modulus p = b := by
    apply modulus_eq_of_nonneg_sq hb.le
    change b ^ 2 = sssAbscissa a b c ^ 2 + y ^ 2
    rw [he, sssHeightSq]
    ring
  have hd : modulus (p - algebraMap F (Complexify F) c) = a := by
    apply modulus_eq_of_nonneg_sq ha.le
    change a ^ 2 = (sssAbscissa a b c - c) ^ 2 + (y - 0) ^ 2
    rw [sub_zero, he, sssHeightSq, sssAbscissa]
    field_simp [hc.ne']
    ring
  refine ⟨p, rfl, hy, hm, hd, ?_⟩
  simpa only [cross_def, QuadraticAlgebra.algebraMap_re,
    QuadraticAlgebra.algebraMap_im, zero_mul, sub_zero] using (mul_pos hc hy).ne'

/-- Equal distances from two distinct real-axis base points determine a point up to conjugation. -/
theorem normalized_point_eq_or_eq_conj (c : F) (hc : c ≠ 0) (p q : Complexify F)
    (hzero : modulus p = modulus q)
    (hbase : modulus (p - algebraMap F (Complexify F) c) =
      modulus (q - algebraMap F (Complexify F) c)) : p = q ∨ p = star q := by
  have hp := normalized_point_re (modulus (q - algebraMap F (Complexify F) c))
    (modulus q) c hc p hzero hbase
  have hq := normalized_point_re (modulus (q - algebraMap F (Complexify F) c))
    (modulus q) c hc q rfl rfl
  have hre : p.re = q.re := hp.trans hq.symm
  have hn := congrArg (fun r : F => r ^ 2) hzero
  rw [modulus_sq, modulus_sq, normSq, normSq, hre] at hn
  have him : p.im ^ 2 = q.im ^ 2 := by linarith only [hn]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp him with him | him
  · exact Or.inl (QuadraticAlgebra.ext hre him)
  · right
    apply QuadraticAlgebra.ext
    · simpa only [conj_re] using hre
    · simpa only [conj_im] using him

/-- Fixing positive orientation removes the conjugate alternative. -/
theorem normalized_point_eq_of_im_pos (c : F) (hc : c ≠ 0) (p q : Complexify F)
    (hp : 0 < p.im) (hq : 0 < q.im) (hzero : modulus p = modulus q)
    (hbase : modulus (p - algebraMap F (Complexify F) c) =
      modulus (q - algebraMap F (Complexify F) c)) : p = q := by
  rcases normalized_point_eq_or_eq_conj c hc p q hzero hbase with h | h
  · exact h
  · have he := congrArg QuadraticAlgebra.im h
    rw [conj_im] at he
    linarith only [hp, hq, he]

/-- Positive side data satisfying the strict triangle inequalities has a unique upper realization. -/
theorem existsUnique_normalized_triangle_point (a b c : F)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a < b + c) (hbac : b < c + a) (hcab : c < a + b) :
    ∃! p : Complexify F, 0 < p.im ∧ modulus p = b ∧
      modulus (p - algebraMap F (Complexify F) c) = a := by
  obtain ⟨p, _, hp, hpb, hpa, _⟩ :=
    exists_normalized_triangle_point a b c ha hb hc habc hbac hcab
  refine ⟨p, ⟨hp, hpb, hpa⟩, ?_⟩
  rintro q ⟨hq, hqb, hqa⟩
  exact normalized_point_eq_of_im_pos c hc.ne' q p hq hp
    (hqb.trans hpb.symm) (hqa.trans hpa.symm)

end Surreal.Complexify

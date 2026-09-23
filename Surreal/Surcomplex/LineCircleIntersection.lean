import Surreal.Surcomplex.Modulus

/-!
# Actual line and unit-circle intersections

The algebraic part of `trigonometry:thm:amplitude` and the explicit points
in `trigonometry:eq:intersectionpoints` hold at arbitrary surreal scales.
Gram's identity gives the discriminant, the complete classification, and
the absolute angular-derivative and Jacobian expressions. No finiteness
condition is imposed on the coefficients of the line.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- The discriminant of a line intersecting the actual unit circle. -/
def lineCircleDiscriminant (A B D : SignSequence.{u}) : SignSequence.{u} :=
  A ^ 2 + B ^ 2 - D ^ 2

/-- Reconstruction from the line value `D` and the oriented cross value `W`. -/
def lineCirclePoint (A B D W : SignSequence.{u}) : Surcomplex.{u} :=
  ⟨(D * A - W * B) / (A ^ 2 + B ^ 2),
    (D * B + W * A) / (A ^ 2 + B ^ 2)⟩

/-- The positive-cross intersection in `trigonometry:eq:intersectionpoints`. -/
def lineCirclePlus (A B D : SignSequence.{u}) : Surcomplex.{u} :=
  lineCirclePoint A B D (SignSequence.sqrt (lineCircleDiscriminant A B D))

/-- The negative-cross intersection in `trigonometry:eq:intersectionpoints`. -/
def lineCircleMinus (A B D : SignSequence.{u}) : Surcomplex.{u} :=
  lineCirclePoint A B D (-SignSequence.sqrt (lineCircleDiscriminant A B D))

/-- Membership in the actual unit circle and in the specified affine line. -/
def IsLineCircleIntersection (A B D : SignSequence.{u}) (z : Surcomplex.{u}) : Prop :=
  modulus z = 1 ∧ A * z.re + B * z.im = D

/-- The point formula is literally the sum of normal and perpendicular components. -/
theorem lineCirclePoint_eq_smul (A B D W : SignSequence.{u}) :
    lineCirclePoint A B D W =
      (D / (A ^ 2 + B ^ 2)) • (⟨A, B⟩ : Surcomplex.{u}) +
        (W / (A ^ 2 + B ^ 2)) • (⟨-B, A⟩ : Surcomplex.{u}) := by
  apply QuadraticAlgebra.ext <;> simp only [lineCirclePoint, QuadraticAlgebra.re_add,
    QuadraticAlgebra.im_add, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul,
    smul_eq_mul] <;> ring

theorem lineCirclePoint_line (A B D W : SignSequence.{u})
    (h : 0 < A ^ 2 + B ^ 2) :
    A * (lineCirclePoint A B D W).re + B * (lineCirclePoint A B D W).im = D := by
  dsimp only [lineCirclePoint]
  field_simp [ne_of_gt h]
  ring

theorem lineCirclePoint_cross (A B D W : SignSequence.{u})
    (h : 0 < A ^ 2 + B ^ 2) :
    A * (lineCirclePoint A B D W).im - B * (lineCirclePoint A B D W).re = W := by
  dsimp only [lineCirclePoint]
  field_simp [ne_of_gt h]
  ring

/-- Normal and perpendicular coordinates determine an actual point uniquely. -/
theorem eq_lineCirclePoint (A B D W : SignSequence.{u}) (z : Surcomplex.{u})
    (h : 0 < A ^ 2 + B ^ 2) (hline : A * z.re + B * z.im = D)
    (hcross : A * z.im - B * z.re = W) : z = lineCirclePoint A B D W := by
  apply QuadraticAlgebra.ext
  · change z.re = (D * A - W * B) / (A ^ 2 + B ^ 2)
    apply (eq_div_iff (ne_of_gt h)).mpr
    linear_combination A * hline - B * hcross
  · change z.im = (D * B + W * A) / (A ^ 2 + B ^ 2)
    apply (eq_div_iff (ne_of_gt h)).mpr
    linear_combination B * hline + A * hcross

theorem normSq_lineCirclePoint (A B D W : SignSequence.{u})
    (h : 0 < A ^ 2 + B ^ 2) :
    normSq (lineCirclePoint A B D W) = (D ^ 2 + W ^ 2) / (A ^ 2 + B ^ 2) := by
  have hg := Complexify.dot_sq_add_cross_sq (⟨A, B⟩ : Surcomplex.{u})
    (lineCirclePoint A B D W)
  simp only [Complexify.dot_def, Complexify.cross_def] at hg
  rw [lineCirclePoint_line A B D W h, lineCirclePoint_cross A B D W h] at hg
  apply (eq_div_iff (ne_of_gt h)).mpr
  simpa only [Complexify.normSq, normSq, mul_comm] using hg.symm

theorem isLineCircleIntersection_lineCirclePoint (A B D W : SignSequence.{u})
    (h : 0 < A ^ 2 + B ^ 2) (hW : W ^ 2 = lineCircleDiscriminant A B D) :
    IsLineCircleIntersection A B D (lineCirclePoint A B D W) := by
  refine ⟨modulus_eq_of_nonneg_sq zero_le_one ?_, lineCirclePoint_line A B D W h⟩
  rw [normSq_lineCirclePoint A B D W h, hW]
  dsimp only [lineCircleDiscriminant]
  rw [show D ^ 2 + (A ^ 2 + B ^ 2 - D ^ 2) = A ^ 2 + B ^ 2 by ring,
    div_self (ne_of_gt h), one_pow]

/-- Both explicit signs are actual solutions whenever the discriminant is nonnegative. -/
theorem isLineCircleIntersection_plus (A B D : SignSequence.{u})
    (h : 0 < A ^ 2 + B ^ 2) (hΔ : 0 ≤ lineCircleDiscriminant A B D) :
    IsLineCircleIntersection A B D (lineCirclePlus A B D) :=
  isLineCircleIntersection_lineCirclePoint A B D _ h (SignSequence.sqrt_sq hΔ)

theorem isLineCircleIntersection_minus (A B D : SignSequence.{u})
    (h : 0 < A ^ 2 + B ^ 2) (hΔ : 0 ≤ lineCircleDiscriminant A B D) :
    IsLineCircleIntersection A B D (lineCircleMinus A B D) :=
  isLineCircleIntersection_lineCirclePoint A B D _ h
    (by rw [neg_sq, SignSequence.sqrt_sq hΔ])

/-- Gram's identity identifies the square of the transverse coordinate at every solution. -/
theorem cross_sq_eq_lineCircleDiscriminant {A B D : SignSequence.{u}}
    {z : Surcomplex.{u}} (hz : IsLineCircleIntersection A B D z) :
    (A * z.im - B * z.re) ^ 2 = lineCircleDiscriminant A B D := by
  have hg := Complexify.dot_sq_add_cross_sq (⟨A, B⟩ : Surcomplex.{u}) z
  simp only [Complexify.dot_def, Complexify.cross_def] at hg
  rw [hz.2] at hg
  change D ^ 2 + (A * z.im - B * z.re) ^ 2 = (A ^ 2 + B ^ 2) * normSq z at hg
  rw [← modulus_sq z, hz.1, one_pow, mul_one] at hg
  dsimp only [lineCircleDiscriminant]
  linarith

theorem lineCircleDiscriminant_nonneg {A B D : SignSequence.{u}}
    {z : Surcomplex.{u}} (hz : IsLineCircleIntersection A B D z) :
    0 ≤ lineCircleDiscriminant A B D := by
  rw [← cross_sq_eq_lineCircleDiscriminant hz]
  exact sq_nonneg _

/-- Every intersection is one of the two explicit points; tangent signs may coincide. -/
theorem isLineCircleIntersection_iff (A B D : SignSequence.{u}) (z : Surcomplex.{u})
    (h : 0 < A ^ 2 + B ^ 2) (hΔ : 0 ≤ lineCircleDiscriminant A B D) :
    IsLineCircleIntersection A B D z ↔ z = lineCirclePlus A B D ∨
      z = lineCircleMinus A B D := by
  constructor
  · intro hz
    have hs : (A * z.im - B * z.re) ^ 2 =
        SignSequence.sqrt (lineCircleDiscriminant A B D) ^ 2 :=
      (cross_sq_eq_lineCircleDiscriminant hz).trans (SignSequence.sqrt_sq hΔ).symm
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hs with hp | hm
    · exact Or.inl (eq_lineCirclePoint A B D _ z h hz.2 hp)
    · exact Or.inr (eq_lineCirclePoint A B D _ z h hz.2 hm)
  · rintro (rfl | rfl)
    · exact isLineCircleIntersection_plus A B D h hΔ
    · exact isLineCircleIntersection_minus A B D h hΔ

/-- The discriminant gives the complete existence criterion at every surreal scale. -/
theorem exists_lineCircleIntersection_iff (A B D : SignSequence.{u})
    (h : 0 < A ^ 2 + B ^ 2) :
    (∃ z : Surcomplex.{u}, IsLineCircleIntersection A B D z) ↔
      0 ≤ lineCircleDiscriminant A B D := by
  constructor
  · rintro ⟨z, hz⟩
    exact lineCircleDiscriminant_nonneg hz
  · intro hΔ
    exact ⟨lineCirclePlus A B D, isLineCircleIntersection_plus A B D h hΔ⟩

theorem not_isLineCircleIntersection_of_discriminant_neg {A B D : SignSequence.{u}}
    (hΔ : lineCircleDiscriminant A B D < 0) (z : Surcomplex.{u}) :
    ¬IsLineCircleIntersection A B D z :=
  fun hz => hΔ.not_ge (lineCircleDiscriminant_nonneg hz)

/-- The two signs coincide exactly at tangency. -/
theorem lineCirclePlus_eq_minus_iff (A B D : SignSequence.{u})
    (h : 0 < A ^ 2 + B ^ 2) (hΔ : 0 ≤ lineCircleDiscriminant A B D) :
    lineCirclePlus A B D = lineCircleMinus A B D ↔ lineCircleDiscriminant A B D = 0 := by
  constructor
  · intro he
    have hc := congrArg (fun z : Surcomplex.{u} => A * z.im - B * z.re) he
    change A * (lineCirclePoint A B D _).im - B * (lineCirclePoint A B D _).re =
      A * (lineCirclePoint A B D _).im - B * (lineCirclePoint A B D _).re at hc
    rw [lineCirclePoint_cross A B D _ h, lineCirclePoint_cross A B D _ h] at hc
    have hs := SignSequence.sqrt_sq hΔ
    have hz : SignSequence.sqrt (lineCircleDiscriminant A B D) = 0 := by linarith
    simpa only [hz, zero_pow (by decide : 2 ≠ 0)] using hs.symm
  · intro he
    simp only [lineCirclePlus, lineCircleMinus, he, SignSequence.sqrt_zero, neg_zero]

theorem lineCirclePlus_ne_minus (A B D : SignSequence.{u})
    (h : 0 < A ^ 2 + B ^ 2) (hΔ : 0 < lineCircleDiscriminant A B D) :
    lineCirclePlus A B D ≠ lineCircleMinus A B D :=
  fun he => hΔ.ne' ((lineCirclePlus_eq_minus_iff A B D h hΔ.le).mp he)

/-- Exactly one actual intersection exists precisely at tangency. -/
theorem existsUnique_lineCircleIntersection_iff (A B D : SignSequence.{u})
    (h : 0 < A ^ 2 + B ^ 2) :
    (∃! z : Surcomplex.{u}, IsLineCircleIntersection A B D z) ↔
      lineCircleDiscriminant A B D = 0 := by
  constructor
  · rintro ⟨z, hz, hu⟩
    have hΔ := lineCircleDiscriminant_nonneg hz
    apply (lineCirclePlus_eq_minus_iff A B D h hΔ).mp
    exact (hu _ (isLineCircleIntersection_plus A B D h hΔ)).trans
      (hu _ (isLineCircleIntersection_minus A B D h hΔ)).symm
  · intro hΔ
    have hnonneg : 0 ≤ lineCircleDiscriminant A B D := hΔ.ge
    refine ⟨lineCirclePlus A B D, isLineCircleIntersection_plus A B D h hnonneg, ?_⟩
    intro z hz
    rcases (isLineCircleIntersection_iff A B D z h hnonneg).mp hz with hp | hm
    · exact hp
    · exact hm.trans ((lineCirclePlus_eq_minus_iff A B D h hnonneg).mpr hΔ).symm

/-- The absolute angular-derivative expression at any actual intersection. -/
theorem abs_lineCircle_angularDerivative {A B D : SignSequence.{u}} {z : Surcomplex.{u}}
    (hz : IsLineCircleIntersection A B D z) :
    |B * z.re - A * z.im| = SignSequence.sqrt (lineCircleDiscriminant A B D) := by
  apply (SignSequence.sqrt_eq_of_nonneg_sq (abs_nonneg _) ?_).symm
  rw [sq_abs, show B * z.re - A * z.im = -(A * z.im - B * z.re) by ring, neg_sq]
  exact cross_sq_eq_lineCircleDiscriminant hz

/-- The determinant of the circle and line gradients has absolute value twice the square root. -/
theorem abs_lineCircle_jacobian {A B D : SignSequence.{u}} {z : Surcomplex.{u}}
    (hz : IsLineCircleIntersection A B D z) :
    |2 * z.re * B - 2 * z.im * A| =
      2 * SignSequence.sqrt (lineCircleDiscriminant A B D) := by
  rw [show 2 * z.re * B - 2 * z.im * A = 2 * (B * z.re - A * z.im) by ring,
    abs_mul, abs_of_pos (by norm_num : (0 : SignSequence.{u}) < 2),
    abs_lineCircle_angularDerivative hz]

/-- At tangency the first angular derivative vanishes. -/
theorem lineCircle_angularDerivative_eq_zero {A B D : SignSequence.{u}} {z : Surcomplex.{u}}
    (hz : IsLineCircleIntersection A B D z) (hΔ : lineCircleDiscriminant A B D = 0) :
    B * z.re - A * z.im = 0 := by
  apply abs_eq_zero.mp
  rw [abs_lineCircle_angularDerivative hz, hΔ, SignSequence.sqrt_zero]

/-- A tangent solution has nonzero second angular derivative, so its contact is quadratic. -/
theorem lineCircle_secondDerivative_ne_zero {A B D : SignSequence.{u}} {z : Surcomplex.{u}}
    (h : 0 < A ^ 2 + B ^ 2) (hz : IsLineCircleIntersection A B D z)
    (hΔ : lineCircleDiscriminant A B D = 0) :
    -A * z.re - B * z.im = -D ∧ -D ≠ 0 := by
  constructor
  · linarith [hz.2]
  · intro he
    have hD : D = 0 := neg_eq_zero.mp he
    simp only [lineCircleDiscriminant, hD, zero_pow (by decide : 2 ≠ 0), sub_zero] at hΔ
    exact h.ne' hΔ

end

end Surreal.Surcomplex

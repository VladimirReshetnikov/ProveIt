import Surreal.Surcomplex.TriangleLaws

/-!
# Quadrance and spread for actual surcomplex triangles

Squared side lengths and squared angle sines satisfy the spread law,
cross law, and triple-spread relation of `trigonometry:eq:spreadlaws`
and `trigonometry:eq:triplespread`. Their coordinate expressions use
only field operations on actual surreal coordinates. Squaring forgets
both reversal and supplementation of the angle, as the source notes.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- Squared sine forgets reversal of an actual finite angle. -/
theorem finiteSin_sq_neg (θ : SignSequence.FiniteElement.{u}) :
    finiteSin (-θ) ^ 2 = finiteSin θ ^ 2 := by
  rw [finiteSin_neg, neg_sq]

/-- Squared sine forgets supplementation of an actual finite angle. -/
theorem finiteSin_sq_pi_sub (θ : SignSequence.FiniteElement.{u}) :
    finiteSin (SignSequence.finiteOfReal Real.pi - θ) ^ 2 = finiteSin θ ^ 2 := by
  rw [finiteSin_sub]
  simp

/-- Spread is a rational expression in the determinant and the two squared vector lengths. -/
theorem interiorAngle_spread_eq_cross_sq_div (z w : Surcomplex.{u})
    (h : Complexify.cross z w ≠ 0) :
    finiteSin (interiorAngle z w h) ^ 2 =
      Complexify.cross z w ^ 2 / (normSq z * normSq w) := by
  rw [finiteSin_interiorAngle, div_pow, sq_abs, mul_pow, modulus_sq, modulus_sq]

/-- The triple-spread identity holds for any three actual finite angles summing to pi. -/
theorem finiteSin_triple_spread (α β γ : SignSequence.FiniteElement.{u})
    (hsum : α + β + γ = SignSequence.finiteOfReal Real.pi) :
    (finiteSin α ^ 2 + finiteSin β ^ 2 + finiteSin γ ^ 2) ^ 2 =
      2 * ((finiteSin α ^ 2) ^ 2 + (finiteSin β ^ 2) ^ 2 + (finiteSin γ ^ 2) ^ 2) +
        4 * finiteSin α ^ 2 * finiteSin β ^ 2 * finiteSin γ ^ 2 := by
  have hg : γ = SignSequence.finiteOfReal Real.pi - (α + β) := by
    apply eq_sub_iff_add_eq.mpr
    rw [← hsum]
    abel
  have hs : finiteSin γ = finiteSin (α + β) := by
    rw [hg, finiteSin_sub]
    simp
  have he : finiteSin γ ^ 2 - finiteSin α ^ 2 - finiteSin β ^ 2 +
      2 * finiteSin α ^ 2 * finiteSin β ^ 2 =
        2 * finiteSin α * finiteSin β * finiteCos α * finiteCos β := by
    rw [hs, finiteSin_add]
    linear_combination finiteSin α ^ 2 * finiteCos_sq_add_finiteSin_sq β +
      finiteSin β ^ 2 * finiteCos_sq_add_finiteSin_sq α
  have hca : finiteCos α ^ 2 = 1 - finiteSin α ^ 2 := by
    linarith only [finiteCos_sq_add_finiteSin_sq α]
  have hcb : finiteCos β ^ 2 = 1 - finiteSin β ^ 2 := by
    linarith only [finiteCos_sq_add_finiteSin_sq β]
  have he2 := congrArg (fun x : SignSequence.{u} => x ^ 2) he
  simp only [mul_pow, hca, hcb] at he2
  linear_combination -he2

namespace Triangle

/-- The quadrance of the side opposite `A` is its squared actual surreal length. -/
def quadranceA (T : Triangle.{u}) : SignSequence.{u} := T.sideA ^ 2

def quadranceB (T : Triangle.{u}) : SignSequence.{u} := T.rotate.quadranceA

def quadranceC (T : Triangle.{u}) : SignSequence.{u} := T.rotate.rotate.quadranceA

/-- The spread at `A` is the square of the actual interior-angle sine. -/
def spreadA (T : Triangle.{u}) : SignSequence.{u} := finiteSin T.angleA ^ 2

def spreadB (T : Triangle.{u}) : SignSequence.{u} := T.rotate.spreadA

def spreadC (T : Triangle.{u}) : SignSequence.{u} := T.rotate.rotate.spreadA

@[simp] theorem quadranceA_rotate (T : Triangle.{u}) : T.rotate.quadranceA = T.quadranceB := rfl

@[simp] theorem quadranceB_rotate (T : Triangle.{u}) : T.rotate.quadranceB = T.quadranceC := rfl

@[simp] theorem quadranceC_rotate (T : Triangle.{u}) : T.rotate.quadranceC = T.quadranceA := by
  change T.rotate.rotate.rotate.quadranceA = T.quadranceA
  rw [rotate_rotate_rotate]

@[simp] theorem spreadA_rotate (T : Triangle.{u}) : T.rotate.spreadA = T.spreadB := rfl

@[simp] theorem spreadB_rotate (T : Triangle.{u}) : T.rotate.spreadB = T.spreadC := rfl

@[simp] theorem spreadC_rotate (T : Triangle.{u}) : T.rotate.spreadC = T.spreadA := by
  change T.rotate.rotate.rotate.spreadA = T.spreadA
  rw [rotate_rotate_rotate]

theorem quadranceA_pos (T : Triangle.{u}) : 0 < T.quadranceA := pow_pos T.sideA_pos 2

theorem quadranceB_pos (T : Triangle.{u}) : 0 < T.quadranceB := T.rotate.quadranceA_pos

theorem quadranceC_pos (T : Triangle.{u}) : 0 < T.quadranceC := T.rotate.rotate.quadranceA_pos

theorem spreadA_mem (T : Triangle.{u}) : T.spreadA ∈ Set.Ioc 0 1 := by
  refine ⟨pow_pos T.sin_angleA_pos 2, ?_⟩
  change finiteSin T.angleA ^ 2 ≤ 1
  nlinarith only [finiteCos_sq_add_finiteSin_sq T.angleA, sq_nonneg (finiteCos T.angleA)]

/-- Side quadrance is computed directly from its actual coordinate differences. -/
theorem quadranceA_eq_normSq (T : Triangle.{u}) : T.quadranceA = normSq (T.B - T.C) :=
  modulus_sq (T.B - T.C)

/-- Angle spread is computed rationally from actual coordinates, without evaluating a sine. -/
theorem spreadA_eq_cross_sq_div (T : Triangle.{u}) :
    T.spreadA = Complexify.cross (T.B - T.A) (T.C - T.A) ^ 2 /
      (normSq (T.B - T.A) * normSq (T.C - T.A)) :=
  interiorAngle_spread_eq_cross_sq_div _ _ T.noncollinear

/-- The common spread-to-quadrance ratio is four area squares divided by the quadrance product. -/
theorem spread_div_quadrance (T : Triangle.{u}) :
    T.spreadA / T.quadranceA =
      4 * T.area ^ 2 / (T.quadranceA * T.quadranceB * T.quadranceC) := by
  change finiteSin T.angleA ^ 2 / T.sideA ^ 2 =
    4 * T.area ^ 2 / (T.sideA ^ 2 * T.sideB ^ 2 * T.sideC ^ 2)
  rw [T.sin_angleA]
  field_simp [T.sideA_pos.ne', T.sideB_pos.ne', T.sideC_pos.ne']
  ring

/-- The cyclic spread law in `trigonometry:eq:spreadlaws`. -/
theorem spread_law (T : Triangle.{u}) :
    T.spreadA / T.quadranceA = T.spreadB / T.quadranceB ∧
      T.spreadB / T.quadranceB = T.spreadC / T.quadranceC := by
  have hB := T.rotate.spread_div_quadrance
  have hC := T.rotate.rotate.spread_div_quadrance
  simp only [spreadA_rotate, spreadB_rotate, quadranceA_rotate, quadranceB_rotate,
    quadranceC_rotate, area_rotate] at hB hC
  rw [T.spread_div_quadrance, hB, hC]
  constructor <;> ring

/-- The cross law in `trigonometry:eq:spreadlaws`; rotation gives its two cyclic forms. -/
theorem cross_law (T : Triangle.{u}) :
    (T.quadranceB + T.quadranceC - T.quadranceA) ^ 2 =
      4 * T.quadranceB * T.quadranceC * (1 - T.spreadA) := by
  have he : T.sideB ^ 2 + T.sideC ^ 2 - T.sideA ^ 2 =
      2 * T.sideB * T.sideC * finiteCos T.angleA := by
    linear_combination -T.cosine_law
  change (T.sideB ^ 2 + T.sideC ^ 2 - T.sideA ^ 2) ^ 2 =
    4 * T.sideB ^ 2 * T.sideC ^ 2 * (1 - finiteSin T.angleA ^ 2)
  rw [he]
  linear_combination 4 * T.sideB ^ 2 * T.sideC ^ 2 * finiteCos_sq_add_finiteSin_sq T.angleA

/-- The exact triple-spread relation `trigonometry:eq:triplespread`. -/
theorem triple_spread (T : Triangle.{u}) :
    (T.spreadA + T.spreadB + T.spreadC) ^ 2 =
      2 * (T.spreadA ^ 2 + T.spreadB ^ 2 + T.spreadC ^ 2) +
        4 * T.spreadA * T.spreadB * T.spreadC :=
  finiteSin_triple_spread T.angleA T.angleB T.angleC T.angle_sum

end Triangle

end
end Surreal.Surcomplex

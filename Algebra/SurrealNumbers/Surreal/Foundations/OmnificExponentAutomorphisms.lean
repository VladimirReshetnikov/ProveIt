import Surreal.Foundations.NormalFormExponentAutomorphisms
import Surreal.Foundations.OmnificAutomorphisms

/-!
# Exponent substitutions preserve the actual omnific ring

The nontrivial automorphism of `odg:def:ex:dilation`, generalized to every
ordered additive automorphism of the actual surreal exponent group.
-/

universe u
namespace Surreal.Foundations.SignSequence
open SmallNormalForm
noncomputable section

@[simp] theorem coeff_exponentAutomorphism
    (e : SignSequence.{u} ≃+o SignSequence.{u}) (x a : SignSequence.{u}) :
    coeff (normalForm (exponentAutomorphism e x)) (e a) = coeff (normalForm x) a := by
  rw [normalForm_exponentAutomorphism]
  exact coeff_mapExponents e (normalForm x) a

@[simp] theorem constant_exponentAutomorphism
    (e : SignSequence.{u} ≃+o SignSequence.{u}) (x : SignSequence.{u}) :
    coeff (normalForm (exponentAutomorphism e x)) 0 = coeff (normalForm x) 0 := by
  simpa only [map_zero] using coeff_exponentAutomorphism e x 0

/-- The entire normal-form support is transported by the exponent bijection. -/
theorem support_exponentAutomorphism
    (e : SignSequence.{u} ≃+o SignSequence.{u}) (x : SignSequence.{u}) :
    support (normalForm (exponentAutomorphism e x)) = e '' support (normalForm x) := by
  ext b
  obtain ⟨a, rfl⟩ := e.surjective b
  change coeff (normalForm (exponentAutomorphism e x)) (e a) ≠ 0 ↔ _
  rw [coeff_exponentAutomorphism]
  simp only [Set.mem_image, mem_support]
  constructor
  · intro h; exact ⟨a, h, rfl⟩
  · rintro ⟨c, hc, he⟩
    exact e.injective he ▸ hc

@[simp] theorem exponentAutomorphism_inverse
    (e : SignSequence.{u} ≃+o SignSequence.{u}) (x : SignSequence.{u}) :
    exponentAutomorphism e.symm (exponentAutomorphism e x) = x := by
  apply SmallNormalForm.cutEvaluationRingEquiv.symm.injective
  change normalForm _ = normalForm _
  rw [normalForm_exponentAutomorphism, normalForm_exponentAutomorphism]
  exact mapExponents_inverse e (normalForm x)

/-- Negative growth coefficients remain zero under an ordered exponent substitution. -/
theorem exponentAutomorphism_mem_supportRing
    (e : SignSequence.{u} ≃+o SignSequence.{u}) {x : SignSequence.{u}}
    (hx : x ∈ nonnegativeSupportSubring) :
    exponentAutomorphism e x ∈ nonnegativeSupportSubring := by
  rw [mem_nonnegativeSupportSubring_iff] at hx ⊢
  intro b hb
  obtain ⟨a, rfl⟩ := e.surjective b
  change coeff (normalForm (exponentAutomorphism e x)) (e a) = 0
  rw [coeff_exponentAutomorphism]
  apply hx a
  apply e.strictMono.lt_iff_lt.mp
  rw [map_zero]
  exact hb

private def omnificExponentMap (e : SignSequence.{u} ≃+o SignSequence.{u})
    (x : OmnificInteger.{u}) : OmnificInteger.{u} :=
  ⟨⟨exponentAutomorphism e (omnificToSurreal x), exponentAutomorphism_mem_supportRing e x.val.property⟩,
    by
      rw [mem_omnificSubring_iff]
      change ∃ n : ℤ, (n : ℝ) = coeff (normalForm (exponentAutomorphism e (omnificToSurreal x))) 0
      rw [constant_exponentAutomorphism]
      exact (mem_omnificSubring_iff x.val).mp x.property⟩

/-- Every ordered exponent automorphism restricts to an actual omnific automorphism. -/
def omnificExponentAutomorphism (e : SignSequence.{u} ≃+o SignSequence.{u}) :
    OmnificInteger.{u} ≃+* OmnificInteger.{u} where
  toFun := omnificExponentMap e
  invFun := omnificExponentMap e.symm
  left_inv x := by
    apply omnificToSurreal_injective
    exact exponentAutomorphism_inverse e (omnificToSurreal x)
  right_inv x := by
    apply omnificToSurreal_injective
    exact exponentAutomorphism_inverse e.symm (omnificToSurreal x)
  map_add' x y := by
    apply omnificToSurreal_injective
    change exponentAutomorphism e (omnificToSurreal (x + y)) =
      omnificToSurreal (omnificExponentMap e x + omnificExponentMap e y)
    rw [map_add, map_add, map_add]; rfl
  map_mul' x y := by
    apply omnificToSurreal_injective
    change exponentAutomorphism e (omnificToSurreal (x * y)) =
      omnificToSurreal (omnificExponentMap e x * omnificExponentMap e y)
    rw [map_mul, map_mul, map_mul]; rfl

@[simp] theorem omnificToSurreal_exponentAutomorphism
    (e : SignSequence.{u} ≃+o SignSequence.{u}) (x : OmnificInteger.{u}) :
    omnificToSurreal (omnificExponentAutomorphism e x) =
      exponentAutomorphism e (omnificToSurreal x) := rfl

/-- The canonical fraction extension agrees with normal-form exponent substitution. -/
theorem omnificAutomorphismExtension_exponentAutomorphism
    (e : SignSequence.{u} ≃+o SignSequence.{u}) :
    omnificAutomorphismExtension (omnificExponentAutomorphism e) = exponentAutomorphism e := by
  apply RingEquiv.toRingHom_injective
  exact (omnificAutomorphismExtension_unique _ (exponentAutomorphism e).toRingHom
    (fun _ => rfl)).symm

/-- Multiplication by a positive actual surreal is an ordered exponent automorphism. -/
def positiveExponentScale (a : SignSequence.{u}) (ha : 0 < a) :
    SignSequence.{u} ≃+o SignSequence.{u} where
  toEquiv := (OrderIso.mulLeft₀ a ha).toEquiv
  map_le_map_iff' := (OrderIso.mulLeft₀ a ha).map_rel_iff
  map_add' x y := mul_add a x y

/-- Scale every Conway exponent by a positive factor. -/
def exponentDilation (a : SignSequence.{u}) (ha : 0 < a) :
    SignSequence.{u} ≃+* SignSequence.{u} := exponentAutomorphism (positiveExponentScale a ha)

theorem positiveExponentScale_inv (a : SignSequence.{u}) (ha : 0 < a) :
    positiveExponentScale a⁻¹ (inv_pos.mpr ha) = (positiveExponentScale a ha).symm := by
  ext b
  rfl

/-- Reciprocal exponent scaling is the inverse on every actual surreal. -/
theorem exponentDilation_inverse (a : SignSequence.{u}) (ha : 0 < a) (x : SignSequence.{u}) :
    exponentDilation a⁻¹ (inv_pos.mpr ha) (exponentDilation a ha x) = x := by
  change exponentAutomorphism (positiveExponentScale a⁻¹ _) (exponentAutomorphism _ x) = x
  rw [positiveExponentScale_inv a ha, exponentAutomorphism_inverse]

/-- The explicit inverse of doubling exponents is halving them. -/
theorem exponentDilation_half_two (x : SignSequence.{u}) :
    exponentDilation (1 / 2 : SignSequence.{u}) (by norm_num)
      (exponentDilation 2 (by norm_num) x) = x := by
  simpa only [one_div] using exponentDilation_inverse (2 : SignSequence.{u}) (by norm_num) x

@[simp] theorem coeff_exponentDilation (a : SignSequence.{u}) (ha : 0 < a)
    (x b : SignSequence.{u}) :
    coeff (normalForm (exponentDilation a ha x)) (a * b) = coeff (normalForm x) b :=
  coeff_exponentAutomorphism (positiveExponentScale a ha) x b

@[simp] theorem exponentDilation_omegaPower (a : SignSequence.{u}) (ha : 0 < a)
    (b : SignSequence.{u}) : exponentDilation a ha (omegaPower b) = omegaPower (a * b) :=
  exponentAutomorphism_omegaPower (positiveExponentScale a ha) b

/-- The printed doubling example sends omega to its square. -/
theorem exponentDilation_two_omega :
    exponentDilation (2 : SignSequence.{u}) (by norm_num) (omegaPower 1) = (omegaPower 1) ^ 2 := by
  rw [exponentDilation_omegaPower, mul_one, pow_two, ← omegaPower_add]
  norm_num

/-- Exponent substitution is not squaring: its image of one plus omega has no cross term. -/
theorem exponentDilation_two_one_add_omega :
    exponentDilation (2 : SignSequence.{u}) (by norm_num) (1 + omegaPower 1) =
      1 + (omegaPower 1) ^ 2 := by
  rw [map_add, map_one, exponentDilation_two_omega]

/-- An explicit omnific element moved by an actual ring automorphism. -/
theorem omnificExponentAutomorphism_two_moves_omega :
    omnificExponentAutomorphism (positiveExponentScale (2 : SignSequence.{u}) (by norm_num))
      (omnificMonomial 1 zero_lt_one) ≠ omnificMonomial 1 zero_lt_one := by
  intro h
  have he := congrArg omnificToSurreal h
  rw [omnificToSurreal_exponentAutomorphism, omnificToSurreal_monomial,
    exponentAutomorphism_omegaPower, omegaPower_inj] at he
  change (2 : SignSequence.{u}) * 1 = 1 at he
  norm_num at he

/-- The automorphism group of the actual omnific ring is nontrivial. -/
theorem exists_nontrivial_omnificAutomorphism :
    ∃ f : OmnificInteger.{u} ≃+* OmnificInteger.{u}, ∃ x, f x ≠ x :=
  ⟨omnificExponentAutomorphism (positiveExponentScale 2 (by norm_num)),
    omnificMonomial 1 zero_lt_one, omnificExponentAutomorphism_two_moves_omega⟩

end
end Surreal.Foundations.SignSequence

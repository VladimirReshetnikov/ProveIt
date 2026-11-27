import GRHArticle.SingularModuli.CMPoints
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Nat.Sqrt

/-!
# Finite lists of primitive reduced forms and their analytic class polynomial

The leading coefficient lies in `1 ≤ a ≤ √(D/3)`, the middle coefficient
in `[-a,a]`, and the discriminant determines the last coefficient. Fixing
the sign on the boundary avoids counting both representatives of one form.
-/

namespace GRHArticle.SingularModuli

open Polynomial

/-- Coefficients of the integral binary quadratic form `ax²+bxy+cy²`. -/
structure FormCoefficients where
  a : ℕ+
  b : ℤ
  c : ℤ
  deriving DecidableEq

/-- Primitive reduced representatives of discriminant `-D`, with the
usual nonnegative middle coefficient on the boundary. -/
def IsPrimitiveReducedForm (D : ℕ+) (f : FormCoefficients) : Prop :=
  f.b ^ 2 - 4 * (f.a : ℤ) * f.c = -(D : ℤ) ∧ |f.b| ≤ (f.a : ℤ) ∧ (f.a : ℤ) ≤ f.c ∧
    ((|f.b| = (f.a : ℤ) ∨ (f.a : ℤ) = f.c) → 0 ≤ f.b) ∧
    Nat.gcd (Nat.gcd (f.a : ℕ) f.b.natAbs) f.c.natAbs = 1

instance (D : ℕ+) (f : FormCoefficients) : Decidable (IsPrimitiveReducedForm D f) := by
  unfold IsPrimitiveReducedForm
  infer_instance

private def formAt (D : ℕ+) (k j : ℕ) : FormCoefficients :=
  let b : ℤ := (j : ℤ) - ((k : ℤ) + 1)
  ⟨k.succPNat, b, (b ^ 2 + D) / (4 * (k + 1))⟩

private def candidateForms (D : ℕ+) (k : ℕ) : Finset FormCoefficients :=
  ((Finset.range (2 * (k + 1) + 1)).filter fun j => IsPrimitiveReducedForm D (formAt D k j)).image
    (formAt D k)

/-- An executable enumeration over the possible leading and middle coefficients. -/
def reducedForms (D : ℕ+) : Finset FormCoefficients :=
  (Finset.range ((D : ℕ) / 3).sqrt).biUnion (candidateForms D)

theorem mem_reducedForms_iff (D : ℕ+) (f : FormCoefficients) :
    f ∈ reducedForms D ↔ IsPrimitiveReducedForm D f := by
  rw [reducedForms]
  constructor
  · intro hf
    obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp hf
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    exact (Finset.mem_filter.mp hj).2
  intro h
  have hf := h
  rcases f with ⟨a, b, c⟩
  obtain ⟨hdisc, hb, hc, _⟩ := h
  have h := three_mul_sq_le_of_reduced D a b c hdisc hb hc
  have hs : (a : ℕ) ≤ ((D : ℕ) / 3).sqrt :=
    Nat.le_sqrt'.mpr ((Nat.le_div_iff_mul_le (by decide : 0 < 3)).mpr (by simpa [mul_comm] using h))
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt a.pos)
  have ha : a = k.succPNat := Subtype.ext hk
  subst a
  simp only [Nat.succPNat_coe, Nat.cast_succ] at hb hc hdisc
  have he : b ^ 2 + (D : ℤ) = (4 * (k + 1)) * c := by linarith
  apply Finset.mem_biUnion.mpr
  have hb' := abs_le.mp hb
  let j := (b + (k + 1 : ℤ)).toNat
  have hj : (j : ℤ) = b + (k + 1 : ℤ) := Int.toNat_of_nonneg (by omega)
  have hform : formAt D k j = ⟨k.succPNat, b, c⟩ := by
    simp [formAt, hj, he, show (4 * (k + 1) : ℤ) ≠ 0 by positivity]
  refine ⟨k, Finset.mem_range.mpr (by simpa using hs), Finset.mem_image.mpr ⟨j, ?_, hform⟩⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hform ▸ hf⟩

theorem reducedForms_three :
    reducedForms 3 = {⟨1, 1, 1⟩} := by decide +kernel

theorem reducedForms_four :
    reducedForms 4 = {⟨1, 0, 1⟩} := by decide +kernel

theorem reducedForms_fiftyFive :
    reducedForms 55 = {⟨1, 1, 14⟩, ⟨2, -1, 7⟩, ⟨2, 1, 7⟩, ⟨4, 3, 4⟩} := by decide +kernel

theorem reducedForms_sixtyEight :
    reducedForms 68 = {⟨1, 0, 17⟩, ⟨2, 2, 9⟩, ⟨3, -2, 6⟩, ⟨3, 2, 6⟩} := by decide +kernel

/-- The complex class polynomial defined as the product over reduced forms,
before asserting integrality or identifying an integer coefficient table. -/
noncomputable def analyticClassPolynomial (D : ℕ+) : ℂ[X] :=
  ∏ f ∈ reducedForms D, (X - C (modularInvariant (quadraticPoint D f.a f.b)))

theorem analyticClassPolynomial_monic (D : ℕ+) : (analyticClassPolynomial D).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

theorem analyticClassPolynomial_natDegree (D : ℕ+) :
    (analyticClassPolynomial D).natDegree = (reducedForms D).card := by
  simp [analyticClassPolynomial, natDegree_prod_of_monic, monic_X_sub_C]

/-- Exactly the values at primitive reduced forms are roots of the analytic polynomial. -/
theorem analyticClassPolynomial_eval_eq_zero_iff (D : ℕ+) (y : ℂ) :
    (analyticClassPolynomial D).eval y = 0 ↔
      ∃ f : FormCoefficients, IsPrimitiveReducedForm D f ∧ y = modularInvariant (quadraticPoint D f.a f.b) := by
  simp [analyticClassPolynomial, eval_prod, Finset.prod_eq_zero_iff, mem_reducedForms_iff, sub_eq_zero]

theorem analyticClassPolynomial_fiftyFive_natDegree : (analyticClassPolynomial 55).natDegree = 4 := by
  rw [analyticClassPolynomial_natDegree, reducedForms_fiftyFive]
  decide

theorem analyticClassPolynomial_sixtyEight_natDegree : (analyticClassPolynomial 68).natDegree = 4 := by
  rw [analyticClassPolynomial_natDegree, reducedForms_sixtyEight]
  decide

theorem analyticClassPolynomial_three : analyticClassPolynomial 3 = X := by
  simp [analyticClassPolynomial, reducedForms_three, modularInvariant_discriminant_neg_three]

theorem analyticClassPolynomial_four : analyticClassPolynomial 4 = X - C 1728 := by
  simp [analyticClassPolynomial, reducedForms_four, modularInvariant_discriminant_neg_four]

end GRHArticle.SingularModuli

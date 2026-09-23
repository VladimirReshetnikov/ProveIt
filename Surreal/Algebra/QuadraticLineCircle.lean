import Surreal.Algebra.QuadraticResidueAlgebra

/-!
# The line-circle coordinate algebra at every collision parameter

The quotient in `trigonometry:eq:quadalgebra` represents the original
line-circle equations over every commutative algebra, including algebras
with nilpotents. The explicit normal/perpendicular coordinate change gives
the universal-property equivalence, rather than only a bijection of points
over a field. Normalized coefficients work over arbitrary commutative
rings; division by the nonzero amplitude is performed in the base field.
-/

namespace Surreal.FinitePolynomial

open Polynomial

noncomputable section

section Ring

variable {R : Type*} [CommRing R]

/-- Solutions of the actual circle and line equations in a commutative coefficient algebra. -/
def lineCirclePoints (A B D : R) (S : Type*) [CommRing S] [Algebra R S] :=
  {xy : S × S // xy.1 ^ 2 + xy.2 ^ 2 = 1 ∧
    algebraMap R S A * xy.1 + algebraMap R S B * xy.2 = algebraMap R S D}

/-- The universal property of the quadratic quotient, retaining arbitrary target nilpotents. -/
def quadraticHomEquivRoots (d : R) (S : Type*) [CommRing S] [Algebra R S] :
    (quadraticQuotient d →ₐ[R] S) ≃ {w : S // w ^ 2 = algebraMap R S d} where
  toFun f := ⟨f (quadraticRoot d), by
    rw [← map_pow, quadraticRoot_sq, AlgHom.commutes]⟩
  invFun w := AdjoinRoot.liftAlgHom (quadraticPolynomial d) (Algebra.ofId R S) w.val
    (by simpa [quadraticPolynomial] using sub_eq_zero.mpr w.property)
  left_inv f := by
    apply AdjoinRoot.algHom_ext
    simp [quadraticRoot]
  right_inv w := by
    apply Subtype.ext
    simp [quadraticRoot]

@[simp] theorem quadraticHomEquivRoots_apply (d : R) (S : Type*) [CommRing S] [Algebra R S]
    (f : quadraticQuotient d →ₐ[R] S) :
    (quadraticHomEquivRoots d S f).val = f (quadraticRoot d) := rfl

@[simp] theorem quadraticHomEquivRoots_symm_root (d : R) (S : Type*)
    [CommRing S] [Algebra R S] (w : {w : S // w ^ 2 = algebraMap R S d}) :
    (quadraticHomEquivRoots d S).symm w (quadraticRoot d) = w.val := by
  simp [quadraticHomEquivRoots, quadraticRoot]

private theorem normalized_coordinates_satisfy (a b c w : R)
    (hn : a ^ 2 + b ^ 2 = 1) (hw : w ^ 2 = 1 - c ^ 2) :
    (a * c - b * w) ^ 2 + (b * c + a * w) ^ 2 = 1 ∧
      a * (a * c - b * w) + b * (b * c + a * w) = c := by
  constructor
  · rw [show (a * c - b * w) ^ 2 + (b * c + a * w) ^ 2 =
      (a ^ 2 + b ^ 2) * (c ^ 2 + w ^ 2) by ring, hn, one_mul, hw]
    ring
  · rw [show a * (a * c - b * w) + b * (b * c + a * w) =
      (a ^ 2 + b ^ 2) * c by ring, hn, one_mul]

private theorem normalized_cross_sq (a b c x y : R) (hn : a ^ 2 + b ^ 2 = 1)
    (hc : x ^ 2 + y ^ 2 = 1) (hl : a * x + b * y = c) :
    (a * y - b * x) ^ 2 = 1 - c ^ 2 := by
  have h : (a * x + b * y) ^ 2 + (a * y - b * x) ^ 2 =
      (a ^ 2 + b ^ 2) * (x ^ 2 + y ^ 2) := by ring
  rw [hn, hc, hl, one_mul] at h
  linear_combination h

private theorem normalized_reconstruct (a b c x y : R)
    (hn : a ^ 2 + b ^ 2 = 1) (hl : a * x + b * y = c) :
    a * c - b * (a * y - b * x) = x ∧
      b * c + a * (a * y - b * x) = y := by
  rw [← hl]
  constructor
  · rw [show a * (a * x + b * y) - b * (a * y - b * x) =
      (a ^ 2 + b ^ 2) * x by ring, hn, one_mul]
  · rw [show b * (a * x + b * y) + a * (a * y - b * x) =
      (a ^ 2 + b ^ 2) * y by ring, hn, one_mul]

/-- Normalized line-circle coordinates and the quadratic coordinate are inverse over any algebra. -/
def normalizedQuadraticRootsEquiv (a b c d : R) (hn : a ^ 2 + b ^ 2 = 1)
    (hd : d = 1 - c ^ 2) (S : Type*) [CommRing S] [Algebra R S] :
    {w : S // w ^ 2 = algebraMap R S d} ≃ lineCirclePoints a b c S where
  toFun w := ⟨(algebraMap R S a * algebraMap R S c - algebraMap R S b * w.val,
    algebraMap R S b * algebraMap R S c + algebraMap R S a * w.val), by
      apply normalized_coordinates_satisfy
      · simpa only [map_add, map_pow, map_one] using congrArg (algebraMap R S) hn
      · simpa only [hd, map_sub, map_one, map_pow] using w.property⟩
  invFun xy := ⟨algebraMap R S a * xy.val.2 - algebraMap R S b * xy.val.1, by
    rw [hd, map_sub, map_one, map_pow]
    exact normalized_cross_sq _ _ _ _ _
      (by simpa only [map_add, map_pow, map_one] using congrArg (algebraMap R S) hn)
      xy.property.1 xy.property.2⟩
  left_inv w := by
    apply Subtype.ext
    change algebraMap R S a * (algebraMap R S b * algebraMap R S c +
        algebraMap R S a * w.val) - algebraMap R S b *
        (algebraMap R S a * algebraMap R S c - algebraMap R S b * w.val) = w.val
    have hn' : algebraMap R S a ^ 2 + algebraMap R S b ^ 2 = 1 := by
      simpa only [map_add, map_pow, map_one] using congrArg (algebraMap R S) hn
    calc
      _ = (algebraMap R S a ^ 2 + algebraMap R S b ^ 2) * w.val := by ring
      _ = _ := by rw [hn', one_mul]
  right_inv xy := by
    apply Subtype.ext
    apply Prod.ext
    · exact (normalized_reconstruct _ _ _ _ _
        (by simpa only [map_add, map_pow, map_one] using congrArg (algebraMap R S) hn)
        xy.property.2).1
    · exact (normalized_reconstruct _ _ _ _ _
        (by simpa only [map_add, map_pow, map_one] using congrArg (algebraMap R S) hn)
        xy.property.2).2

/-- The normalized quadratic algebra represents the line-circle equations over every target algebra. -/
def normalizedQuadraticLineCircleEquiv (a b c d : R) (hn : a ^ 2 + b ^ 2 = 1)
    (hd : d = 1 - c ^ 2) (S : Type*) [CommRing S] [Algebra R S] :
    (quadraticQuotient d →ₐ[R] S) ≃ lineCirclePoints a b c S :=
  (quadraticHomEquivRoots d S).trans (normalizedQuadraticRootsEquiv a b c d hn hd S)

@[simp] theorem normalizedQuadraticLineCircleEquiv_fst (a b c d : R)
    (hn : a ^ 2 + b ^ 2 = 1) (hd : d = 1 - c ^ 2)
    (S : Type*) [CommRing S] [Algebra R S] (f : quadraticQuotient d →ₐ[R] S) :
    (normalizedQuadraticLineCircleEquiv a b c d hn hd S f).val.1 =
      algebraMap R S a * algebraMap R S c - algebraMap R S b * f (quadraticRoot d) := rfl

@[simp] theorem normalizedQuadraticLineCircleEquiv_snd (a b c d : R)
    (hn : a ^ 2 + b ^ 2 = 1) (hd : d = 1 - c ^ 2)
    (S : Type*) [CommRing S] [Algebra R S] (f : quadraticQuotient d →ₐ[R] S) :
    (normalizedQuadraticLineCircleEquiv a b c d hn hd S f).val.2 =
      algebraMap R S b * algebraMap R S c + algebraMap R S a * f (quadraticRoot d) := rfl

@[simp] theorem normalizedQuadraticLineCircleEquiv_symm_root (a b c d : R)
    (hn : a ^ 2 + b ^ 2 = 1) (hd : d = 1 - c ^ 2)
    (S : Type*) [CommRing S] [Algebra R S] (xy : lineCirclePoints a b c S) :
    (normalizedQuadraticLineCircleEquiv a b c d hn hd S).symm xy (quadraticRoot d) =
      algebraMap R S a * xy.val.2 - algebraMap R S b * xy.val.1 := by
  exact quadraticHomEquivRoots_symm_root d S _

end Ring

section Field

variable {K : Type*} [Field K]

/-- Dividing the line equation by a nonzero base-field amplitude is valid in every target algebra. -/
theorem lineCircle_normalized_equation_iff (A B D ρ : K) (hρ : ρ ≠ 0)
    (S : Type*) [CommRing S] [Algebra K S] (x y : S) :
    algebraMap K S (A / ρ) * x + algebraMap K S (B / ρ) * y = algebraMap K S (D / ρ) ↔
      algebraMap K S A * x + algebraMap K S B * y = algebraMap K S D := by
  have hc (t : K) : ρ * (t / ρ) = t := by
    calc
      _ = t * (ρ / ρ) := by ring
      _ = t := by rw [div_self hρ, mul_one]
  constructor
  · intro hl
    have he := congrArg (fun z : S => algebraMap K S ρ * z) hl
    simpa only [mul_add, ← mul_assoc, ← map_mul, hc] using he
  · intro hl
    have he := congrArg (fun z : S => z * algebraMap K S ρ⁻¹) hl
    simpa only [div_eq_mul_inv, map_mul, add_mul, mul_right_comm] using he

/-- Normalizing the coefficients preserves exactly the same solution pair in every algebra. -/
def lineCircleNormalizeEquiv (A B D ρ : K) (hρ : ρ ≠ 0)
    (S : Type*) [CommRing S] [Algebra K S] :
    lineCirclePoints (A / ρ) (B / ρ) (D / ρ) S ≃ lineCirclePoints A B D S where
  toFun xy := ⟨xy.val, xy.property.1,
    (lineCircle_normalized_equation_iff A B D ρ hρ S _ _).mp xy.property.2⟩
  invFun xy := ⟨xy.val, xy.property.1,
    (lineCircle_normalized_equation_iff A B D ρ hρ S _ _).mpr xy.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The complete coordinate-algebra identification in `trigonometry:eq:quadalgebra`.
Its target is every commutative algebra, so the equivalence retains collision nilpotents. -/
def quadraticLineCircleEquiv (A B D ρ : K) (hρ : ρ ≠ 0) (hn : ρ ^ 2 = A ^ 2 + B ^ 2)
    (S : Type*) [CommRing S] [Algebra K S] :
    (quadraticQuotient ((ρ ^ 2 - D ^ 2) / ρ ^ 2) →ₐ[K] S) ≃ lineCirclePoints A B D S :=
  (normalizedQuadraticLineCircleEquiv (A / ρ) (B / ρ) (D / ρ)
    ((ρ ^ 2 - D ^ 2) / ρ ^ 2)
    (by rw [div_pow, div_pow, ← add_div, ← hn, div_self (pow_ne_zero 2 hρ)])
    (by rw [sub_div, div_self (pow_ne_zero 2 hρ), div_pow]) S).trans
    (lineCircleNormalizeEquiv A B D ρ hρ S)

/-- The universal point's first original coordinate. -/
@[simp] theorem quadraticLineCircleEquiv_fst (A B D ρ : K)
    (hρ : ρ ≠ 0) (hn : ρ ^ 2 = A ^ 2 + B ^ 2)
    (S : Type*) [CommRing S] [Algebra K S]
    (f : quadraticQuotient ((ρ ^ 2 - D ^ 2) / ρ ^ 2) →ₐ[K] S) :
    (quadraticLineCircleEquiv A B D ρ hρ hn S f).val.1 =
      algebraMap K S (A / ρ) * algebraMap K S (D / ρ) -
        algebraMap K S (B / ρ) * f (quadraticRoot ((ρ ^ 2 - D ^ 2) / ρ ^ 2)) := rfl

/-- The universal point's second original coordinate. -/
@[simp] theorem quadraticLineCircleEquiv_snd (A B D ρ : K)
    (hρ : ρ ≠ 0) (hn : ρ ^ 2 = A ^ 2 + B ^ 2)
    (S : Type*) [CommRing S] [Algebra K S]
    (f : quadraticQuotient ((ρ ^ 2 - D ^ 2) / ρ ^ 2) →ₐ[K] S) :
    (quadraticLineCircleEquiv A B D ρ hρ hn S f).val.2 =
      algebraMap K S (B / ρ) * algebraMap K S (D / ρ) +
        algebraMap K S (A / ρ) * f (quadraticRoot ((ρ ^ 2 - D ^ 2) / ρ ^ 2)) := rfl

/-- The inverse sends the quotient generator to the normalized perpendicular coordinate. -/
@[simp] theorem quadraticLineCircleEquiv_symm_root (A B D ρ : K)
    (hρ : ρ ≠ 0) (hn : ρ ^ 2 = A ^ 2 + B ^ 2)
    (S : Type*) [CommRing S] [Algebra K S] (xy : lineCirclePoints A B D S) :
    (quadraticLineCircleEquiv A B D ρ hρ hn S).symm xy
        (quadraticRoot ((ρ ^ 2 - D ^ 2) / ρ ^ 2)) =
      algebraMap K S (A / ρ) * xy.val.2 - algebraMap K S (B / ρ) * xy.val.1 := by
  simp only [quadraticLineCircleEquiv, Equiv.symm_trans_apply,
    normalizedQuadraticLineCircleEquiv_symm_root]
  rfl

end Field

end
end Surreal.FinitePolynomial

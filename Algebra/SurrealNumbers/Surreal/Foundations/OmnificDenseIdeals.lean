import Surreal.Foundations.OmnificIdealClosure
import Surreal.Foundations.OmnificPrincipalImages
import Surreal.Foundations.OmnificIrreducibles

/-!
# Proper dense omnific principal ideals

The full `osq:cor:dense`. A nonconstant generator with unit constant term
generates a proper dense ideal. This applies to every nonconstant
irreducible. Its quotient has no nonzero small unital image; even a
nonunital map to a small ring that kills the generator must be zero.
-/

universe u v
namespace Surreal.Foundations.SignSequence
noncomputable section

/-- A principal ideal is dense precisely when the generator has unit constant coefficient. -/
theorem omnific_principal_dense_iff (f : OmnificInteger.{u}) :
    @Dense OmnificInteger omnificCongruenceTopology (Ideal.span {f} : Set OmnificInteger) ↔
      IsUnit (omnificConstantCoeff f) := by
  rw [omnificCongruenceTopology_dense_iff, Ideal.map_span, Set.image_singleton,
    Ideal.span_singleton_eq_top]

/-- Nonconstant generators with constant term plus or minus one give proper dense ideals. -/
theorem omnific_principal_proper_dense (f : OmnificInteger.{u})
    (hf : ¬ ∃ n : ℤ, f = omnificIntCast n) (hc : IsUnit (omnificConstantCoeff f)) :
    Ideal.span {f} ≠ ⊤ ∧
      @Dense OmnificInteger omnificCongruenceTopology (Ideal.span {f} : Set OmnificInteger) :=
  ⟨Ideal.Quotient.nontrivial_iff.mp (omnific_principal_quotient_nontrivial f hf),
    (omnific_principal_dense_iff f).mpr hc⟩

/-- Every small unital ring image sends such a generator to plus or minus one. -/
theorem omnific_unit_constant_small_ringHom {S : Type v} [Ring S] [Small.{u} S]
    (φ : OmnificInteger.{u} →+* S) (f : OmnificInteger.{u})
    (hc : IsUnit (omnificConstantCoeff f)) : φ f = 1 ∨ φ f = -1 := by
  rw [omnific_small_ringHom_eq_constant φ f]
  rcases Int.isUnit_iff.mp hc with h | h
  · exact Or.inl (by rw [h, Int.cast_one])
  · exact Or.inr (by rw [h, Int.cast_neg, Int.cast_one])

/-- Even a nonunital map to a small ring that kills a unit-constant element is zero. -/
theorem omnific_small_nonunital_eq_zero_of_unit_constant {S : Type v}
    [NonUnitalRing S] [Small.{u} S] (φ : OmnificInteger.{u} →ₙ+* S)
    (f : OmnificInteger.{u}) (hc : IsUnit (omnificConstantCoeff f)) (hf : φ f = 0) : φ = 0 := by
  have h1 : φ 1 = 0 := by
    rw [omnific_small_hom_eq_constant φ f] at hf
    rcases Int.isUnit_iff.mp hc with h | h
    · simpa only [h, map_one] using hf
    · simpa only [h, map_neg, map_one, neg_eq_zero] using hf
  ext x
  change φ x = 0
  calc
    φ x = φ 1 * φ x := by rw [← map_mul, _root_.one_mul]
    _ = 0 := by rw [h1, zero_mul]

/-- Every nonconstant irreducible generates a proper dense ideal invisible to small unital rings. -/
theorem omnific_nonconstant_irreducible_dense (f : OmnificInteger.{u})
    (hf : Irreducible f) (hn : ¬ ∃ n : ℤ, f = omnificIntCast n)
    (S : Type v) [Ring S] [Nontrivial S] [Small.{u} S] :
    (omnificConstantCoeff f = 1 ∨ omnificConstantCoeff f = -1) ∧
      Ideal.span {f} ≠ ⊤ ∧
      @Dense OmnificInteger omnificCongruenceTopology (Ideal.span {f} : Set OmnificInteger) ∧
      ¬ Nonempty ((OmnificInteger.{u} ⧸ Ideal.span {f}) →+* S) := by
  have hc := omnific_nonconstant_irreducible_constant f hf hn
  have hu := Int.isUnit_iff.mpr hc
  exact ⟨hc, (omnific_principal_proper_dense f hn hu).1,
    (omnific_principal_proper_dense f hn hu).2, omnific_principal_no_small_ringHom f hu S⟩

end
end Surreal.Foundations.SignSequence

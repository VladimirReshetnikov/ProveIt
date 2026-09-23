import Surreal.Foundations.OmnificFiniteQuotients

/-!
# Canonical constant extraction and invisible infinite elements

The full `odg:prop:canonicalct`, together with the following noninjective
endomorphism example and the non-residual-finiteness assertion following
`odg:eq:profinite`. The latter is expressed by a nonzero actual omnific
integer killed by every finite-target ring homomorphism in any universe.
No inverse-limit construction or congruence-topology theorem is claimed here.
-/

universe u v
namespace Surreal.Foundations.SignSequence

open SmallNormalForm

noncomputable section

/-- Every homomorphism from the omnific ring to the ordinary integers kills its infinite part. -/
theorem omnific_int_hom_kills_purelyInfinite (f : OmnificInteger.{u} →+* ℤ)
    (x : OmnificInteger.{u}) (hx : x ∈ omnificPurelyInfiniteIdeal) : f x = 0 := by
  have hd (k : ℕ) : (2 : ℤ) ^ k ∣ f x := by
    obtain ⟨y, hy⟩ := omnific_int_dvd_of_purelyInfinite ((2 : ℤ) ^ k)
      (pow_ne_zero k (by norm_num)) x hx
    refine ⟨f y, ?_⟩
    simpa only [map_mul, omnific_hom_intCast, Int.cast_id] using congrArg f hy
  have hb := (padicValInt_dvd_iff (p := 2) (padicValInt 2 (f x) + 1) (f x)).mp
    (hd (padicValInt 2 (f x) + 1))
  exact hb.resolve_right (by omega)

/-- The constant-term map is the unique unital homomorphism to the ordinary integers. -/
theorem omnific_int_hom_eq_constant (f : OmnificInteger.{u} →+* ℤ) :
    f = omnificConstantCoeff := by
  apply RingHom.ext
  intro x
  obtain ⟨j, hj, hx⟩ := omnific_constant_decomposition x
  calc
    f x = f (omnificIntCast (omnificConstantCoeff x) + j) := congrArg f hx
    _ = omnificConstantCoeff x := by
      rw [map_add, omnific_hom_intCast, omnific_int_hom_kills_purelyInfinite f j hj,
        Int.cast_id, _root_.add_zero]

/-- Every omnific endomorphism fixes integer constant extraction. -/
theorem omnific_endomorphism_constant (f : OmnificInteger.{u} →+* OmnificInteger.{u}) :
    omnificConstantCoeff.comp f = omnificConstantCoeff :=
  omnific_int_hom_eq_constant (omnificConstantCoeff.comp f)

/-- Endomorphisms preserve the purely infinite ideal, in both directions under inverse image. -/
theorem omnific_endomorphism_purelyInfinite_iff
    (f : OmnificInteger.{u} →+* OmnificInteger.{u}) (x : OmnificInteger.{u}) :
    f x ∈ omnificPurelyInfiniteIdeal ↔ x ∈ omnificPurelyInfiniteIdeal := by
  change omnificConstantCoeff (f x) = 0 ↔ omnificConstantCoeff x = 0
  have h := RingHom.congr_fun (omnific_endomorphism_constant f) x
  change omnificConstantCoeff (f x) = omnificConstantCoeff x at h
  rw [h]

/-- The exact inverse image of the purely infinite ideal under every omnific endomorphism. -/
theorem omnific_endomorphism_comap_purelyInfinite
    (f : OmnificInteger.{u} →+* OmnificInteger.{u}) :
    omnificPurelyInfiniteIdeal.comap f = omnificPurelyInfiniteIdeal := by
  ext x
  exact omnific_endomorphism_purelyInfinite_iff f x

/-- Every positive Conway monomial is an actual omnific integer with no constant term. -/
def omnificMonomial (a : SignSequence.{u}) (ha : 0 < a) : OmnificInteger.{u} :=
  ⟨⟨omegaPower a, by
      rw [mem_nonnegativeSupportSubring_iff]
      intro b hb
      simp only [normalForm_omegaPower, coeff_single, if_neg (ne_of_lt (hb.trans ha))]⟩,
    by
      rw [mem_omnificSubring_iff]
      refine ⟨0, ?_⟩
      simp only [normalForm_omegaPower, coeff_single, if_neg (ne_of_lt ha), Int.cast_zero]⟩

@[simp] theorem omnificToSurreal_monomial (a : SignSequence.{u}) (ha : 0 < a) :
    omnificToSurreal (omnificMonomial a ha) = omegaPower a := rfl

/-- The monomial witness is nonzero in the actual omnific ring. -/
theorem omnificMonomial_ne_zero (a : SignSequence.{u}) (ha : 0 < a) :
    omnificMonomial a ha ≠ 0 := by
  intro h
  have hz := congrArg omnificToSurreal h
  rw [omnificToSurreal_monomial, map_zero] at hz
  exact omegaPower_ne_zero a hz

/-- A positive-growth monomial belongs to the purely infinite ideal. -/
theorem omnificMonomial_mem_purelyInfinite (a : SignSequence.{u}) (ha : 0 < a) :
    omnificMonomial a ha ∈ omnificPurelyInfiniteIdeal := by
  change omnificConstantCoeff (omnificMonomial a ha) = 0
  apply Int.cast_injective (α := ℝ)
  rw [cast_omnificConstantCoeff, omnificToSurreal_monomial, normalForm_omegaPower,
    coeff_single, if_neg (ne_of_lt ha), Int.cast_zero]

/-- The purely infinite ideal is nonzero, witnessed by the positive monomial of exponent one. -/
theorem omnificPurelyInfiniteIdeal_ne_bot : omnificPurelyInfiniteIdeal.{u} ≠ ⊥ := by
  intro h
  have hm := omnificMonomial_mem_purelyInfinite (1 : SignSequence.{u}) zero_lt_one
  rw [h, Ideal.mem_bot] at hm
  exact omnificMonomial_ne_zero _ _ hm

/-- A nonzero omnific element is invisible to every finite ring target of any specified universe. -/
theorem omnific_exists_nonzero_killed_by_finite_rings :
    ∃ x : OmnificInteger.{u}, x ≠ 0 ∧
      ∀ (R : Type v) [Ring R] [Finite R] (f : OmnificInteger.{u} →+* R), f x = 0 := by
  refine ⟨omnificMonomial 1 zero_lt_one, omnificMonomial_ne_zero _ _, ?_⟩
  intro R _ _ f
  exact omnific_finite_hom_kills_purelyInfinite f _ (omnificMonomial_mem_purelyInfinite _ _)

/-- Finite-target ring homomorphisms cannot separate all nonzero omnific integers from zero. -/
theorem omnific_not_residually_finite :
    ¬ (∀ x : OmnificInteger.{u}, x ≠ 0 →
      ∃ (R : Type v) (_ : Ring R) (_ : Finite R) (f : OmnificInteger.{u} →+* R), f x ≠ 0) := by
  obtain ⟨x, hx, hkill⟩ := omnific_exists_nonzero_killed_by_finite_rings.{u, v}
  intro h
  obtain ⟨R, hR, hfinite, f, hf⟩ := h x hx
  exact hf (hkill R f)

/-- Retraction to the ordinary constants, regarded as an actual omnific endomorphism. -/
def omnificConstantEndomorphism : OmnificInteger.{u} →+* OmnificInteger.{u} :=
  omnificIntCast.comp omnificConstantCoeff

/-- The constant retraction is idempotent. -/
theorem omnificConstantEndomorphism_idempotent :
    ∀ x : OmnificInteger.{u},
      omnificConstantEndomorphism (omnificConstantEndomorphism x) =
        omnificConstantEndomorphism x := by
  intro x
  change omnificIntCast (omnificConstantCoeff (omnificIntCast (omnificConstantCoeff x))) = _
  rw [omnificConstantCoeff_intCast]
  rfl

/-- The concrete constant retraction is noninjective. -/
theorem omnificConstantEndomorphism_not_injective :
    ¬ Function.Injective (omnificConstantEndomorphism.{u}) := by
  intro h
  let x := omnificMonomial (1 : SignSequence.{u}) zero_lt_one
  have hx : omnificConstantCoeff x = 0 := omnificMonomial_mem_purelyInfinite _ _
  have he : omnificConstantEndomorphism x = omnificConstantEndomorphism 0 := by
    change omnificIntCast (omnificConstantCoeff x) = omnificIntCast (omnificConstantCoeff 0)
    simp only [hx, map_zero]
  exact omnificMonomial_ne_zero _ _ (h he)

/-- In particular the constant retraction is not the identity endomorphism. -/
theorem omnificConstantEndomorphism_ne_id :
    omnificConstantEndomorphism.{u} ≠ RingHom.id OmnificInteger.{u} := by
  intro h
  apply omnificConstantEndomorphism_not_injective
  rw [h]
  exact Function.injective_id

end
end Surreal.Foundations.SignSequence

import Surreal.Foundations.OmnificSmallTargets

/-!
# Ordered specializations and small retracts of omnific integers

Clauses (i) and (ii) of `osq:cor:rigid`, with the real automorphism
consequence in (iii). The target of an ordered specialization need only
be partially ordered. A retraction onto a unital subring is specified by
its pointwise action on the subring.
-/

universe u v
namespace Surreal.Foundations.SignSequence

/-- No unital specialization to a nonzero small ordered ring preserves order. -/
theorem omnific_no_monotone_small_ringHom {S : Type v} [Ring S] [PartialOrder S]
    [IsOrderedRing S] [Nontrivial S] [Small.{u} S] (φ : OmnificInteger.{u} →+* S) :
    ¬ Monotone φ := by
  intro hφ
  let w := omnificMonomial (1 : SignSequence.{u}) zero_lt_one
  have hw : omnificConstantCoeff w = 0 := omnificMonomial_mem_purelyInfinite _ _
  have hbig : 1 < w := by
    change 1 < omegaPower (1 : SignSequence.{u})
    simpa only [omegaPower_zero] using omegaPower_strictMono (zero_lt_one : (0 : SignSequence.{u}) < 1)
  have h := hφ hbig.le
  rw [map_one, omnific_small_ringHom_eq_constant φ w, hw, Int.cast_zero] at h
  exact (not_le_of_gt (_root_.zero_lt_one : (0 : S) < 1)) h

/-- A small unital subring is a ring retract exactly when it is the integer subring. -/
theorem omnific_small_subring_retract_iff (A : Subring OmnificInteger.{u}) [Small.{u} A] :
    (∃ φ : OmnificInteger.{u} →+* A, ∀ a : A, φ a.val = a) ↔
      A = omnificIntCast.range := by
  constructor
  · rintro ⟨φ, hφ⟩
    apply le_antisymm
    · intro x hx
      refine ⟨omnificConstantCoeff x, ?_⟩
      have he := congrArg Subtype.val (hφ ⟨x, hx⟩)
      rw [omnific_small_ringHom_eq_constant] at he
      rw [show omnificIntCast (omnificConstantCoeff x) =
        (omnificConstantCoeff x : OmnificInteger.{u}) from map_intCast _ _]
      exact he
    · rintro x ⟨n, rfl⟩
      rw [show omnificIntCast n = (n : OmnificInteger.{u}) from map_intCast _ _]
      exact intCast_mem A n
  · rintro rfl
    refine ⟨omnificIntCast.rangeRestrict.comp omnificConstantCoeff, ?_⟩
    rintro ⟨x, n, rfl⟩
    apply Subtype.ext
    change omnificIntCast (omnificConstantCoeff (omnificIntCast n)) = omnificIntCast n
    rw [omnificConstantCoeff_intCast]

/-- Every real omnific automorphism carries the purely infinite ideal onto itself. -/
theorem omnific_automorphism_map_purelyInfinite
    (σ : OmnificInteger.{u} ≃+* OmnificInteger.{u}) :
    omnificPurelyInfiniteIdeal.map σ.toRingHom = omnificPurelyInfiniteIdeal := by
  conv_lhs => rw [← omnific_endomorphism_comap_purelyInfinite σ.toRingHom]
  exact Ideal.map_comap_of_surjective _ σ.surjective _

end Surreal.Foundations.SignSequence

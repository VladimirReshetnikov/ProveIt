import Surreal.Foundations.OmnificSmallQuotients

/-!
# Explicit ordinal families of distinct omnific residues

The full actual-surreal assertion `osq:thm:idealsize`. Whenever an ideal
misses a purely infinite element, it misses a positive monomial. The
literal ordinal scales c/omega^(alpha+1) then give pairwise distinct
residues. Each restriction to a small ordinal is a small family; the
argument uses only finite telescope certificates inside the source ring.
-/

universe u v
namespace Surreal.Foundations.SignSequence
noncomputable section

/-- An ideal missing a monomial cannot contain a difference between two smaller subordinate monomials. -/
theorem omnific_monomial_difference_not_mem (I : Ideal OmnificInteger.{u})
    (c : SignSequence.{u}) (hc : 0 < c) (hI : omnificMonomial c hc ∉ I)
    (a b : SignSequence.{u}) (hb : 0 < b) (hba : b < a)
    (hac : ∀ n : ℕ, (n : SignSequence) * a < c) :
    omnificMonomial a (hb.trans hba) - omnificMonomial b hb ∉ I := by
  intro hmem
  obtain ⟨q, _, he⟩ := omnific_monomial_difference_certificate c a b hb hba hac
  exact hI (he ▸ I.mul_mem_right q hmem)

/-- The manuscript's ordinal-indexed monomials remain pairwise distinct modulo the ideal. -/
theorem omnific_quotient_ordinal_monomials_injective (I : Ideal OmnificInteger.{u})
    (c : SignSequence.{u}) (hc : 0 < c) (hI : omnificMonomial c hc ∉ I) :
    Function.Injective (fun a : Ordinal.{u} => Ideal.Quotient.mk I
      (omnificMonomial (ordinalScale c a) (ordinalScale_pos c hc a))) := by
  have hsep (a b : Ordinal.{u}) (hab : a < b) :
      Ideal.Quotient.mk I (omnificMonomial (ordinalScale c a) (ordinalScale_pos c hc a)) ≠
        Ideal.Quotient.mk I (omnificMonomial (ordinalScale c b) (ordinalScale_pos c hc b)) := by
    intro he
    apply omnific_monomial_difference_not_mem I c hc hI
      (ordinalScale c a) (ordinalScale c b) (ordinalScale_pos c hc b)
      (ordinalScale_strictAnti c hc hab) (nat_mul_ordinalScale_lt c hc a)
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, he, sub_self]
  intro a b he
  rcases lt_trichotomy a b with hab | hab | hab
  · exact False.elim (hsep a b hab he)
  · exact hab
  · exact False.elim (hsep b a hab he.symm)

/-- Any ideal not containing Pi misses some positive monomial. -/
theorem omnific_exists_monomial_not_mem (I : Ideal OmnificInteger.{u})
    (hI : ¬ omnificPurelyInfiniteIdeal ≤ I) :
    ∃ (c : SignSequence.{u}) (hc : 0 < c), omnificMonomial c hc ∉ I := by
  have hn : ¬ (omnificPurelyInfiniteIdeal : Set OmnificInteger.{u}) ⊆ I := hI
  obtain ⟨x, hx, hnot⟩ := Set.not_subset.mp hn
  obtain ⟨c, hc, hd⟩ := omnific_common_monomial_divisor (fun _ : PUnit => x) (fun _ => hx)
  obtain ⟨q, _, he⟩ := hd PUnit.unit
  exact ⟨c, hc, fun hm => hnot (he ▸ I.mul_mem_right q hm)⟩

/-- A single explicit monomial scale supplies distinct residues for every ordinal index. -/
theorem omnific_quotient_size_alternative (I : Ideal OmnificInteger.{u})
    (hI : ¬ omnificPurelyInfiniteIdeal ≤ I) :
    ∃ (c : SignSequence.{u}) (hc : 0 < c), Function.Injective
      (fun a : Ordinal.{u} => Ideal.Quotient.mk I
        (omnificMonomial (ordinalScale c a) (ordinalScale_pos c hc a))) := by
  obtain ⟨c, hc, hn⟩ := omnific_exists_monomial_not_mem I hI
  exact ⟨c, hc, omnific_quotient_ordinal_monomials_injective I c hc hn⟩

/-- Restricting the explicit family gives pairwise distinct residues indexed by any small ordinal. -/
theorem omnific_quotient_size_alternative_small_family (I : Ideal OmnificInteger.{u})
    (hI : ¬ omnificPurelyInfiniteIdeal ≤ I) (κ : Ordinal.{u}) :
    ∃ f : Set.Iio κ → OmnificInteger.{u} ⧸ I, Function.Injective f := by
  obtain ⟨c, hc, hi⟩ := omnific_quotient_size_alternative I hI
  exact ⟨fun a => Ideal.Quotient.mk I
    (omnificMonomial (ordinalScale c a.val) (ordinalScale_pos c hc a.val)),
    hi.comp Subtype.val_injective⟩

/-- Every small index type is represented by pairwise incongruent actual omnific elements. -/
theorem omnific_quotient_arbitrary_small_family (I : Ideal OmnificInteger.{u})
    (hI : ¬ omnificPurelyInfiniteIdeal ≤ I) (ι : Type v) [Small.{u} ι] :
    ∃ f : ι → OmnificInteger.{u}, Function.Injective (fun i => Ideal.Quotient.mk I (f i)) := by
  obtain ⟨c, hc, hi⟩ := omnific_quotient_size_alternative I hI
  let o : ι → Ordinal.{u} := fun i =>
    Ordinal.typein (@WellOrderingRel (Shrink.{u} ι)) (equivShrink ι i)
  have ho : Function.Injective o :=
    (Ordinal.typein_injective _).comp (equivShrink ι).injective
  exact ⟨fun i => omnificMonomial (ordinalScale c (o i)) (ordinalScale_pos c hc (o i)), hi.comp ho⟩

end
end Surreal.Foundations.SignSequence

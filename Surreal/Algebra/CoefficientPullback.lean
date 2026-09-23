import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Restricting the coefficients of a split ring retraction

The algebraic pullback behind the omnific constant-term map in
`odg:prop:ring`: restrict a ring retraction to elements whose coefficient
lies in an embedded subring. The restricted map retracts onto that subring,
and its quotient by the kernel is exactly the coefficient ring.
-/

namespace Surreal.CoefficientPullback

noncomputable section

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]

/-- Pull back the range of the coefficient embedding along the given retraction. -/
def subring (f : A →+* B) (i : C →+* B) : Subring A := i.range.comap f

/-- Identify an injectively embedded coefficient ring with its image. -/
def rangeEquiv (i : C →+* B) (hi : Function.Injective i) : C ≃+* i.range :=
  RingEquiv.ofBijective i.rangeRestrict
    ⟨fun _ _ h => hi (congrArg Subtype.val h), i.rangeRestrict_surjective⟩

/-- The coefficient map on the pullback, with values in the original coefficient ring. -/
def retraction (f : A →+* B) (i : C →+* B) (hi : Function.Injective i) :
    subring f i →+* C :=
  (rangeEquiv i hi).symm.toRingHom.comp
    ((f.comp (subring f i).subtype).codRestrict i.range (fun x => x.property))

/-- Embedding the extracted coefficient back into the larger coefficient ring recovers `f`. -/
@[simp] theorem embedding_retraction (f : A →+* B) (i : C →+* B)
    (hi : Function.Injective i) (x : subring f i) : i (retraction f i hi x) = f x.val := by
  have h := (rangeEquiv i hi).apply_symm_apply
    (⟨f x.val, x.property⟩ : i.range)
  exact congrArg Subtype.val h

/-- A section of the larger retraction restricts to a section on the pullback. -/
def sectionMap (f : A →+* B) (i : C →+* B) (s : B →+* A)
    (hs : ∀ b, f (s b) = b) : C →+* subring f i :=
  (s.comp i).codRestrict (subring f i) (fun c => ⟨c, (hs (i c)).symm⟩)

@[simp] theorem retraction_sectionMap (f : A →+* B) (i : C →+* B)
    (hi : Function.Injective i) (s : B →+* A) (hs : ∀ b, f (s b) = b) (c : C) :
    retraction f i hi (sectionMap f i s hs c) = c := by
  apply hi
  rw [embedding_retraction]
  exact hs (i c)

/-- The restricted retraction is surjective. -/
theorem retraction_surjective (f : A →+* B) (i : C →+* B)
    (hi : Function.Injective i) (s : B →+* A) (hs : ∀ b, f (s b) = b) :
    Function.Surjective (retraction f i hi) :=
  fun c => ⟨sectionMap f i s hs c, retraction_sectionMap f i hi s hs c⟩

/-- The kernel is precisely the vanishing of the original coefficient. -/
theorem mem_ker_iff (f : A →+* B) (i : C →+* B)
    (hi : Function.Injective i) (x : subring f i) :
    x ∈ RingHom.ker (retraction f i hi) ↔ f x.val = 0 := by
  change retraction f i hi x = 0 ↔ _
  rw [← hi.eq_iff, map_zero, embedding_retraction]

/-- The quotient of the pullback by its retraction kernel is the smaller coefficient ring. -/
def quotientEquiv (f : A →+* B) (i : C →+* B)
    (hi : Function.Injective i) (s : B →+* A) (hs : ∀ b, f (s b) = b) :
    (subring f i) ⧸ RingHom.ker (retraction f i hi) ≃+* C :=
  (retraction f i hi).quotientKerEquivOfSurjective (retraction_surjective f i hi s hs)

end
end Surreal.CoefficientPullback

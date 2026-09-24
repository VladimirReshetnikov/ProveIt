import Mathlib.RingTheory.HahnSeries.Multiplication
import Mathlib.Algebra.MonoidAlgebra.Lift

/-!
# Finite Hahn series as an additive monoid algebra

The native finitely supported coefficient representation embeds as a ring
homomorphism into Hahn series. Its image is exactly the Hahn series with
finite support. This supplies the finite arithmetic bridge used in
`found:thm:workspace`; evaluating finite monomial expressions into another
field is separate from constructing an infinite Hahn evaluation map.
-/

namespace Surreal.HahnSeries

open _root_.HahnSeries

noncomputable section

variable {Γ R : Type*} [AddCommMonoid Γ] [PartialOrder Γ]
  [IsOrderedCancelAddMonoid Γ] [CommSemiring R]

private def finiteSupportMonomialHom : Multiplicative Γ →* R⟦Γ⟧ where
  toFun g := single g.toAdd 1
  map_one' := single_zero_one
  map_mul' g h := by
    change single (g.toAdd + h.toAdd) 1 = single g.toAdd 1 * single h.toAdd 1
    rw [single_mul_single, one_mul]

/-- The additive monoid algebra embeds into Hahn series by its finite coefficients. -/
def finiteSupportEmbedding : AddMonoidAlgebra R Γ →+* R⟦Γ⟧ :=
  AddMonoidAlgebra.liftNCRingHom _root_.HahnSeries.C finiteSupportMonomialHom
    (fun _ _ => Commute.all _ _)

@[simp] theorem finiteSupportEmbedding_single (g : Γ) (r : R) :
    finiteSupportEmbedding (AddMonoidAlgebra.single g r) = single g r := by
  rw [finiteSupportEmbedding, AddMonoidAlgebra.liftNCRingHom_single]
  change single 0 r * single g 1 = single g r
  rw [single_mul_single, zero_add, mul_one]

/-- Every coefficient is preserved exactly by the finite-support embedding. -/
@[simp] theorem coeff_finiteSupportEmbedding (F : AddMonoidAlgebra R Γ) (g : Γ) :
    (finiteSupportEmbedding F).coeff g = F.coeff g := by
  classical
  induction F using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add F G hF hG =>
    simp only [map_add, HahnSeries.coeff_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hF, hG]
  | single h r =>
    rw [finiteSupportEmbedding_single]
    by_cases hh : h = g
    · subst h
      simp
    · simp [Ne.symm hh]

/-- The ring embedding has exactly Mathlib's underlying `ofFinsupp` value. -/
theorem finiteSupportEmbedding_eq_ofFinsupp (F : AddMonoidAlgebra R Γ) :
    finiteSupportEmbedding F = ofFinsupp F.coeff := by
  ext g
  rw [coeff_finiteSupportEmbedding, coeff_ofFinsupp]

theorem finiteSupportEmbedding_injective :
    Function.Injective (finiteSupportEmbedding : AddMonoidAlgebra R Γ → R⟦Γ⟧) := by
  intro F G h
  apply AddMonoidAlgebra.coeff_injective
  ext g
  simpa only [coeff_finiteSupportEmbedding] using congrArg (fun x : R⟦Γ⟧ => x.coeff g) h

/-- The finite support is the actual support of the coefficient function. -/
theorem support_finiteSupportEmbedding (F : AddMonoidAlgebra R Γ) :
    (finiteSupportEmbedding F).support = (F.coeff.support : Set Γ) := by
  ext g
  simp only [mem_support, coeff_finiteSupportEmbedding, Finset.mem_coe, Finsupp.mem_support_iff]

theorem finite_support_finiteSupportEmbedding (F : AddMonoidAlgebra R Γ) :
    (finiteSupportEmbedding F).support.Finite := by
  rw [support_finiteSupportEmbedding]
  exact F.coeff.support.finite_toSet

/-- Recover the finite coefficient expression from a Hahn series of finite support. -/
def finiteSupportRepresentation (x : R⟦Γ⟧) (hx : x.support.Finite) : AddMonoidAlgebra R Γ :=
  AddMonoidAlgebra.ofCoeff (Finsupp.ofSupportFinite x.coeff hx)

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
@[simp] theorem finiteSupportRepresentation_coeff (x : R⟦Γ⟧) (hx : x.support.Finite) (g : Γ) :
    (finiteSupportRepresentation x hx).coeff g = x.coeff g := rfl

@[simp] theorem finiteSupportEmbedding_representation (x : R⟦Γ⟧) (hx : x.support.Finite) :
    finiteSupportEmbedding (finiteSupportRepresentation x hx) = x := by
  ext g
  rw [coeff_finiteSupportEmbedding, finiteSupportRepresentation_coeff]

/-- Exactly the finite-support Hahn series lie in the image of the monoid algebra. -/
theorem mem_range_finiteSupportEmbedding (x : R⟦Γ⟧) :
    x ∈ Set.range (finiteSupportEmbedding : AddMonoidAlgebra R Γ → R⟦Γ⟧) ↔ x.support.Finite := by
  constructor
  · rintro ⟨F, rfl⟩
    exact finite_support_finiteSupportEmbedding F
  · intro hx
    exact ⟨finiteSupportRepresentation x hx, finiteSupportEmbedding_representation x hx⟩

/-- The finite coefficient expression is unique, independently of its presentation. -/
theorem existsUnique_finiteSupport_preimage (x : R⟦Γ⟧) (hx : x.support.Finite) :
    ∃! F : AddMonoidAlgebra R Γ, finiteSupportEmbedding F = x := by
  refine ⟨finiteSupportRepresentation x hx, finiteSupportEmbedding_representation x hx, ?_⟩
  intro F hF
  apply finiteSupportEmbedding_injective
  rw [hF, finiteSupportEmbedding_representation]

end

end Surreal.HahnSeries

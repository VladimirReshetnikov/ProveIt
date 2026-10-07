import OAI.Combinatorics.Progressions.Geometry.CoefficientAmbientCoordinates

namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {K : Type*} {m : ℕ} {J : Fin m → Type*}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

noncomputable def coefficientAmbientHom :
    CoefficientTorus (K := K) U →+ (CoefficientAmbientIndex K J → UnitAddCircle) where
  toFun := coefficientAmbientTorus U
  map_zero' := by
    funext t
    simp [coefficientAmbientTorus]
  map_add' x y := by
    funext t
    simp [coefficientAmbientTorus, map_add]

theorem coefficientAmbientTorus_injective :
    Function.Injective (coefficientAmbientTorus (K := K) U) := by
  intro x y h
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective (coefficientIntegerLattice U) x
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk'_surjective (coefficientIntegerLattice U) y
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  intro s i
  have he : ((a s).val i : UnitAddCircle) = ((b s).val i : UnitAddCircle) := congrFun h ⟨s, i⟩
  have hz : (((a s).val i - (b s).val i : ℝ) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_sub, he, sub_self]
  obtain ⟨z, hz⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hz
  exact ⟨z, by simpa using hz.symm⟩

variable [Fintype K] [∀ j, Fintype (J j)]

theorem coefficientCoverKernel_finite (d : ℕ) (hd : 0 < d) :
    Finite (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d).ker := by
  let T := {z : UnitAddCircle // d • z = 0}
  let : Fintype T := (AddCircle.finite_torsion (1 : ℝ) hd).fintype
  let f : (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d).ker →
      CoefficientAmbientIndex K J → T := fun x i =>
    ⟨coefficientAmbientHom U x.val i, by
      change (d • coefficientAmbientHom U x.val) i = 0
      rw [← map_nsmul]
      have hx : d • x.val = 0 := x.property
      rw [hx, map_zero]
      rfl⟩
  apply Finite.of_injective f
  intro x y hxy
  apply Subtype.ext
  apply coefficientAmbientTorus_injective U
  funext i
  exact congrArg Subtype.val (congrFun hxy i)

@[instance_reducible]
noncomputable def coefficientCoverKernelFintype (d : ℕ) (hd : 0 < d) :
    Fintype (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d).ker := by
  let : Finite (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d).ker :=
    coefficientCoverKernel_finite U d hd
  exact Fintype.ofFinite _

end Erdos3.VectorPolynomial

end

end OAI

import Mathlib.LinearAlgebra.StdBasis

namespace OAI

section

namespace Erdos3

open Module

variable {R T : Type*} [Semiring R] {J I : T → Type*}

def taggedSubmodule (U : ∀ t, Submodule R (J t → R)) : Submodule R ((Σ t, J t) → R) where
  carrier := {x | ∀ t, (fun j => x ⟨t, j⟩) ∈ U t}
  zero_mem' := fun t => (U t).zero_mem
  add_mem' := fun hx hy t => (U t).add_mem (hx t) (hy t)
  smul_mem' := fun c _ hx t => (U t).smul_mem c (hx t)

@[simp]
theorem mem_taggedSubmodule (U : ∀ t, Submodule R (J t → R)) (x : (Σ t, J t) → R) :
    x ∈ taggedSubmodule U ↔ ∀ t, (fun j => x ⟨t, j⟩) ∈ U t := Iff.rfl

def taggedSubmoduleEquiv (U : ∀ t, Submodule R (J t → R)) :
    (∀ t, U t) ≃ₗ[R] taggedSubmodule U where
  toFun x := ⟨fun j => (x j.1 : J j.1 → R) j.2, fun t => (x t).property⟩
  invFun x := fun t => ⟨fun j => (x : (Σ t, J t) → R) ⟨t, j⟩, x.property t⟩
  left_inv x := by
    funext t
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    funext j
    rfl
  map_add' x y := rfl
  map_smul' c x := rfl

@[simp]
theorem taggedSubmoduleEquiv_apply (U : ∀ t, Submodule R (J t → R))
    (x : ∀ t, U t) (t : T) (j : J t) :
    (taggedSubmoduleEquiv U x : (Σ t, J t) → R) ⟨t, j⟩ = (x t : J t → R) j := rfl

@[simp]
theorem taggedSubmoduleEquiv_symm_apply (U : ∀ t, Submodule R (J t → R))
    (x : taggedSubmodule U) (t : T) (j : J t) :
    ((taggedSubmoduleEquiv U).symm x t : J t → R) j =
      (x : (Σ t, J t) → R) ⟨t, j⟩ := rfl

variable [Fintype T]

noncomputable def taggedSubmoduleBasis (U : ∀ t, Submodule R (J t → R))
    (b : ∀ t, Basis (I t) R (U t)) : Basis (Σ t, I t) R (taggedSubmodule U) :=
  (Pi.basis b).map (taggedSubmoduleEquiv U)

theorem taggedSubmoduleBasis_apply [DecidableEq T]
    (U : ∀ t, Submodule R (J t → R)) (b : ∀ t, Basis (I t) R (U t))
    (t : T) (i : I t) (t' : T) (j : J t') :
    (taggedSubmoduleBasis U b ⟨t, i⟩ : (Σ t, J t) → R) ⟨t', j⟩ =
      ((Pi.single (M := fun t => U t) t (b t i) t' : U t') : J t' → R) j := by
  rw [taggedSubmoduleBasis, Basis.map_apply, Pi.basis_apply]
  rfl

@[simp]
theorem taggedSubmoduleBasis_same
    (U : ∀ t, Submodule R (J t → R)) (b : ∀ t, Basis (I t) R (U t))
    (t : T) (i : I t) (j : J t) :
    (taggedSubmoduleBasis U b ⟨t, i⟩ : (Σ t, J t) → R) ⟨t, j⟩ = (b t i : J t → R) j := by
  classical
  rw [taggedSubmoduleBasis_apply, Pi.single_eq_same]

theorem taggedSubmoduleBasis_of_ne
    (U : ∀ t, Submodule R (J t → R)) (b : ∀ t, Basis (I t) R (U t))
    (t : T) (i : I t) (t' : T) (j : J t') (h : t' ≠ t) :
    (taggedSubmoduleBasis U b ⟨t, i⟩ : (Σ t, J t) → R) ⟨t', j⟩ = 0 := by
  classical
  rw [taggedSubmoduleBasis_apply, Pi.single_eq_of_ne h]
  rfl

theorem taggedSubmoduleBasis_repr
    (U : ∀ t, Submodule R (J t → R)) (b : ∀ t, Basis (I t) R (U t))
    (x : taggedSubmodule U) (t : T) (i : I t) :
    (taggedSubmoduleBasis U b).repr x ⟨t, i⟩ =
      (b t).repr ((taggedSubmoduleEquiv U).symm x t) i := rfl

end Erdos3

end

end OAI

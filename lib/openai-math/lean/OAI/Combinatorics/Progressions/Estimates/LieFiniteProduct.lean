import OAI.Combinatorics.Progressions.Nilpotent.BCHSubgroupGridExistence

namespace OAI

section

namespace Erdos3

open Module

variable {α : Type*} {M : α → Type*} [∀ a, LieRing (M a)]

instance lieRingPi : LieRing (∀ a, M a) where
  bracket x y a := ⁅x a, y a⁆
  add_lie x y z := by funext a; exact add_lie _ _ _
  lie_add x y z := by funext a; exact lie_add _ _ _
  lie_self x := by funext a; exact lie_self _
  leibniz_lie x y z := by funext a; exact leibniz_lie _ _ _

@[simp] theorem lie_pi_apply (x y : ∀ a, M a) (a : α) : ⁅x, y⁆ a = ⁅x a, y a⁆ := rfl

variable {R : Type*} [CommRing R] [∀ a, LieAlgebra R (M a)]

instance lieAlgebraPi : LieAlgebra R (∀ a, M a) where
  lie_smul r x y := by funext a; exact lie_smul _ _ _

def liePiEval (a : α) : (∀ a, M a) →ₗ⁅R⁆ M a where
  toLinearMap := LinearMap.proj a
  map_lie' := rfl

@[simp] theorem liePiEval_apply (a : α) (x : ∀ a, M a) : liePiEval (R := R) a x = x a := rfl

variable {L : Type*} [LieRing L] [LieAlgebra R L]

def liePiMap (φ : ∀ a, L →ₗ⁅R⁆ M a) : L →ₗ⁅R⁆ (∀ a, M a) where
  toLinearMap := LinearMap.pi (fun a => (φ a).toLinearMap)
  map_lie' {x y} := by funext a; exact (φ a).map_lie x y

@[simp] theorem liePiMap_apply (φ : ∀ a, L →ₗ⁅R⁆ M a) (x : L) (a : α) :
    liePiMap φ x a = φ a x := rfl

theorem liePiEval_comp_liePiMap (φ : ∀ a, L →ₗ⁅R⁆ M a) (a : α) :
    (liePiEval a).comp (liePiMap φ) = φ a := rfl

namespace NilpotentLieFiltration

variable [∀ a, LieAlgebra ℚ (M a)] {s : ℕ}

def pi (F : ∀ a, NilpotentLieFiltration (M a) s) : NilpotentLieFiltration (∀ a, M a) s where
  layer n := Submodule.pi Set.univ (fun a => (F a).layer n)
  antitone _ _ h := Submodule.pi_mono (fun a _ => (F a).antitone h)
  one_eq_top := by simp only [one_eq_top, Submodule.pi_top]
  lie_mem {i j x y} hx hy a ha := (F a).lie_mem (hx a ha) (hy a ha)
  terminal := by simp only [terminal, Submodule.pi_univ_bot]

@[simp] theorem mem_pi_layer (F : ∀ a, NilpotentLieFiltration (M a) s) (n : ℕ) (x : ∀ a, M a) :
    x ∈ (pi F).layer n ↔ ∀ a, x a ∈ (F a).layer n := by simp [pi, Submodule.mem_pi]

end NilpotentLieFiltration

section Coordinates

variable [Fintype α] {κ : α → Type*} [∀ a, Fintype (κ a)]
  [∀ a, LieAlgebra ℚ (M a)]

omit [∀ a, Fintype (κ a)] in

theorem lie_pi_structure_height (f : ∀ a, Basis (κ a) ℚ (M a)) {H : ℕ} (hH : 1 ≤ H)
    (hf : ∀ a i j k, RationalHeightLE (lieStructureConstants (f a) i j k) H) :
    ∀ i j k, RationalHeightLE (lieStructureConstants (Pi.basis f) i j k) H := by
  classical
  rintro ⟨a, i⟩ ⟨b, j⟩ ⟨c, k⟩
  unfold lieStructureConstants
  rw [Pi.basis_repr, lie_pi_apply, Pi.basis_apply, Pi.basis_apply]
  by_cases hac : a = c
  · subst c
    rw [Pi.single_eq_same]
    by_cases hba : b = a
    · subst b
      rw [Pi.single_eq_same]
      exact hf a i j k
    · rw [Pi.single_eq_of_ne (Ne.symm hba), lie_zero, map_zero, Finsupp.zero_apply]
      exact rationalHeightLE_zero hH
  · rw [Pi.single_eq_of_ne (Ne.symm hac), zero_lie, map_zero, Finsupp.zero_apply]
    exact rationalHeightLE_zero hH

variable [LieAlgebra ℚ L] {ι : Type*} [Fintype ι]

omit [∀ a, Fintype (κ a)] [Fintype ι] in
theorem liePiMap_height (e : Basis ι ℚ L) (f : ∀ a, Basis (κ a) ℚ (M a))
    (φ : ∀ a, L →ₗ⁅ℚ⁆ M a) {H : ℕ}
    (hφ : ∀ a i j, RationalHeightLE ((f a).repr (φ a (e j)) i) H) :
    ∀ i j, RationalHeightLE ((Pi.basis f).repr (liePiMap φ (e j)) i) H := by
  rintro ⟨a, i⟩ j
  exact hφ a i j

end Coordinates
end Erdos3

end

end OAI

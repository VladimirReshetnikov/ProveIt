import Mathlib

namespace OAI

section

namespace Erdos3

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

def fourAlternatingMap : (Fin 4 → V) →ₗ[R] V :=
  (LinearMap.proj 0 : (Fin 4 → V) →ₗ[R] V) + LinearMap.proj 1 - LinearMap.proj 2 - LinearMap.proj 3

theorem fourAlternatingMap_apply (v : Fin 4 → V) :
    fourAlternatingMap (R := R) v = v 0 + v 1 - v 2 - v 3 := rfl

def fourCommonModulo (C D : Submodule R V) : Submodule R (Fin 4 → V) :=
  Submodule.pi Set.univ (fun _ => C) ⊓
    ⨅ k : Fin 4, D.comap ((LinearMap.proj k : (Fin 4 → V) →ₗ[R] V) - LinearMap.proj 0)

theorem mem_fourCommonModulo (C D : Submodule R V) (v : Fin 4 → V) :
    v ∈ fourCommonModulo C D ↔ (∀ k, v k ∈ C) ∧ ∀ k, v k - v 0 ∈ D := by
  simp [fourCommonModulo, Submodule.mem_pi]

def fourBalancedDependent (D : Submodule R V) : Submodule R (Fin 4 → V) :=
  Submodule.pi Set.univ (fun _ => D) ⊓ LinearMap.ker (fourAlternatingMap (R := R))

theorem mem_fourBalancedDependent (D : Submodule R V) (v : Fin 4 → V) :
    v ∈ fourBalancedDependent D ↔ (∀ k, v k ∈ D) ∧ v 0 + v 1 - v 2 - v 3 = 0 := by
  simp [fourBalancedDependent, Submodule.mem_pi, fourAlternatingMap_apply]

theorem fourBalancedDependent_le_common (C D : Submodule R V) (hDC : D ≤ C) :
    fourBalancedDependent D ≤ fourCommonModulo C D := by
  intro v hv
  obtain ⟨hv, _⟩ := (mem_fourBalancedDependent D v).mp hv
  exact (mem_fourCommonModulo C D v).mpr
    ⟨fun k => hDC (hv k), fun k => D.sub_mem (hv k) (hv 0)⟩

def fourRefinedRelation (C D : Submodule R V) (K : Submodule R (Fin 4 → V)) :
    Submodule R (Fin 4 → V) :=
  (K ⊓ fourCommonModulo C D) ⊔ fourBalancedDependent D

theorem fourRefinedRelation_le_common (C D : Submodule R V) (hDC : D ≤ C)
    (K : Submodule R (Fin 4 → V)) : fourRefinedRelation C D K ≤ fourCommonModulo C D :=
  sup_le inf_le_right (fourBalancedDependent_le_common C D hDC)

theorem fourBalancedDependent_le_refined (C D : Submodule R V)
    (K : Submodule R (Fin 4 → V)) : fourBalancedDependent D ≤ fourRefinedRelation C D K :=
  le_sup_right

def fourPetalSpace (D : Submodule R V) (K : Submodule R (Fin 4 → V)) : Submodule R V :=
  D ⊓ K.comap (LinearMap.single R (fun _ : Fin 4 => V) 0)

theorem mem_fourPetalSpace (D : Submodule R V) (K : Submodule R (Fin 4 → V)) (v : V) :
    v ∈ fourPetalSpace D K ↔ v ∈ D ∧ LinearMap.single R (fun _ : Fin 4 => V) 0 v ∈ K := Iff.rfl

theorem fourPetalSpace_le_first (D : Submodule R V) (K : Submodule R (Fin 4 → V)) :
    fourPetalSpace D K ≤ K.map (LinearMap.proj 0) := by
  intro v hv
  exact ⟨LinearMap.single R (fun _ : Fin 4 => V) 0 v, hv.2, by simp [LinearMap.single_apply]⟩

theorem fourAlternatingMap_mem_dependent (C D : Submodule R V) (v : Fin 4 → V)
    (hv : v ∈ fourCommonModulo C D) : fourAlternatingMap (R := R) v ∈ D := by
  have h := (mem_fourCommonModulo C D v).mp hv
  have heq : fourAlternatingMap (R := R) v = (v 1 - v 0) - (v 2 - v 0) - (v 3 - v 0) := by
    rw [fourAlternatingMap_apply]
    abel
  rw [heq]
  exact D.sub_mem (D.sub_mem (h.2 1) (h.2 2)) (h.2 3)

end Erdos3

end

end OAI

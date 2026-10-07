import OAI.Combinatorics.Progressions.Estimates.FourBalancedRelations

namespace OAI

section

namespace Erdos3

variable {R V E : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [AddCommGroup E] [Module R E]

def fourDiagonalMap : V →ₗ[R] (Fin 4 → V) := LinearMap.pi (fun _ => LinearMap.id)

theorem four_annihilator_decomposition (C D : Submodule R V)
    (ℓ : (Fin 4 → V) →ₗ[R] E)
    (hℓ : ∀ z ∈ fourBalancedDependent D, ℓ z = 0)
    (v : Fin 4 → V) (hv : v ∈ fourCommonModulo C D) :
    ℓ v = ℓ (fourDiagonalMap (R := R) (v 0)) +
      ℓ (LinearMap.single R (fun _ : Fin 4 => V) 0 (fourAlternatingMap (R := R) v)) := by
  let a := fourAlternatingMap (R := R) v
  have ha : a ∈ D := fourAlternatingMap_mem_dependent C D v hv
  let z : Fin 4 → V := fun k => v k - v 0 - (Pi.single (0 : Fin 4) a : Fin 4 → V) k
  have hz : z ∈ fourBalancedDependent D := by
    apply (mem_fourBalancedDependent D z).mpr
    refine ⟨?_, ?_⟩
    · intro k
      apply D.sub_mem (((mem_fourCommonModulo C D v).mp hv).2 k)
      by_cases hk : k = 0
      · subst k; simpa only [Pi.single_eq_same] using ha
      · simpa only [Pi.single_eq_of_ne hk] using D.zero_mem
    · change (v 0 - v 0 - a) + (v 1 - v 0 - 0) - (v 2 - v 0 - 0) - (v 3 - v 0 - 0) = 0
      dsimp only [a]
      rw [fourAlternatingMap_apply]
      abel
  have h := hℓ z hz
  change ℓ (v - fourDiagonalMap (R := R) (v 0) -
    LinearMap.single R (fun _ : Fin 4 => V) 0 a) = 0 at h
  rw [map_sub, map_sub] at h
  calc
    ℓ v = (ℓ v - ℓ (fourDiagonalMap (R := R) (v 0))) +
        ℓ (fourDiagonalMap (R := R) (v 0)) := (sub_add_cancel _ _).symm
    _ = ℓ (LinearMap.single R (fun _ : Fin 4 => V) 0 a) +
        ℓ (fourDiagonalMap (R := R) (v 0)) := by rw [sub_eq_zero.mp h]
    _ = _ := add_comm _ _

theorem four_annihilator_common_zero (D : Submodule R V)
    (ℓ : (Fin 4 → V) →ₗ[R] E)
    (hℓ : ∀ z ∈ fourBalancedDependent D, ℓ z = 0) (v : V) (hv : v ∈ D) :
    ℓ (fourDiagonalMap (R := R) v) = 0 := by
  apply hℓ
  apply (mem_fourBalancedDependent D _).mpr
  exact ⟨fun _ => hv, by change v + v - v - v = 0; abel⟩

theorem four_refined_annihilator_identity (C D : Submodule R V) (hDC : D ≤ C)
    (K : Submodule R (Fin 4 → V)) (ℓ : (Fin 4 → V) →ₗ[R] E)
    (hℓ : ∀ z ∈ fourRefinedRelation C D K, ℓ z = 0)
    (v : Fin 4 → V) (hv : v ∈ fourRefinedRelation C D K) :
    ℓ (fourDiagonalMap (R := R) (v 0)) +
      ℓ (LinearMap.single R (fun _ : Fin 4 => V) 0 (v 0 + v 1 - v 2 - v 3)) = 0 := by
  have h := four_annihilator_decomposition C D ℓ
    (fun z hz => hℓ z (fourBalancedDependent_le_refined C D K hz)) v
    (fourRefinedRelation_le_common C D hDC K hv)
  rw [fourAlternatingMap_apply] at h
  exact h.symm.trans (hℓ v hv)

theorem four_refined_annihilator_petal_zero (D : Submodule R V)
    (K : Submodule R (Fin 4 → V)) (ℓ : (Fin 4 → V) →ₗ[R] E)
    (hℓ : ∀ z ∈ K, ℓ z = 0) (v : V) (hv : v ∈ fourPetalSpace D K) :
    ℓ (LinearMap.single R (fun _ : Fin 4 => V) 0 v) = 0 :=
  hℓ _ hv.2

end Erdos3

end

end OAI

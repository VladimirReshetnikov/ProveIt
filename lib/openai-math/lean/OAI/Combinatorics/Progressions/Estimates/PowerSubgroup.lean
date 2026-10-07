import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

variable {G : Type*} [Group G]

def powerSubgroup (G : Type*) [Group G] (m : ℕ) : Subgroup G :=
  Subgroup.closure (Set.range (fun g : G => g ^ m))

theorem pow_mem_powerSubgroup (g : G) (m : ℕ) : g ^ m ∈ powerSubgroup G m :=
  Subgroup.subset_closure ⟨g, rfl⟩

theorem powerSubgroup_map_le (f : G →* G) (m : ℕ) :
    (powerSubgroup G m).map f ≤ powerSubgroup G m := by
  rw [Subgroup.map_le_iff_le_comap]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨g, rfl⟩
  change f (g ^ m) ∈ powerSubgroup G m
  rw [map_pow]
  exact pow_mem_powerSubgroup _ _

instance powerSubgroup_characteristic (m : ℕ) : (powerSubgroup G m).Characteristic :=
  Subgroup.characteristic_iff_map_le.mpr (fun f => powerSubgroup_map_le f.toMonoidHom m)

def subgroupPowerCover (Γ : Subgroup G) (m : ℕ) : Subgroup G :=
  (powerSubgroup Γ m).map Γ.subtype

theorem subgroupPowerCover_le (Γ : Subgroup G) (m : ℕ) : subgroupPowerCover Γ m ≤ Γ := by
  rintro _ ⟨g, _, rfl⟩
  exact g.property

theorem pow_mem_subgroupPowerCover (Γ : Subgroup G) {g : G} (hg : g ∈ Γ) (m : ℕ) :
    g ^ m ∈ subgroupPowerCover Γ m :=
  Subgroup.mem_map.mpr ⟨(⟨g, hg⟩ : Γ) ^ m, pow_mem_powerSubgroup _ _, rfl⟩

theorem subgroupPowerCover_le_iff (Γ Λ : Subgroup G) (m : ℕ) :
    subgroupPowerCover Γ m ≤ Λ ↔ ∀ g ∈ Γ, g ^ m ∈ Λ := by
  constructor
  · intro h g hg
    exact h (pow_mem_subgroupPowerCover Γ hg m)
  · intro h
    apply Subgroup.map_le_iff_le_comap.mpr
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨g, rfl⟩
    exact h g g.property

theorem subgroupPowerCover_subgroupOf (Γ : Subgroup G) (m : ℕ) :
    (subgroupPowerCover Γ m).subgroupOf Γ = powerSubgroup Γ m := by
  change ((powerSubgroup Γ m).map Γ.subtype).comap Γ.subtype = _
  exact Subgroup.comap_map_eq_self_of_injective (f := Γ.subtype) Subtype.val_injective _

instance subgroupPowerCover_characteristic (Γ : Subgroup G) (m : ℕ) :
    ((subgroupPowerCover Γ m).subgroupOf Γ).Characteristic := by
  rw [subgroupPowerCover_subgroupOf]
  infer_instance

instance subgroupPowerCover_normal (Γ : Subgroup G) (m : ℕ) :
    ((subgroupPowerCover Γ m).subgroupOf Γ).Normal := inferInstance

end Erdos3

end

end OAI

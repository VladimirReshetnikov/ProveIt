import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

variable {H G A : Type*} [Group H] [Group G]

theorem factorsThrough_target_cosets (φ : H →* G) (Γ : Subgroup H) (Λ : Subgroup G)
    (hcover : Λ ≤ Γ.map φ) (f : H → A)
    (hker : ∀ k ∈ φ.ker, ∀ x, f (k * x) = f x)
    (hΓ : ∀ γ ∈ Γ, ∀ x, f (x * γ) = f x) :
    Function.FactorsThrough f (fun x => (QuotientGroup.mk (φ x) : G ⧸ Λ)) := by
  intro x y hxy
  have hmem : (φ x)⁻¹ * φ y ∈ Λ := QuotientGroup.eq.mp hxy
  obtain ⟨γ, hγ, hφγ⟩ := hcover hmem
  let k := y * γ⁻¹ * x⁻¹
  have hk : k ∈ φ.ker := by
    change φ k = 1
    simp only [k, map_mul, map_inv, hφγ, mul_inv_rev, inv_inv]
    group
  have hdecomp : k * (x * γ) = y := by
    dsimp [k]
    group
  calc
    f x = f (x * γ) := (hΓ γ hγ x).symm
    _ = f (k * (x * γ)) := (hker k hk (x * γ)).symm
    _ = f y := congrArg f hdecomp

theorem exists_unique_quotient_reconstruction (φ : H →* G) (hφ : Function.Surjective φ)
    (Γ : Subgroup H) (Λ : Subgroup G) (hcover : Λ ≤ Γ.map φ) (f : H → A)
    (hker : ∀ k ∈ φ.ker, ∀ x, f (k * x) = f x)
    (hΓ : ∀ γ ∈ Γ, ∀ x, f (x * γ) = f x) :
    ∃! F : G ⧸ Λ → A, ∀ x, F (QuotientGroup.mk (φ x)) = f x := by
  let π : H → G ⧸ Λ := fun x => QuotientGroup.mk (φ x)
  have hπ : Function.Surjective π := QuotientGroup.mk_surjective.comp hφ
  have hf := factorsThrough_target_cosets φ Γ Λ hcover f hker hΓ
  let F : G ⧸ Λ → A := fun y => f (Function.surjInv hπ y)
  have hF (x : H) : F (π x) = f x := hf (Function.surjInv_eq hπ (π x))
  refine ⟨F, hF, ?_⟩
  intro F' hF'
  funext y
  obtain ⟨x, rfl⟩ := hπ y
  exact (hF' x).trans (hF x).symm

theorem exists_unique_observable_reconstruction (φ : H →* G) (hφ : Function.Surjective φ)
    (Γ : Subgroup H) (Λ : Subgroup G) (hcover : Λ ≤ Γ.map φ) (f : H ⧸ Γ → A)
    (hker : ∀ k ∈ φ.ker, ∀ x, f (QuotientGroup.mk (k * x)) = f (QuotientGroup.mk x)) :
    ∃! F : G ⧸ Λ → A, ∀ x, F (QuotientGroup.mk (φ x)) = f (QuotientGroup.mk x) := by
  apply exists_unique_quotient_reconstruction φ hφ Γ Λ hcover (fun x => f (QuotientGroup.mk x)) hker
  intro γ hγ x
  apply congrArg f
  apply QuotientGroup.eq.mpr
  simpa only [mul_inv_rev, inv_mul_cancel_left, inv_mul_cancel_right] using Γ.inv_mem hγ

theorem exists_unique_image_reconstruction (φ : H →* G)
    (Γ : Subgroup H) (Λ : Subgroup G) (hcover : Λ ⊓ φ.range ≤ Γ.map φ)
    (f : H ⧸ Γ → A)
    (hker : ∀ k ∈ φ.ker, ∀ x, f (QuotientGroup.mk (k * x)) = f (QuotientGroup.mk x)) :
    ∃! F : φ.range ⧸ Λ.subgroupOf φ.range → A,
      ∀ x, F (QuotientGroup.mk (φ.rangeRestrict x)) = f (QuotientGroup.mk x) := by
  apply exists_unique_observable_reconstruction φ.rangeRestrict φ.rangeRestrict_surjective
    Γ (Λ.subgroupOf φ.range)
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := hcover ⟨hy, y.property⟩
    exact ⟨x, hx, Subtype.ext hxy⟩
  · intro k hk x
    apply hker k _ x
    change φ k = 1
    exact congrArg Subtype.val (show φ.rangeRestrict k = 1 from hk)

end Erdos3

end

section

namespace Erdos3

variable {H G A : Type*} [Group H] [Group G]

def CosetImage (φ : H →* G) (Λ : Subgroup G) :=
  Set.range (fun x : H => (QuotientGroup.mk (φ x) : G ⧸ Λ))

def projectToCosetImage (φ : H →* G) (Λ : Subgroup G) (x : H) : CosetImage φ Λ :=
  ⟨QuotientGroup.mk (φ x), ⟨x, rfl⟩⟩

theorem projectToCosetImage_surjective (φ : H →* G) (Λ : Subgroup G) :
    Function.Surjective (projectToCosetImage φ Λ) := by
  rintro ⟨y, x, rfl⟩
  exact ⟨x, rfl⟩

theorem factorsThrough_image_cosets (φ : H →* G) (Γ : Subgroup H) (Λ : Subgroup G)
    (hcover : Λ ⊓ φ.range ≤ Γ.map φ) (f : H → A)
    (hker : ∀ k ∈ φ.ker, ∀ x, f (k * x) = f x)
    (hΓ : ∀ γ ∈ Γ, ∀ x, f (x * γ) = f x) :
    Function.FactorsThrough f (projectToCosetImage φ Λ) := by
  intro x y hxy
  have hmem : (φ x)⁻¹ * φ y ∈ Λ := QuotientGroup.eq.mp (congrArg Subtype.val hxy)
  have hrange : (φ x)⁻¹ * φ y ∈ φ.range := ⟨x⁻¹ * y, by simp only [map_mul, map_inv]⟩
  obtain ⟨γ, hγ, hφγ⟩ := hcover ⟨hmem, hrange⟩
  let k := y * γ⁻¹ * x⁻¹
  have hk : k ∈ φ.ker := by
    change φ k = 1
    simp only [k, map_mul, map_inv, hφγ, mul_inv_rev, inv_inv]
    group
  have hdecomp : k * (x * γ) = y := by dsimp [k]; group
  calc
    f x = f (x * γ) := (hΓ γ hγ x).symm
    _ = f (k * (x * γ)) := (hker k hk (x * γ)).symm
    _ = f y := congrArg f hdecomp

theorem exists_unique_cosetImage_reconstruction (φ : H →* G) (Γ : Subgroup H) (Λ : Subgroup G)
    (hcover : Λ ⊓ φ.range ≤ Γ.map φ) (f : H → A)
    (hker : ∀ k ∈ φ.ker, ∀ x, f (k * x) = f x)
    (hΓ : ∀ γ ∈ Γ, ∀ x, f (x * γ) = f x) :
    ∃! F : CosetImage φ Λ → A, ∀ x, F (projectToCosetImage φ Λ x) = f x := by
  let π := projectToCosetImage φ Λ
  have hπ := projectToCosetImage_surjective φ Λ
  have hf := factorsThrough_image_cosets φ Γ Λ hcover f hker hΓ
  let F : CosetImage φ Λ → A := fun y => f (Function.surjInv hπ y)
  have hF (x : H) : F (π x) = f x := hf (Function.surjInv_eq hπ (π x))
  refine ⟨F, hF, ?_⟩
  intro F' hF'
  funext y
  obtain ⟨x, rfl⟩ := hπ y
  exact (hF' x).trans (hF x).symm

end Erdos3

end

end OAI

import Mathlib.Data.Set.Prod
import Mathlib.GroupTheory.QuotientGroup.Basic

namespace OAI

section

namespace Erdos3

variable {G H X : Type*} [AddCommGroup G] [AddCommGroup H]
variable (C : G →+ H) (s : X → G) (q : X → H)

theorem kernelLiftChart_injOn (hproj : ∀ x, C (s x) = q x)
    {S : Set X} (hq : Set.InjOn q S) :
    Set.InjOn (fun p : X × C.ker => s p.1 + p.2.val) (S ×ˢ Set.univ) := by
  intro x hx y hy he
  change s x.1 + x.2.val = s y.1 + y.2.val at he
  have hkx : C x.2.val = 0 := x.2.property
  have hky : C y.2.val = 0 := y.2.property
  have hb : q x.1 = q y.1 := by
    have ht := congrArg C he
    simpa only [map_add, hproj, hkx, hky, add_zero] using ht
  have hxy : x.1 = y.1 := hq hx.1 hy.1 hb
  apply Prod.ext hxy
  apply Subtype.ext
  rw [hxy] at he
  exact add_left_cancel he

theorem kernelLiftChart_image (hproj : ∀ x, C (s x) = q x) (S : Set X) :
    (fun p : X × C.ker => s p.1 + p.2.val) '' (S ×ˢ Set.univ) = C ⁻¹' (q '' S) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.1, hx.1, ?_⟩
    have hk : C x.2.val = 0 := x.2.property
    simp only [map_add, hproj, hk, add_zero]
  · rintro ⟨x, hx, hxy⟩
    have hk : y - s x ∈ C.ker := by
      change C (y - s x) = 0
      rw [map_sub, hproj, ← hxy, sub_self]
    refine ⟨(x, ⟨y - s x, hk⟩), ⟨hx, Set.mem_univ _⟩, ?_⟩
    change s x + (y - s x) = y
    rw [← add_sub_assoc, add_sub_cancel_left]

theorem kernelLiftChart_relabel_injOn {R : Type*} (e : R ≃ C.ker)
    (hproj : ∀ x, C (s x) = q x) {S : Set X} (hq : Set.InjOn q S) :
    Set.InjOn (fun p : X × R => s p.1 + (e p.2).val) (S ×ˢ Set.univ) := by
  intro x hx y hy he
  have hp := kernelLiftChart_injOn C s q hproj hq
    (show (x.1, e x.2) ∈ S ×ˢ Set.univ from ⟨hx.1, Set.mem_univ _⟩)
    (show (y.1, e y.2) ∈ S ×ˢ Set.univ from ⟨hy.1, Set.mem_univ _⟩) he
  exact Prod.ext (congrArg (fun z : X × C.ker => z.1) hp)
    (e.injective (congrArg (fun z : X × C.ker => z.2) hp))

theorem kernelLiftChart_relabel_image {R : Type*} (e : R ≃ C.ker)
    (hproj : ∀ x, C (s x) = q x) (S : Set X) :
    (fun p : X × R => s p.1 + (e p.2).val) '' (S ×ˢ Set.univ) = C ⁻¹' (q '' S) := by
  rw [← kernelLiftChart_image C s q hproj S]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(x.1, e x.2), ⟨hx.1, Set.mem_univ _⟩, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(x.1, e.symm x.2), ⟨hx.1, Set.mem_univ _⟩, by simp only [e.apply_symm_apply]⟩

end Erdos3

end

end OAI

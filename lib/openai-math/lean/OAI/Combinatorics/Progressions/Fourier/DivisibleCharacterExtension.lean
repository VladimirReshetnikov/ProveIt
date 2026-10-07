import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Topology.Instances.AddCircle.Real

namespace OAI

section

namespace Erdos3

theorem exists_divisible_character_extension
    {A G Q : Type} [AddCommGroup A] [AddCommGroup G] [AddCommGroup Q]
    [DivisibleBy Q ℤ] (η : A →+ G) (φ : A →+ Q)
    (hker : ∀ x, η x = 0 → φ x = 0) :
    ∃ θ : G →+ Q, ∀ x, θ (η x) = φ x := by
  let : Module.Injective ℤ Q := (Module.Baer.of_divisible Q).injective
  let f := (QuotientAddGroup.kerLift η).toIntLinearMap
  let g := (QuotientAddGroup.lift η.ker φ (fun x hx => hker x hx)).toIntLinearMap
  obtain ⟨θ, hθ⟩ := Module.Injective.out f (QuotientAddGroup.kerLift_injective η) g
  exact ⟨θ.toAddMonoidHom, fun x => hθ (QuotientAddGroup.mk x)⟩

theorem exists_cyclic_torus_character
    {A : Type} [AddCommGroup A] {N : ℕ} [NeZero N]
    (η : A →+ ZMod N) (φ : A →+ AddCircle (1 : ℝ))
    (hker : ∀ x, η x = 0 → φ x = 0) :
    ∃ θ : AddCircle (1 : ℝ), N • θ = 0 ∧ ∀ x, φ x = (η x).val • θ := by
  obtain ⟨χ, hχ⟩ := exists_divisible_character_extension η φ hker
  refine ⟨χ 1, ?_, fun x => ?_⟩
  · rw [← map_nsmul]
    simp [nsmul_eq_mul]
  · rw [← hχ x, ← map_nsmul]
    congr 1
    simp

theorem exists_cyclic_real_character
    {A : Type} [AddCommGroup A] {N : ℕ} [NeZero N]
    (η : A →+ ZMod N) (φ : A →+ AddCircle (1 : ℝ))
    (hker : ∀ x, η x = 0 → φ x = 0) :
    ∃ t ∈ Set.Ico (0 : ℝ) 1,
      (∃ k : ℤ, (N : ℝ) * t = (k : ℝ)) ∧
      ∀ x, φ x = ((((η x).val : ℝ) * t : ℝ) : AddCircle (1 : ℝ)) := by
  obtain ⟨θ, hN, hθ⟩ := exists_cyclic_torus_character η φ hker
  obtain ⟨t, ht, he⟩ := AddCircle.eq_coe_Ico θ
  refine ⟨t, ht, ?_, fun x => ?_⟩
  · rw [← he, ← AddCircle.coe_nsmul, AddCircle.coe_eq_zero_iff] at hN
    obtain ⟨k, hk⟩ := hN
    exact ⟨k, by simpa [nsmul_eq_mul] using hk.symm⟩
  · rw [hθ, ← he, ← AddCircle.coe_nsmul]
    congr 1
    simp [nsmul_eq_mul]

theorem exists_cyclic_real_character_lift
    {A : Type} [AddCommGroup A] {N : ℕ} [NeZero N]
    (η : A →+ ZMod N) (φ : A →+ AddCircle (1 : ℝ))
    (hker : ∀ x, η x = 0 → φ x = 0) :
    ∃ t ∈ Set.Ico (0 : ℝ) 1,
      (∃ k : ℤ, (N : ℝ) * t = (k : ℝ)) ∧
      ∀ (x : A) (n : ℤ), η x = (n : ZMod N) →
        φ x = (((n : ℝ) * t : ℝ) : AddCircle (1 : ℝ)) := by
  obtain ⟨χ, hχ⟩ := exists_divisible_character_extension η φ hker
  obtain ⟨t, ht, he⟩ := AddCircle.eq_coe_Ico (χ 1)
  have hN : N • χ 1 = 0 := by rw [← map_nsmul]; simp [nsmul_eq_mul]
  refine ⟨t, ht, ?_, ?_⟩
  · rw [← he, ← AddCircle.coe_nsmul, AddCircle.coe_eq_zero_iff] at hN
    obtain ⟨k, hk⟩ := hN
    exact ⟨k, by simpa [nsmul_eq_mul] using hk.symm⟩
  · intro x n hn
    rw [← hχ x, hn]
    have hcast : (n : ZMod N) = n • (1 : ZMod N) := by simp [zsmul_eq_mul]
    rw [hcast, map_zsmul, ← he, ← AddCircle.coe_zsmul]
    congr 1
    simp [zsmul_eq_mul]

end Erdos3

end

end OAI

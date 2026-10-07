import Mathlib

namespace OAI

section

namespace Erdos3

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

def fourCoordinateKernel (S : Finset (Fin 4)) : Submodule ℚ (Fin 4 → V) :=
  ⨅ k ∈ S, LinearMap.ker (LinearMap.proj k)

theorem mem_fourCoordinateKernel (S : Finset (Fin 4)) (v : Fin 4 → V) :
    v ∈ fourCoordinateKernel S ↔ ∀ k ∈ S, v k = 0 := by
  simp [fourCoordinateKernel]

def fourFirstProjection (J : Submodule ℚ (Fin 4 → V)) : Submodule ℚ V :=
  J.map (LinearMap.proj 0)

theorem mem_fourFirstProjection (J : Submodule ℚ (Fin 4 → V)) (v : V) :
    v ∈ fourFirstProjection J ↔ ∃ w ∈ J, w 0 = v := Iff.rfl

def fourSparseFirstProjection (J : Submodule ℚ (Fin 4 → V)) (S : Finset (Fin 4)) : Submodule ℚ V :=
  (J ⊓ fourCoordinateKernel S).map (LinearMap.proj 0)

theorem mem_fourSparseFirstProjection (J : Submodule ℚ (Fin 4 → V))
    (S : Finset (Fin 4)) (v : V) :
    v ∈ fourSparseFirstProjection J S ↔ ∃ w ∈ J, w 0 = v ∧ ∀ k ∈ S, w k = 0 := by
  change (∃ w, w ∈ J ⊓ fourCoordinateKernel S ∧ w 0 = v) ↔ _
  constructor
  · rintro ⟨w, ⟨hw, hS⟩, hv⟩
    exact ⟨w, hw, hv, (mem_fourCoordinateKernel S w).mp hS⟩
  · rintro ⟨w, hw, hv, hS⟩
    exact ⟨w, ⟨hw, (mem_fourCoordinateKernel S w).mpr hS⟩, hv⟩

theorem fourSparseFirstProjection_le (J : Submodule ℚ (Fin 4 → V)) (S : Finset (Fin 4)) :
    fourSparseFirstProjection J S ≤ fourFirstProjection J :=
  Submodule.map_mono inf_le_left

def fourDependentProjection (J : Submodule ℚ (Fin 4 → V)) : Submodule ℚ V :=
  fourSparseFirstProjection J {1, 2} ⊓ fourSparseFirstProjection J {1, 3}

theorem fourDependentProjection_le (J : Submodule ℚ (Fin 4 → V)) :
    fourDependentProjection J ≤ fourFirstProjection J :=
  inf_le_left.trans (fourSparseFirstProjection_le J {1, 2})

end Erdos3

end

section

namespace Erdos3

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

def fourLinearMap (f : V →ₗ[ℚ] W) : (Fin 4 → V) →ₗ[ℚ] (Fin 4 → W) :=
  LinearMap.pi (fun k => f.comp (LinearMap.proj k))

theorem fourFirstProjection_map (f : V →ₗ[ℚ] W) (J : Submodule ℚ (Fin 4 → V)) :
    fourFirstProjection (J.map (fourLinearMap f)) = (fourFirstProjection J).map f := by
  ext y
  constructor
  · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨v 0, ⟨v, hv, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨fourLinearMap f v, ⟨v, hv, rfl⟩, rfl⟩

theorem fourSparseFirstProjection_map (f : V →ₗ[ℚ] W) (hf : Function.Injective f)
    (J : Submodule ℚ (Fin 4 → V)) (S : Finset (Fin 4)) :
    fourSparseFirstProjection (J.map (fourLinearMap f)) S = (fourSparseFirstProjection J S).map f := by
  ext y
  constructor
  · intro hy
    obtain ⟨w, ⟨v, hv, rfl⟩, hzero, hS⟩ := (mem_fourSparseFirstProjection _ _ _).mp hy
    refine ⟨v 0, (mem_fourSparseFirstProjection _ _ _).mpr ⟨v, hv, rfl, ?_⟩, hzero⟩
    intro k hk
    exact hf ((hS k hk).trans (map_zero f).symm)
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨v, hv, rfl, hS⟩ := (mem_fourSparseFirstProjection _ _ _).mp hx
    refine (mem_fourSparseFirstProjection _ _ _).mpr
      ⟨fourLinearMap f v, ⟨v, hv, rfl⟩, rfl, ?_⟩
    intro k hk
    change f (v k) = 0
    rw [hS k hk, map_zero]

theorem fourDependentProjection_map (f : V →ₗ[ℚ] W) (hf : Function.Injective f)
    (J : Submodule ℚ (Fin 4 → V)) :
    fourDependentProjection (J.map (fourLinearMap f)) = (fourDependentProjection J).map f := by
  rw [fourDependentProjection, fourSparseFirstProjection_map f hf, fourSparseFirstProjection_map f hf]
  ext y
  constructor
  · rintro ⟨⟨x, hx, hxy⟩, ⟨z, hz, hzy⟩⟩
    have hxz : x = z := hf (hxy.trans hzy.symm)
    exact ⟨x, ⟨hx, hxz.symm ▸ hz⟩, hxy⟩
  · rintro ⟨x, ⟨hx, hz⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, ⟨x, hz, rfl⟩⟩

end Erdos3

end

section

namespace Erdos3

theorem four_sparse_lifts_vanish {I : Type*} {V : I → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℚ (V i)]
    {M A : Type*} [Zero M] [AddCommGroup A]
    (S : Set I) (B : (∀ i, V i) → M)
    (hzero : ∀ v i, i ∈ S → v i = 0 → B v = 0)
    (η : M → A) (hη : η 0 = 0) (J : ∀ i, Submodule ℚ (Fin 4 → V i))
    (hJ : ∀ v : ∀ i, Fin 4 → V i, (∀ i, v i ∈ J i) →
      η (B (fun i => v i 0)) + η (B (fun i => v i 1)) -
        η (B (fun i => v i 2)) - η (B (fun i => v i 3)) = 0)
    (v : ∀ i, V i) (hv : ∀ i, v i ∈ fourFirstProjection (J i))
    (a b : I) (hab : a ≠ b) (ha : a ∈ S) (hb : b ∈ S)
    (hva : v a ∈ fourSparseFirstProjection (J a) {1, 2})
    (hvb : v b ∈ fourSparseFirstProjection (J b) {1, 3}) : η (B v) = 0 := by
  classical
  have hlift (i : I) : ∃ w ∈ J i, w 0 = v i := (mem_fourFirstProjection (J i) (v i)).mp (hv i)
  choose w hwJ hw0 using hlift
  obtain ⟨xa, hxa, hxa0, hxaz⟩ := (mem_fourSparseFirstProjection (J a) {1, 2} (v a)).mp hva
  obtain ⟨xb, hxb, hxb0, hxbz⟩ := (mem_fourSparseFirstProjection (J b) {1, 3} (v b)).mp hvb
  let z : ∀ i, Fin 4 → V i := Function.update (Function.update w a xa) b xb
  have hza : z a = xa := by simp [z, hab]
  have hzb : z b = xb := by simp [z]
  have hzJ (i : I) : z i ∈ J i := by
    by_cases hib : i = b
    · subst i
      rw [hzb]
      exact hxb
    by_cases hia : i = a
    · subst i
      rw [hza]
      exact hxa
    simpa only [z, Function.update_of_ne hib, Function.update_of_ne hia] using hwJ i
  have hzfirst : (fun i => z i 0) = v := by
    funext i
    by_cases hib : i = b
    · subst i
      rw [hzb]
      exact hxb0
    by_cases hia : i = a
    · subst i
      rw [hza]
      exact hxa0
    simpa only [z, Function.update_of_ne hib, Function.update_of_ne hia] using hw0 i
  have hz1 : B (fun i => z i 1) = 0 := hzero _ a ha (by rw [hza]; exact hxaz 1 (by simp))
  have hz2 : B (fun i => z i 2) = 0 := hzero _ a ha (by rw [hza]; exact hxaz 2 (by simp))
  have hz3 : B (fun i => z i 3) = 0 := hzero _ b hb (by rw [hzb]; exact hxbz 3 (by simp))
  have h := hJ z hzJ
  simpa only [hzfirst, hz1, hz2, hz3, hη, add_zero, sub_zero] using h

theorem four_dependent_inputs_vanish {I : Type*} {V : I → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℚ (V i)]
    {M A : Type*} [Zero M] [AddCommGroup A]
    (S : Set I) (B : (∀ i, V i) → M)
    (hzero : ∀ v i, i ∈ S → v i = 0 → B v = 0)
    (η : M → A) (hη : η 0 = 0) (J : ∀ i, Submodule ℚ (Fin 4 → V i))
    (hJ : ∀ v : ∀ i, Fin 4 → V i, (∀ i, v i ∈ J i) →
      η (B (fun i => v i 0)) + η (B (fun i => v i 1)) -
        η (B (fun i => v i 2)) - η (B (fun i => v i 3)) = 0)
    (v : ∀ i, V i) (hv : ∀ i, v i ∈ fourFirstProjection (J i))
    (a b : I) (hab : a ≠ b) (ha : a ∈ S) (hb : b ∈ S)
    (hva : v a ∈ fourDependentProjection (J a))
    (hvb : v b ∈ fourDependentProjection (J b)) : η (B v) = 0 :=
  four_sparse_lifts_vanish S B hzero η hη J hJ v hv a b hab ha hb hva.1 hvb.2

end Erdos3

end

end OAI

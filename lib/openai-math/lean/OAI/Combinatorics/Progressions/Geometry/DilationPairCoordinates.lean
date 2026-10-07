import Mathlib.Algebra.Module.Rat
import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.Abel

namespace OAI

section

namespace Erdos3

variable {L : Type*} [AddCommGroup L] [Module ℚ L]

def scaledPairDifference (q : ℚ) : (L × L) →ₗ[ℚ] L :=
  LinearMap.fst ℚ L L - q • LinearMap.snd ℚ L L

@[simp] theorem scaledPairDifference_apply (q : ℚ) (x : L × L) :
    scaledPairDifference q x = x.1 - q • x.2 := rfl

def scaledPairAssemble (q : ℚ) (u v : L) : L × L := (u + q • v, v)

@[simp] theorem scaledPairDifference_assemble (q : ℚ) (u v : L) :
    scaledPairDifference q (scaledPairAssemble q u v) = u := by
  simp [scaledPairAssemble]

theorem scaledPairAssemble_decompose (q : ℚ) (x : L × L) :
    scaledPairAssemble q (scaledPairDifference q x) x.2 = x := by
  apply Prod.ext <;> simp [scaledPairAssemble]

def scaledPairLayer (P Q : Submodule ℚ L) (q : ℚ) : Submodule ℚ (L × L) where
  carrier := {x | x.1 ∈ P ∧ x.2 ∈ P ∧ scaledPairDifference q x ∈ Q}
  zero_mem' := ⟨P.zero_mem, P.zero_mem, by simp⟩
  add_mem' hx hy := ⟨P.add_mem hx.1 hy.1, P.add_mem hx.2.1 hy.2.1,
    by simpa only [map_add] using Q.add_mem hx.2.2 hy.2.2⟩
  smul_mem' a x hx := ⟨P.smul_mem a hx.1, P.smul_mem a hx.2.1,
    by simpa only [map_smul] using Q.smul_mem a hx.2.2⟩

@[simp] theorem mem_scaledPairLayer (P Q : Submodule ℚ L) (q : ℚ) (x : L × L) :
    x ∈ scaledPairLayer P Q q ↔ x.1 ∈ P ∧ x.2 ∈ P ∧ x.1 - q • x.2 ∈ Q := Iff.rfl

def scaledPairLayerEquiv (P Q : Submodule ℚ L) (hQP : Q ≤ P) (q : ℚ) :
    (Q × P) ≃ₗ[ℚ] scaledPairLayer P Q q where
  toFun x := ⟨scaledPairAssemble q x.1 x.2,
    ⟨P.add_mem (hQP x.1.property) (P.smul_mem q x.2.property), x.2.property,
      by
        rw [scaledPairDifference_assemble]
        exact x.1.property⟩⟩
  invFun x := (⟨scaledPairDifference q x.val, x.property.2.2⟩, ⟨x.val.2, x.property.2.1⟩)
  left_inv x := by
    apply Prod.ext
    · exact Subtype.ext (scaledPairDifference_assemble q (x.1 : L) (x.2 : L))
    · rfl
  right_inv x := Subtype.ext (scaledPairAssemble_decompose q x.val)
  map_add' x y := by
    apply Subtype.ext
    apply Prod.ext
    · simp only [scaledPairAssemble, Prod.fst_add, Prod.snd_add, Submodule.coe_add, smul_add]
      abel
    · rfl
  map_smul' a x := by
    apply Subtype.ext
    apply Prod.ext
    · change a • (x.1 : L) + q • (a • (x.2 : L)) = a • ((x.1 : L) + q • (x.2 : L))
      rw [smul_add, smul_comm q a]
    · rfl

end Erdos3

end

end OAI

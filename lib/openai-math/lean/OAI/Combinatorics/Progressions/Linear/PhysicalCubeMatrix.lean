import OAI.Combinatorics.Progressions.Geometry.PrincipalSpatialSiteComparison

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Matrix

def physicalCubeCoefficient {K α : Type*} (root : K → ℤ) (D : Matrix α K ℤ) :
    Matrix (Unit ⊕ α) (Option K) ℤ
  | .inl _, none => 1
  | .inl _, some k => root k
  | .inr _, none => 0
  | .inr i, some k => D i k

def physicalCubeOffset {X α : Type*} (base : X → ℤ) (x : X) : (Unit ⊕ α) → ℤ
  | .inl _ => base x
  | .inr _ => 0

def physicalCubeRootDifferences {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (z : Option K × X → ℤ) : X → (Unit ⊕ α) → ℤ :=
  fun x i => physicalCubeOffset base x i + ∑ k, physicalCubeCoefficient root D i k * z (k, x)

theorem physicalCubeRootDifferences_root {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (z : Option K × X → ℤ) (x : X) :
    physicalCubeRootDifferences root D base z x (.inl ()) =
      jointIntegerPhysicalSite root (base, z) x := by
  simp [physicalCubeRootDifferences, physicalCubeOffset, physicalCubeCoefficient,
    jointIntegerPhysicalSite, integerPhysicalSite]

theorem physicalCubeRootDifferences_direction {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (z : Option K × X → ℤ) (x : X) (i : α) :
    physicalCubeRootDifferences root D base z x (.inr i) = ∑ k, D i k * z (some k, x) := by
  simp [physicalCubeRootDifferences, physicalCubeOffset, physicalCubeCoefficient]

theorem physicalCubeRootDifferences_vertex {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (z : Option K × X → ℤ) (x : X) (t : Finset α) :
    physicalCubeRootDifferences root D base z x (.inl ()) +
        ∑ i ∈ t, physicalCubeRootDifferences root D base z x (.inr i) =
      jointIntegerPhysicalSite (integerAffineCube root D t) (base, z) x := by
  rw [physicalCubeRootDifferences_root]
  simp_rw [physicalCubeRootDifferences_direction]
  have hs : (∑ k, ∑ i ∈ t, D i k * z (some k, x)) =
      ∑ i ∈ t, ∑ k, D i k * z (some k, x) := Finset.sum_comm
  simp only [jointIntegerPhysicalSite, integerPhysicalSite, Pi.add_apply,
    integerAffineCube, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  rw [hs]
  ring

theorem physicalCubeRootDifferences_star {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (z : Option K × X → ℤ) (x : X) (i : Unit ⊕ α) :
    spatialStar (physicalCubeRootDifferences root D base z x) i =
      jointIntegerPhysicalSite (integerAffineCube root D (spatialStarVertex i)) (base, z) x := by
  rw [spatialStar_vertex, physicalCubeRootDifferences_vertex]

def physicalCubeBlockMatrix {K X α : Type*} [DecidableEq X]
    (root : K → ℤ) (D : Matrix α K ℤ) : Matrix (X × (Unit ⊕ α)) (Option K × X) ℤ :=
  fun row col => if row.1 = col.2 then physicalCubeCoefficient root D row.2 col.1 else 0

theorem physicalCubeBlockMatrix_mulVec {K X α : Type*}
    [Fintype K] [Fintype X] [DecidableEq X]
    (root : K → ℤ) (D : Matrix α K ℤ) (z : Option K × X → ℤ) (x : X) (i : Unit ⊕ α) :
    (physicalCubeBlockMatrix root D *ᵥ z) (x, i) =
      ∑ k, physicalCubeCoefficient root D i k * z (k, x) := by
  simp [physicalCubeBlockMatrix, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, ite_mul]

theorem physicalCubeRootDifferences_matrix {K X α : Type*}
    [Fintype K] [Fintype X] [DecidableEq X]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ) (z : Option K × X → ℤ) :
    (fun row : X × (Unit ⊕ α) => physicalCubeRootDifferences root D base z row.1 row.2) =
      (fun row => physicalCubeOffset base row.1 row.2) + physicalCubeBlockMatrix root D *ᵥ z := by
  funext row
  rw [Pi.add_apply, physicalCubeBlockMatrix_mulVec]
  rfl

end Erdos3.BooleanCubeKernel

end

end OAI

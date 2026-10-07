import OAI.Combinatorics.Progressions.Linear.ContainedKernelPhysicalDisplacement
import OAI.Combinatorics.Progressions.Linear.PreparedSpatialKernelBlocks

namespace OAI

section

namespace Erdos3
open scoped Classical

def twoKernelCopies (X : Type*) : X ⊕ X ≃ Fin 2 × X where
  toFun := Sum.elim (fun x => (0, x)) (fun x => (1, x))
  invFun z := if z.1 = 0 then Sum.inl z.2 else Sum.inr z.2
  left_inv := by intro z; cases z <;> simp
  right_inv := by rintro ⟨i, x⟩; fin_cases i <;> simp

def twoKernelEmbedding {X G : Type*} (blocks : Fin 2 × X ↪ G) : X ⊕ X ↪ G :=
  (twoKernelCopies X).toEmbedding.trans blocks

abbrev SpatialKernelRemainder {X G : Type*} (blocks : Fin 2 × X ↪ G) :=
  {g : G // g ∉ Set.range (twoKernelEmbedding blocks)}

noncomputable def spatialTwoBlockEquiv {X G : Type*} (blocks : Fin 2 × X ↪ G) :
    G ≃ X ⊕ (X ⊕ SpatialKernelRemainder blocks) :=
  ((Equiv.sumCongr (Equiv.ofInjective (twoKernelEmbedding blocks)
      (twoKernelEmbedding blocks).injective) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range (twoKernelEmbedding blocks)))).symm.trans
      (Equiv.sumAssoc X X (SpatialKernelRemainder blocks))

@[simp] theorem spatialTwoBlockEquiv_symm_first {X G : Type*}
    (blocks : Fin 2 × X ↪ G) (x : X) :
    (spatialTwoBlockEquiv blocks).symm (Sum.inl x) = blocks (0, x) := rfl

@[simp] theorem spatialTwoBlockEquiv_symm_second {X G : Type*}
    (blocks : Fin 2 × X ↪ G) (x : X) :
    (spatialTwoBlockEquiv blocks).symm (Sum.inr (Sum.inl x)) = blocks (1, x) := rfl

theorem fixedSpatialKernelBlock_first {X G : Type*} [Fintype X] [Fintype G]
    (blocks : Fin 2 × X ↪ G) (W L : ℝ) (z : Option G × X → ℝ) (x i : X) :
    fixedSpatialKernelBlock (spatialTwoBlockEquiv blocks) W L z false x i =
      (L / (1 + W)) * z (some (blocks (0, i)), x) := rfl

theorem fixedSpatialKernelBlock_second {X G : Type*} [Fintype X] [Fintype G]
    (blocks : Fin 2 × X ↪ G) (W L : ℝ) (z : Option G × X → ℝ) (x i : X) :
    fixedSpatialKernelBlock (spatialTwoBlockEquiv blocks) W L z true x i =
      (L / (1 + W)) * z (some (blocks (1, i)), x) := rfl

end Erdos3

end

end OAI

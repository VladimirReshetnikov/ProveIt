import OAI.Combinatorics.Progressions.Estimates.SquarefreeRealAction

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound) (p : ℝ) (B : ℕ) (hB : 0 < B)
  (hstable : M.SquarefreeGridStable p B)

noncomputable def squarefreeSpacePermute (e : ReplicatedPermutation bound) :
    (M.squarefreeModel p B hB hstable).Space → (M.squarefreeModel p B hB hstable).Space :=
  cosetMap _ _ (M.squarefreeRealPermute p B hB hstable e)
    (M.squarefreeRealPermute_lattice p B hB hstable e)

theorem squarefreeSpacePermute_mk (e : ReplicatedPermutation bound)
    (g : (M.squarefreeModel p B hB hstable).RealGroup) :
    M.squarefreeSpacePermute p B hB hstable e (QuotientGroup.mk g) =
      QuotientGroup.mk (M.squarefreeRealPermute p B hB hstable e g) := rfl

theorem squarefreeSpacePermute_one (x : (M.squarefreeModel p B hB hstable).Space) :
    M.squarefreeSpacePermute p B hB hstable 1 x = x := by
  induction x using Quotient.inductionOn with
  | h g => rw [M.squarefreeSpacePermute_mk, M.squarefreeRealPermute_one]

theorem squarefreeSpacePermute_mul (e f : ReplicatedPermutation bound)
    (x : (M.squarefreeModel p B hB hstable).Space) :
    M.squarefreeSpacePermute p B hB hstable (e * f) x =
      M.squarefreeSpacePermute p B hB hstable e (M.squarefreeSpacePermute p B hB hstable f x) := by
  induction x using Quotient.inductionOn with
  | h g =>
    rw [M.squarefreeSpacePermute_mk, M.squarefreeSpacePermute_mk,
      M.squarefreeSpacePermute_mk, M.squarefreeRealPermute_mul]

@[instance_reducible]
noncomputable def squarefreeSpaceAction :
    MulAction (ReplicatedPermutation bound) (M.squarefreeModel p B hB hstable).Space where
  smul := M.squarefreeSpacePermute p B hB hstable
  one_smul := M.squarefreeSpacePermute_one p B hB hstable
  mul_smul := M.squarefreeSpacePermute_mul p B hB hstable

theorem squarefreeSpacePermute_smul (e : ReplicatedPermutation bound)
    (g : (M.squarefreeModel p B hB hstable).RealGroup)
    (x : (M.squarefreeModel p B hB hstable).Space) :
    M.squarefreeSpacePermute p B hB hstable e (g • x) =
      M.squarefreeRealPermute p B hB hstable e g • M.squarefreeSpacePermute p B hB hstable e x :=
  cosetMap_smul _ _ _ _ _ _

theorem squarefreeSpacePermute_commutes_top (e : ReplicatedPermutation bound)
    (g : (M.squarefreeModel p B hB hstable).RealGroup)
    (hg : g ∈ (M.squarefreeModel p B hB hstable).filtration.realification.subgroup
      (Fintype.card (ReplicatedIndex bound))) (x : (M.squarefreeModel p B hB hstable).Space) :
    M.squarefreeSpacePermute p B hB hstable e (g • x) =
      g • M.squarefreeSpacePermute p B hB hstable e x := by
  rw [M.squarefreeSpacePermute_smul, M.squarefreeRealPermute_top p B hB hstable e g hg]

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI

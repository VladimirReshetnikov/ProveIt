import OAI.Combinatorics.Progressions.Estimates.RationalRealSubgroup

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem realification_subgroup_eq_realificationSubgroup (i : ℕ) :
    F.realification.subgroup i =
      NilpotentLieBCHGroup.realificationSubgroup (hnil := F.lowerCentralSeries_eq_bot)
        (F.layerIdeal i).toLieSubalgebra := by
  ext g
  rfl

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem realification_layer_lattice_closed_discrete (e : Basis ι ℚ L)
    (Γ : Subgroup F.Group) (l : ℕ) (hl : 0 < l)
    (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l) (i : ℕ) :
    let Λ := (Γ.map NilpotentLieBCHGroup.realificationHom).comap (F.realification.subgroup i).subtype
    IsClosed (Λ : Set (F.realification.subgroup i)) ∧ IsDiscrete (Λ : Set (F.realification.subgroup i)) := by
  rw [F.realification_subgroup_eq_realificationSubgroup]
  exact NilpotentLieBCHGroup.realificationSubgroup_lattice_closed_discrete e
    (F.layerIdeal i).toLieSubalgebra Γ l hl houter

omit [T2Space (ℝ ⊗[ℚ] L)] in
theorem realification_layer_lattice_cocompact (e : Basis ι ℚ L)
    (Γ : Subgroup F.Group) (l : ℕ) (hl : 0 < l)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l) (i : ℕ) :
    CompactSpace (F.realification.subgroup i ⧸
      (Γ.map NilpotentLieBCHGroup.realificationHom).comap (F.realification.subgroup i).subtype) := by
  rw [F.realification_subgroup_eq_realificationSubgroup]
  exact NilpotentLieBCHGroup.realificationSubgroup_lattice_cocompact e
    (F.layerIdeal i).toLieSubalgebra Γ l hl hinner houter

end Erdos3.NilpotentLieFiltration

end

end OAI

import OAI.Combinatorics.Progressions.Nilpotent.BCHChartCutoffSmooth

namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem realDenominatorGrid_exists_rational {ι : Type*} (l : ℕ) (hl : 0 < l)
    (x : ι → ℝ) (hx : x ∈ realDenominatorGrid l) :
    ∃ y : ι → ℚ, y ∈ denominatorGrid l ∧ (fun i => (y i : ℝ)) = x := by
  obtain ⟨z, hz⟩ := hx
  let y : ι → ℚ := fun i => (z i : ℚ) / l
  have hy : (fun i => (y i : ℝ)) = x := by
    funext i
    change (((z i : ℚ) / l : ℚ) : ℝ) = x i
    push_cast
    apply (div_eq_iff (show (l : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr hl.ne')).mpr
    have hi := congrFun hz i
    change (z i : ℝ) = (l : ℝ) * x i at hi
    simpa only [mul_comm] using hi
  refine ⟨y, (real_cast_mem_denominatorGrid_iff l y).mp ?_, hy⟩
  rw [hy]
  exact ⟨z, hz⟩

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

theorem real_grid_exists_rationalLieInclusion (e : Basis ι ℚ L) (l : ℕ) (hl : 0 < l)
    (x : ℝ ⊗[ℚ] L) (hx : (e.baseChange ℝ).equivFun x ∈ realDenominatorGrid l) :
    ∃ a : L, e.equivFun a ∈ denominatorGrid l ∧ rationalLieInclusion a = x := by
  obtain ⟨y, hy, heq⟩ := realDenominatorGrid_exists_rational l hl _ hx
  refine ⟨e.equivFun.symm y, ?_, ?_⟩
  · simpa only [LinearEquiv.apply_symm_apply] using hy
  · apply (e.baseChange ℝ).equivFun.injective
    funext i
    calc
      _ = (e.equivFun (e.equivFun.symm y) i : ℝ) :=
        rationalLieInclusion_coordinates e (e.equivFun.symm y) i
      _ = (y i : ℝ) := by rw [LinearEquiv.apply_symm_apply]
      _ = _ := congrFun heq i

namespace NilpotentLieBCHGroup

variable {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem realification_grid_iff (e : Basis ι ℚ L) (l : ℕ) (hl : 0 < l)
    (g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil)) :
    (e.baseChange ℝ).equivFun g.coord ∈ realDenominatorGrid l ↔
      ∃ a : NilpotentLieBCHGroup L s hnil,
        e.equivFun a.coord ∈ denominatorGrid l ∧ realificationHom a = g := by
  constructor
  · intro hg
    obtain ⟨a, ha, heq⟩ := real_grid_exists_rationalLieInclusion e l hl g.coord hg
    exact ⟨⟨a⟩, ha, ext heq⟩
  · rintro ⟨a, ha, rfl⟩
    rw [realificationHom_coordinates, real_cast_mem_denominatorGrid_iff]
    exact ha

end NilpotentLieBCHGroup
end Erdos3

end

end OAI

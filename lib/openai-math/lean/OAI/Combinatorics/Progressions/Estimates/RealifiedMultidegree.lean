import Mathlib.Algebra.Lie.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.Basis
import OAI.Combinatorics.Progressions.Estimates.MultidegreeDilationPair
import OAI.Combinatorics.Progressions.Estimates.RealSubquotientEquiv

namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L]

noncomputable def rationalLieInclusion : L →ₗ⁅ℚ⁆ (ℝ ⊗[ℚ] L) where
  toLinearMap := TensorProduct.mk ℚ ℝ L 1
  map_lie' {x y} := by simp [LieAlgebra.ExtendScalars.bracket_tmul]

@[simp]
theorem rationalLieInclusion_apply (x : L) : rationalLieInclusion x = (1 : ℝ) ⊗ₜ[ℚ] x := rfl

theorem rationalLieInclusion_coordinates (e : Basis ι ℚ L) (x : L) (i : ι) :
    (e.baseChange ℝ).repr (rationalLieInclusion x) i = (e.repr x i : ℝ) := by
  simp [Basis.baseChange_repr_tmul, Algebra.smul_def]

theorem rationalLieInclusion_injective (e : Basis ι ℚ L) :
    Function.Injective (rationalLieInclusion : L →ₗ⁅ℚ⁆ (ℝ ⊗[ℚ] L)) := by
  intro x y h
  apply e.repr.injective
  ext i
  have hi := congrArg (fun z => (e.baseChange ℝ).repr z i) h
  rw [rationalLieInclusion_coordinates, rationalLieInclusion_coordinates] at hi
  exact_mod_cast hi

theorem realLieBasis_structure (e : Basis ι ℚ L) (i j k : ι) :
    (e.baseChange ℝ).repr ⁅e.baseChange ℝ i, e.baseChange ℝ j⁆ k =
      (lieStructureConstants e i j k : ℝ) := by
  simp [Basis.baseChange_apply, LieAlgebra.ExtendScalars.bracket_tmul,
    Basis.baseChange_repr_tmul, Algebra.smul_def, lieStructureConstants]

theorem realification_lowerCentralSeries_eq_bot {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) :
    LieModule.lowerCentralSeries ℚ (ℝ ⊗[ℚ] L) (ℝ ⊗[ℚ] L) s = ⊥ := by
  have hreal : LieModule.lowerCentralSeries ℝ (ℝ ⊗[ℚ] L) (ℝ ⊗[ℚ] L) s = ⊥ := by
    rw [LieSubmodule.lowerCentralSeries_tensor_eq_baseChange, hnil, LieSubmodule.baseChange_bot]
  apply SetLike.coe_injective
  change (LieModule.lowerCentralSeries ℚ (ℝ ⊗[ℚ] L) (ℝ ⊗[ℚ] L) s : Set (ℝ ⊗[ℚ] L)) = {0}
  rw [LieModule.coe_lowerCentralSeries_eq_int,
    ← LieModule.coe_lowerCentralSeries_eq_int ℝ (ℝ ⊗[ℚ] L) (ℝ ⊗[ℚ] L) s, hreal]
  rfl

namespace NilpotentLieBCHGroup

variable {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

noncomputable def realificationHom :
    NilpotentLieBCHGroup L s hnil →*
      NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil) :=
  map rationalLieInclusion

@[simp]
theorem realificationHom_coord (g : NilpotentLieBCHGroup L s hnil) :
    (realificationHom g).coord = rationalLieInclusion g.coord := rfl

theorem realificationHom_injective (e : Basis ι ℚ L) :
    Function.Injective (realificationHom (hnil := hnil)) := by
  intro g h heq
  apply ext
  apply rationalLieInclusion_injective e
  exact congrArg coord heq

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def realLayer (i : ℕ) : LieIdeal ℝ (ℝ ⊗[ℚ] L) := (F.layerIdeal i).baseChange ℝ

theorem realLayer_antitone : Antitone F.realLayer := by
  intro i j hij
  exact Submodule.baseChange_mono ℝ (F.antitone hij)

theorem realLayer_one : F.realLayer 1 = ⊤ := by
  have h : F.layerIdeal 1 = ⊤ := by
    ext a
    change a ∈ F.layer 1 ↔ a ∈ (⊤ : Submodule ℚ L)
    rw [F.one_eq_top]
  simp only [realLayer, h, LieSubmodule.baseChange_top]

theorem realLayer_terminal : F.realLayer (s + 1) = ⊥ := by
  have h : F.layerIdeal (s + 1) = ⊥ := by
    ext a
    change a ∈ F.layer (s + 1) ↔ a ∈ (⊥ : Submodule ℚ L)
    rw [F.terminal]
  simp only [realLayer, h, LieSubmodule.baseChange_bot]

theorem lie_realLayer_le (i j : ℕ) : ⁅F.realLayer i, F.realLayer j⁆ ≤ F.realLayer (i + j) := by
  have h : ⁅F.layerIdeal i, F.layerIdeal j⁆ ≤ F.layerIdeal (i + j) := by
    rw [LieSubmodule.lie_le_iff]
    exact fun a ha b hb => F.lie_mem ha hb
  rw [realLayer, realLayer, ← LieSubmodule.lie_baseChange]
  exact Submodule.baseChange_mono ℝ h

theorem realLayer_lie_mem {i j : ℕ} {a b : ℝ ⊗[ℚ] L}
    (ha : a ∈ F.realLayer i) (hb : b ∈ F.realLayer j) : ⁅a, b⁆ ∈ F.realLayer (i + j) :=
  F.lie_realLayer_le i j (LieSubmodule.lie_mem_lie ha hb)

noncomputable def realification : NilpotentLieFiltration (ℝ ⊗[ℚ] L) s where
  layer i := (F.realLayer i).toSubmodule.restrictScalars ℚ
  antitone := F.realLayer_antitone
  one_eq_top := by rw [F.realLayer_one]; rfl
  lie_mem := F.realLayer_lie_mem
  terminal := by rw [F.realLayer_terminal]; rfl

theorem rational_inclusion_mem_realLayer {i : ℕ} {a : L} (ha : a ∈ F.layer i) :
    rationalLieInclusion a ∈ F.realLayer i :=
  LieSubmodule.tmul_mem_baseChange_of_mem 1 ha

theorem realificationHom_mem_subgroup {i : ℕ} {g : F.Group} (hg : g ∈ F.subgroup i) :
    NilpotentLieBCHGroup.realificationHom g ∈ F.realification.subgroup i :=
  F.rational_inclusion_mem_realLayer hg

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped TensorProduct BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def realLayer (a : σ → ℕ) : LieIdeal ℝ (ℝ ⊗[ℚ] L) := (F.layerIdeal a).baseChange ℝ

theorem realLayer_antitone : Antitone F.realLayer :=
  fun _ _ h => Submodule.baseChange_mono ℝ (F.antitone h)

theorem realLayer_zero : F.realLayer 0 = ⊤ := by
  have h : F.layerIdeal 0 = ⊤ := by
    ext x
    change x ∈ F.layer 0 ↔ x ∈ (⊤ : Submodule ℚ L)
    rw [F.zero_eq_top]
  simp only [realLayer, h, LieSubmodule.baseChange_top]

theorem realLayer_terminal (a : σ → ℕ) (ha : ¬a ≤ bound) : F.realLayer a = ⊥ := by
  have h : F.layerIdeal a = ⊥ := by
    ext x
    change x ∈ F.layer a ↔ x ∈ (⊥ : Submodule ℚ L)
    rw [F.terminal a ha]
  simp only [realLayer, h, LieSubmodule.baseChange_bot]

theorem realLayer_lie_mem {a b : σ → ℕ} {x y : ℝ ⊗[ℚ] L}
    (hx : x ∈ F.realLayer a) (hy : y ∈ F.realLayer b) : ⁅x, y⁆ ∈ F.realLayer (a + b) := by
  have h : ⁅F.layerIdeal a, F.layerIdeal b⁆ ≤ F.layerIdeal (a + b) := by
    rw [LieSubmodule.lie_le_iff]
    exact fun x hx y hy => F.lie_mem hx hy
  have hreal : ⁅F.realLayer a, F.realLayer b⁆ ≤ F.realLayer (a + b) := by
    rw [realLayer, realLayer, ← LieSubmodule.lie_baseChange]
    exact Submodule.baseChange_mono ℝ h
  exact hreal (LieSubmodule.lie_mem_lie hx hy)

theorem realLayer_degree_eq (n : ℕ) :
    (F.ordinary.realLayer n).toSubmodule =
      ⨆ (a : σ → ℕ) (_ha : n ≤ ∑ i, a i), (F.realLayer a).toSubmodule := by
  change (F.ordinary.layer n).baseChange ℝ =
    ⨆ (a : σ → ℕ) (_ha : n ≤ ∑ i, a i), (F.layer a).baseChange ℝ
  rw [F.degree_eq]
  simp only [real_baseChange_iSup]

noncomputable def realification : MultidegreeLieFiltration σ (ℝ ⊗[ℚ] L) s bound where
  ordinary := F.ordinary.realification
  layer a := (F.realLayer a).toSubmodule.restrictScalars ℚ
  antitone := F.realLayer_antitone
  zero_eq_top := by rw [F.realLayer_zero]; rfl
  lie_mem := F.realLayer_lie_mem
  terminal a ha := by rw [F.realLayer_terminal a ha]; rfl
  degree_eq n := by
    change (F.ordinary.realLayer n).toSubmodule.restrictScalars ℚ = _
    rw [F.realLayer_degree_eq]
    simp only [real_restrictScalars_iSup]

end Erdos3.MultidegreeLieFiltration

end

end OAI

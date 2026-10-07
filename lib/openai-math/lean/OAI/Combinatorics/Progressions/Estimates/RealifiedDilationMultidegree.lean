import OAI.Combinatorics.Progressions.Estimates.PolarizedCoefficientPermutation
import OAI.Combinatorics.Progressions.Geometry.RealifiedPairCoordinates

namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {L : Type*} [AddCommGroup L] [Module ℚ L]

theorem scaledPairLayer_eq_inf (P Q : Submodule ℚ L) (q : ℚ) :
    scaledPairLayer P Q q = P.comap (LinearMap.fst ℚ L L) ⊓
      (P.comap (LinearMap.snd ℚ L L) ⊓ Q.comap (scaledPairDifference q)) := by
  ext x
  rfl

theorem realPairEquiv_mem_scaledPairLayer (P Q : Submodule ℚ L) (q : ℚ)
    (x : ℝ ⊗[ℚ] (L × L)) :
    realPairEquiv x ∈ scaledPairLayer ((P.baseChange ℝ).restrictScalars ℚ)
        ((Q.baseChange ℝ).restrictScalars ℚ) q ↔
      x ∈ (scaledPairLayer P Q q).baseChange ℝ := by
  change ((realPairEquiv x).1 ∈ P.baseChange ℝ ∧
    (realPairEquiv x).2 ∈ P.baseChange ℝ ∧
    scaledPairDifference q (realPairEquiv x) ∈ Q.baseChange ℝ) ↔ _
  rw [realPairEquiv_difference, realPairEquiv_first, realPairEquiv_second]
  simp only [scaledPairLayer_eq_inf, realification_inf, realification_comap,
    Submodule.mem_inf, Submodule.mem_comap]

noncomputable def realifiedScaledPairLayerEquiv (P Q : Submodule ℚ L) (q : ℚ) :
    ((scaledPairLayer P Q q).baseChange ℝ) ≃ₗ[ℚ]
      scaledPairLayer ((P.baseChange ℝ).restrictScalars ℚ)
        ((Q.baseChange ℝ).restrictScalars ℚ) q where
  toFun x := ⟨realPairEquiv x.val, (realPairEquiv_mem_scaledPairLayer P Q q x.val).mpr x.property⟩
  invFun x := ⟨realPairEquiv.symm x.val, (realPairEquiv_mem_scaledPairLayer P Q q _).mp (by
    simpa only [LinearEquiv.apply_symm_apply] using x.property)⟩
  left_inv x := Subtype.ext (realPairEquiv.symm_apply_apply x.val)
  right_inv x := Subtype.ext (realPairEquiv.apply_symm_apply x.val)
  map_add' x y := Subtype.ext (realPairEquiv.map_add x.val y.val)
  map_smul' r x := Subtype.ext ((realPairEquiv.restrictScalars ℚ).map_smul r x.val)

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem realPairEquiv_mem_dilationPairLayer (q : ℚ) (n : ℕ)
    (x : ℝ ⊗[ℚ] (L × L)) :
    realPairEquiv x ∈ F.realification.dilationPairLayer q n ↔
      x ∈ (F.dilationPairLayer q n).baseChange ℝ :=
  realPairEquiv_mem_scaledPairLayer (F.layer n) (F.layer (n + 1)) (q ^ n) x

noncomputable def realifiedDilationPairLayerEquiv (q : ℚ) (n : ℕ) :
    ((F.dilationPairLayer q n).baseChange ℝ) ≃ₗ[ℚ]
      F.realification.dilationPairLayer q n :=
  realifiedScaledPairLayerEquiv (F.layer n) (F.layer (n + 1)) (q ^ n)

noncomputable def realifiedDilationPairEquiv (q : ℚ) :
    (ℝ ⊗[ℚ] F.dilationPairSubalgebra q) ≃ₗ[ℚ]
      F.realification.dilationPairSubalgebra q :=
  ((realificationSubmoduleEquiv (F.dilationPairLayer q 1)).restrictScalars ℚ).trans
    (F.realifiedDilationPairLayerEquiv q 1)

theorem realifiedDilationPairEquiv_coe (q : ℚ)
    (x : ℝ ⊗[ℚ] F.dilationPairSubalgebra q) :
    (F.realifiedDilationPairEquiv q x : (ℝ ⊗[ℚ] L) × (ℝ ⊗[ℚ] L)) =
      realPairEquiv (realificationLieHom (F.dilationPairSubalgebra q).incl x) := rfl

theorem realifiedDilationPairEquiv_mem_layer (q : ℚ) (n : ℕ)
    (x : ℝ ⊗[ℚ] F.dilationPairSubalgebra q) :
    x ∈ (F.dilationPairFiltration q).realification.layer n ↔
      F.realifiedDilationPairEquiv q x ∈ (F.realification.dilationPairFiltration q).layer n := by
  change x ∈ ((F.dilationPairLayer q n).comap
    (F.dilationPairSubalgebra q).incl.toLinearMap).baseChange ℝ ↔ _
  rw [realification_comap]
  change realificationLieHom (F.dilationPairSubalgebra q).incl x ∈
    (F.dilationPairLayer q n).baseChange ℝ ↔
      (F.realifiedDilationPairEquiv q x : (ℝ ⊗[ℚ] L) × (ℝ ⊗[ℚ] L)) ∈
        F.realification.dilationPairLayer q n
  rw [F.realifiedDilationPairEquiv_coe, F.realPairEquiv_mem_dilationPairLayer]

theorem realifiedDilationPairEquiv_symm_mem_layer (q : ℚ) (n : ℕ)
    (x : F.realification.dilationPairSubalgebra q) :
    (F.realifiedDilationPairEquiv q).symm x ∈ (F.dilationPairFiltration q).realification.layer n ↔
      x ∈ (F.realification.dilationPairFiltration q).layer n := by
  rw [F.realifiedDilationPairEquiv_mem_layer, LinearEquiv.apply_symm_apply]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped TensorProduct BigOperators

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem strictUpperLayer_realification (a : σ → ℕ) :
    (F.realification.strictUpperLayer a).toSubmodule =
      ((F.strictUpperLayer a).toSubmodule.baseChange ℝ).restrictScalars ℚ := by
  simp only [strictUpperLayer, LieSubmodule.iSup_toSubmodule,
    real_baseChange_iSup, real_restrictScalars_iSup]
  rfl

theorem realPairEquiv_mem_dilationPairLayer (q : ℚ) (a : σ → ℕ)
    (x : ℝ ⊗[ℚ] (L × L)) :
    realPairEquiv x ∈ F.realification.dilationPairLayer q a ↔
      x ∈ (F.dilationPairLayer q a).baseChange ℝ := by
  change realPairEquiv x ∈ scaledPairLayer (F.realification.layer a)
    (F.realification.strictUpperLayer a).toSubmodule (q ^ ∑ i, a i) ↔ _
  rw [F.strictUpperLayer_realification]
  exact realPairEquiv_mem_scaledPairLayer (F.layer a) (F.strictUpperLayer a).toSubmodule _ x

theorem realifiedDilationPairEquiv_mem_multidegree (q : ℚ) (a : σ → ℕ)
    (x : ℝ ⊗[ℚ] F.ordinary.dilationPairSubalgebra q) :
    x ∈ (F.dilationPairMultidegree q).realification.layer a ↔
      F.ordinary.realifiedDilationPairEquiv q x ∈ (F.realification.dilationPairMultidegree q).layer a := by
  change x ∈ ((F.dilationPairLayer q a).comap
    (F.ordinary.dilationPairSubalgebra q).incl.toLinearMap).baseChange ℝ ↔ _
  rw [realification_comap]
  change realificationLieHom (F.ordinary.dilationPairSubalgebra q).incl x ∈
    (F.dilationPairLayer q a).baseChange ℝ ↔
      (F.ordinary.realifiedDilationPairEquiv q x : (ℝ ⊗[ℚ] L) × (ℝ ⊗[ℚ] L)) ∈
        F.realification.dilationPairLayer q a
  rw [F.ordinary.realifiedDilationPairEquiv_coe, F.realPairEquiv_mem_dilationPairLayer]

theorem realifiedDilationPairEquiv_symm_mem_multidegree (q : ℚ) (a : σ → ℕ)
    (x : F.ordinary.realification.dilationPairSubalgebra q) :
    (F.ordinary.realifiedDilationPairEquiv q).symm x ∈
        (F.dilationPairMultidegree q).realification.layer a ↔
      x ∈ (F.realification.dilationPairMultidegree q).layer a := by
  rw [F.realifiedDilationPairEquiv_mem_multidegree, LinearEquiv.apply_symm_apply]

end Erdos3.MultidegreeLieFiltration

end

end OAI

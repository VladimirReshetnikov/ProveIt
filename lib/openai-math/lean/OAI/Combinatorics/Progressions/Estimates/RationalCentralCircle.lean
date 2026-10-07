import OAI.Combinatorics.Progressions.Fourier.VerticalFrequencyIdentification

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d)

noncomputable def rationalDirectionPeriod (v : L) : ℕ :=
  D.grid * arrayDenominator (D.basis.equivFun v)

theorem rationalDirectionPeriod_pos (v : L) : 0 < D.rationalDirectionPeriod v :=
  Nat.mul_pos D.grid_pos (arrayDenominator_pos _)

theorem rationalDirectionPeriod_mem_lattice (v : L) :
    (⟨(D.rationalDirectionPeriod v : ℚ) • v⟩ : D.filtration.Group) ∈ D.lattice := by
  have hc : D.basis.equivFun ((D.rationalDirectionPeriod v : ℚ) • v) ∈
      scaledIntegerGrid D.grid := by
    refine ⟨clearedArray (D.basis.equivFun v), ?_⟩
    rw [map_smul]
    ext i
    change (D.rationalDirectionPeriod v : ℚ) * D.basis.equivFun v i =
      (D.grid : ℚ) * (clearedArray (D.basis.equivFun v) i : ℚ)
    rw [clearedArray_cast]
    simp only [rationalDirectionPeriod, Nat.cast_mul, mul_assoc]
  have h := D.inner_grid hc
  change (⟨D.basis.equivFun.symm (D.basis.equivFun
    ((D.rationalDirectionPeriod v : ℚ) • v))⟩ : D.filtration.Group) ∈ D.lattice at h
  simpa only [LinearEquiv.symm_apply_apply] using h

noncomputable def periodicRealDirection (v : L) : ℝ ⊗[ℚ] L :=
  rationalLieInclusion ((D.rationalDirectionPeriod v : ℚ) • v)

theorem periodicRealDirection_eq (v : L) :
    D.periodicRealDirection v = (D.rationalDirectionPeriod v : ℝ) • rationalLieInclusion v := by
  simp only [periodicRealDirection, Nat.cast_smul_eq_nsmul, map_nsmul]

theorem periodicRealDirection_mem_lattice (v : L) :
    (⟨D.periodicRealDirection v⟩ : D.RealGroup) ∈ D.realLattice := by
  exact Subgroup.mem_map.mpr ⟨⟨(D.rationalDirectionPeriod v : ℚ) • v⟩,
    D.rationalDirectionPeriod_mem_lattice v, rfl⟩

theorem periodicRealDirection_central (v : L) (hv : v ∈ D.filtration.layer s)
    (w : ℝ ⊗[ℚ] L) : ⁅D.periodicRealDirection v, w⁆ = 0 := by
  rw [D.periodicRealDirection_eq, smul_lie,
    rationalLieInclusion_central v (D.filtration.top_layer_central hv), smul_zero]

theorem periodicRealDirection_mem_top (v : L) (hv : v ∈ D.filtration.layer s) :
    (⟨D.periodicRealDirection v⟩ : D.RealGroup) ∈ D.filtration.realification.subgroup s := by
  change (1 : ℝ) ⊗ₜ[ℚ] ((D.rationalDirectionPeriod v : ℚ) • v) ∈
    (D.filtration.layer s).baseChange ℝ
  exact Submodule.tmul_mem_baseChange_of_mem 1 ((D.filtration.layer s).smul_mem _ hv)

theorem periodicRealDirection_span {ι : Type*} (v : ι → L) :
    Submodule.span ℝ (Set.range (fun i => D.periodicRealDirection (v i))) =
      Submodule.span ℝ (Set.range (fun i => rationalLieInclusion (v i))) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change D.periodicRealDirection (v i) ∈ _
    rw [D.periodicRealDirection_eq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have h := Submodule.smul_mem
      (Submodule.span ℝ (Set.range (fun i => D.periodicRealDirection (v i))))
      (D.rationalDirectionPeriod (v i) : ℝ)⁻¹ (Submodule.subset_span ⟨i, rfl⟩)
    change (D.rationalDirectionPeriod (v i) : ℝ)⁻¹ • D.periodicRealDirection (v i) ∈ _ at h
    rw [D.periodicRealDirection_eq, smul_smul, inv_mul_cancel₀, one_smul] at h
    · exact h
    · exact_mod_cast (D.rationalDirectionPeriod_pos (v i)).ne'

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d)
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

noncomputable def centralRationalCircle (v : L) (hv : v ∈ D.filtration.layer s) :
    let := D.metricSpace
    IsometricCircleAction D.Space := by
  let := D.metricSpace
  exact centralBCHCircleAction (D.basis.baseChange ℝ) D.realLattice
    D.realLattice_closed_discrete.1 (D.periodicRealDirection v)
    (D.periodicRealDirection_central v hv) (D.periodicRealDirection_mem_lattice v)

theorem centralRationalCircle_act_coe (v : L) (hv : v ∈ D.filtration.layer s)
    (r : ℝ) (x : D.Space) :
    let := D.metricSpace
    (D.centralRationalCircle v hv).act (r : CircleFourier.Circle) x =
      realBCHLine (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
        (D.periodicRealDirection v) r • x := by
  let := D.metricSpace
  exact centralBCHCircleAction_act_coe (D.basis.baseChange ℝ) D.realLattice
    D.realLattice_closed_discrete.1 (D.periodicRealDirection v)
    (D.periodicRealDirection_central v hv) (D.periodicRealDirection_mem_lattice v) r x

theorem centralRationalCircle_commutes (v w : L)
    (hv : v ∈ D.filtration.layer s) (hw : w ∈ D.filtration.layer s) :
    let := D.metricSpace
    (D.centralRationalCircle v hv).Commutes (D.centralRationalCircle w hw) := by
  let := D.metricSpace
  exact centralBCHCircleAction_commutes (D.basis.baseChange ℝ) D.realLattice
    D.realLattice_closed_discrete.1 (D.periodicRealDirection v) (D.periodicRealDirection w)
    (D.periodicRealDirection_central v hv) (D.periodicRealDirection_central w hw)
    (D.periodicRealDirection_mem_lattice v) (D.periodicRealDirection_mem_lattice w)

theorem exists_centralRationalCircle_frequency (v : L) (hv : v ∈ D.filtration.layer s)
    (eta : L →ₗ[ℚ] ℚ) (f : D.Space → ℂ)
    (hf : ∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup s → ∀ x,
      f (z • x) = character ((realifyFunctional eta z.coord : ℝ) : CircleFourier.Circle) * f x) :
    let := D.metricSpace
    ∃ n : ℤ,
      (∀ t x, f ((D.centralRationalCircle v hv).act t x) = character (n • t) * f x) ∧
      (eta v = 0 → n = 0) := by
  classical
  let := D.metricSpace
  by_cases hz : ∀ x, f x = 0
  · exact ⟨0, fun t x => by simp [hz], fun _ => rfl⟩
  push Not at hz
  obtain ⟨n, hn⟩ := vertical_frequency_integral_on_lattice D.filtration D.realLattice eta f hf hz
    (⟨D.periodicRealDirection v⟩ : D.RealGroup)
    (D.periodicRealDirection_mem_top v hv) (D.periodicRealDirection_mem_lattice v)
  refine ⟨n, ?_, ?_⟩
  · intro t x
    obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective t
    rw [D.centralRationalCircle_act_coe]
    have hr : realBCHLine (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
        (D.periodicRealDirection v) r ∈ D.filtration.realification.subgroup s := by
      change r • D.periodicRealDirection v ∈ D.filtration.realLayer s
      exact (D.filtration.realLayer s).smul_mem r (D.periodicRealDirection_mem_top v hv)
    rw [hf _ hr]
    apply congrArg (fun z : CircleFourier.Circle => character z * f x)
    change ((realifyFunctional eta (r • D.periodicRealDirection v) : ℝ) : CircleFourier.Circle) =
      n • (r : CircleFourier.Circle)
    rw [map_smul, hn, ← AddCircle.coe_zsmul]
    congr 1
    simp only [smul_eq_mul, zsmul_eq_mul, mul_comm]
  · intro heta
    have hzero : realifyFunctional eta (D.periodicRealDirection v) = 0 := by
      simp [periodicRealDirection, realifyFunctional_tmul, heta]
    have hn0 : (n : ℝ) = 0 := hn.symm.trans hzero
    exact_mod_cast hn0

end Erdos3.RationalFilteredNilmanifold

end

end OAI

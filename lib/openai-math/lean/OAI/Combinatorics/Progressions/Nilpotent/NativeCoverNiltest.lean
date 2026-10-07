import OAI.Combinatorics.Progressions.Linear.SplitCoverProjection

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
  (T : D.Niltest w) (Λ : Subgroup D.filtration.Group) (m : ℕ) (hm : 0 < m)
  (hin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates D.basis Λ)
  (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid m) (hΛ : Λ ≤ D.lattice)

noncomputable def onSublattice : (D.withLattice Λ m hm hin hout).Niltest w where
  orbit := T.orbit
  observable := T.observable ∘ sublatticeProjection D (D.withLattice Λ m hm hin hout) hΛ
  normBound := T.normBound
  lipBound := T.lipBound
  norm_le _ := T.norm_le _
  lipschitz := sublattice_pullback_lipschitz D (D.withLattice Λ m hm hin hout) hΛ rfl
    T.observable T.lipschitz

theorem onSublattice_orbit : (T.onSublattice Λ m hm hin hout hΛ).orbit = T.orbit := rfl

theorem onSublattice_normBound :
    (T.onSublattice Λ m hm hin hout hΛ).normBound = T.normBound := rfl

theorem onSublattice_lipBound :
    (T.onSublattice Λ m hm hin hout hΛ).lipBound = T.lipBound := rfl

theorem onSublattice_eval (x : σ → ℤ) :
    (T.onSublattice Λ m hm hin hout hΛ).eval x = T.eval x := rfl

theorem onSublattice_evalCyclic (N : ℕ) [NeZero N] (x : σ → ZMod N) :
    (T.onSublattice Λ m hm hin hout hΛ).evalCyclic N x = T.evalCyclic N x := rfl

theorem onSublattice_complexity {p : ℝ} (hT : T.ComplexityLE p)
    (hD : (D.withLattice Λ m hm hin hout).GeometryComplexityLE p) :
    (T.onSublattice Λ m hm hin hout hΛ).ComplexityLE p := ⟨hD, hT.2⟩

theorem onSublattice_unit_interval (hT : T.UnitIntervalValued) :
    (T.onSublattice Λ m hm hin hout hΛ).UnitIntervalValued := fun _ => hT _

theorem onSublattice_vertical (χ : D.RealGroup → CircleFourier.Circle)
    (hT : ∀ z ∈ D.filtration.realification.subgroup s, ∀ x,
      T.observable (z • x) = CircleFourier.character (χ z) * T.observable x)
    (z : D.RealGroup) (hz : z ∈ D.filtration.realification.subgroup s)
    (x : (D.withLattice Λ m hm hin hout).Space) :
    (T.onSublattice Λ m hm hin hout hΛ).observable (z • x) =
      CircleFourier.character (χ z) * (T.onSublattice Λ m hm hin hout hΛ).observable x := by
  induction x using Quotient.inductionOn with
  | _ x => exact hT z hz (QuotientGroup.mk x)

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open NilpotentLieFiltration
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
    (T : D.Niltest w) (E : RationalFilteredNilmanifold L s d)
    (hfil : E.filtration = D.filtration) (hb : E.basis = D.basis)
    (hΛ : E.lattice ≤ D.lattice)

noncomputable def onNativeCover : E.Niltest w where
  orbit := polynomialOrbitOfLog T.orbit.log (by rw [hfil]; exact T.orbit.adapted)
  observable := T.observable ∘ sublatticeProjection D E hΛ
  normBound := T.normBound
  lipBound := T.lipBound
  norm_le _ := T.norm_le _
  lipschitz := sublattice_pullback_lipschitz D E hΛ hb T.observable T.lipschitz

@[simp] theorem onNativeCover_log :
    (T.onNativeCover E hfil hb hΛ).orbit.log = T.orbit.log := rfl

@[simp] theorem onNativeCover_normBound :
    (T.onNativeCover E hfil hb hΛ).normBound = T.normBound := rfl

@[simp] theorem onNativeCover_lipBound :
    (T.onNativeCover E hfil hb hΛ).lipBound = T.lipBound := rfl

@[simp] theorem onNativeCover_eval (x : σ → ℤ) :
    (T.onNativeCover E hfil hb hΛ).eval x = T.eval x := rfl

@[simp] theorem onNativeCover_evalCyclic (N : ℕ) [NeZero N] (x : σ → ZMod N) :
    (T.onNativeCover E hfil hb hΛ).evalCyclic N x = T.evalCyclic N x := rfl

theorem onNativeCover_complexity {p : ℝ} (hT : T.ComplexityLE p)
    (hE : E.GeometryComplexityLE p) :
    (T.onNativeCover E hfil hb hΛ).ComplexityLE p := ⟨hE, hT.2⟩

theorem onNativeCover_unit_interval (hT : T.UnitIntervalValued) :
    (T.onNativeCover E hfil hb hΛ).UnitIntervalValued := fun _ => hT _

theorem onNativeCover_vertical (χ : D.RealGroup → CircleFourier.Circle)
    (hT : ∀ z ∈ D.filtration.realification.subgroup s, ∀ x,
      T.observable (z • x) = CircleFourier.character (χ z) * T.observable x)
    (z : D.RealGroup) (hz : z ∈ D.filtration.realification.subgroup s)
    (x : E.Space) :
    (T.onNativeCover E hfil hb hΛ).observable (z • x) =
      CircleFourier.character (χ z) * (T.onNativeCover E hfil hb hΛ).observable x := by
  induction x using Quotient.inductionOn with
  | _ x => exact hT z hz (QuotientGroup.mk x)

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI

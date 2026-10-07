/- Modified for ProveIt: Use IsModuleTopology.topologicalAddGroup on Lean 4.32; statements unchanged. -/
import OAI.Combinatorics.Progressions.Estimates.AllocatedMarkedDictionaryRecovery

namespace OAI

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

attribute [local instance_reducible] optionLieSpace

def DiagramNativeExternalNetConclusion (s t k : ℕ)
{H M L₀ ι : Type u} [Fintype ι] [DecidableEq ι]
      {L : ι → Type u}
      [LieRing H] [LieAlgebra ℚ H] [LieRing M] [LieAlgebra ℚ M]
      [LieRing L₀] [LieAlgebra ℚ L₀] [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [TopologicalSpace (ℝ ⊗[ℚ] H)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] H)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] H)] [T2Space (ℝ ⊗[ℚ] H)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      [TopologicalSpace (ℝ ⊗[ℚ] L₀)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₀)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₀)] [T2Space (ℝ ⊗[ℚ] L₀)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {e f d₀ : ℕ} {d : ι → ℕ}
      (E : RationalFilteredNilmanifold H t e) (D : RationalFilteredNilmanifold M t f)
      (Q : RationalFilteredNilmanifold L₀ s d₀)
      (F : ∀ i, RationalFilteredNilmanifold (L i) t (d i))
      (φ : H →ₗ⁅ℚ⁆ M) (ψ₀ : H →ₗ⁅ℚ⁆ L₀) (ψ : ∀ i, H →ₗ⁅ℚ⁆ L i) (p cost : ℝ) (q : ℕ) : Prop :=
      let Z₀ := pi F
      letI := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, L i))
      letI := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i, L i))
      letI := realification_moduleTopology_t2 Z₀.basis
      ∃ Q' : RationalFilteredNilmanifold L₀ s d₀,
        Q'.filtration = Q.filtration ∧ Q'.basis = Q.basis ∧ Q'.lattice ≤ Q.lattice ∧
        Q'.GeometryComplexityLE cost ∧
        ∃ Z : RationalFilteredNilmanifold (∀ i, L i) t (Fintype.card (Σ i, Fin (d i))),
          Z.filtration = Z₀.filtration ∧ Z.basis = Z₀.basis ∧ Z.lattice ≤ Z₀.lattice ∧
          Z.GeometryComplexityLE cost ∧
          ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp cost ∧
          letI := Q'.metricSpace
          letI := Z.metricSpace
          let diagram := fun x : E.RealGroup =>
            ((QuotientGroup.mk (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                (hM := Q'.filtration.lowerCentralSeries_eq_bot) ψ₀ x) : Q'.Space),
              (QuotientGroup.mk (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                (hM := Z.filtration.lowerCentralSeries_eq_bot) (liePiMap ψ) x) : Z.Space))
          ∀ {O R IO : Type*} [Fintype R] [Fintype IO]
            (S : O → D.Space → ℂ) (oc : IO → O) (r : R → D.RealGroup)
            (ℓ B : ℝ≥0) {ε : ℝ},
            (ℓ : ℝ) ≤ Real.exp p → 1 ≤ B → (B : ℝ) ≤ Real.exp ((p + 2) ^ k) →
            0 < ε → 1 / ε ≤ Real.exp p →
            (Fintype.card IO : ℝ) ≤ Real.exp p → (Fintype.card R : ℝ) ≤ Real.exp p →
            (∀ o, letI := D.metricSpace; LipschitzWith ℓ (S o)) →
            (∀ o x, (S o x).im = 0 ∧ 0 ≤ (S o x).re ∧ (S o x).re ≤ 1) →
            (∀ o, ∃ i, ∀ x, ‖S o x - S (oc i) x‖ ≤ ε / 3) →
            (∀ j, (D.basis.baseChange ℝ).equivFun (r j).coord ∈ realDenominatorGrid q) →
            let A := coordinateBox (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
              (D.basis.baseChange ℝ) B
            let frozen := fun o (a : A) j (x : E.RealGroup) =>
              S o (QuotientGroup.mk (a.val * realificationMap
                (hnil := E.filtration.lowerCentralSeries_eq_bot)
                (hM := D.filtration.lowerCentralSeries_eq_bot) φ x * r j))
            ∃ n : ℕ, (n : ℝ) ≤ Real.exp cost ∧
              ∃ centers : Fin n → Q'.Space → ℂ,
                (∀ i, LipschitzWith K (centers i)) ∧
                (∀ i y, (centers i y).im = 0 ∧ 0 ≤ (centers i y).re ∧ (centers i y).re ≤ 1) ∧
                (∀ i y, ‖centers i y‖ ≤ 1) ∧
                (∀ o a j x, positiveImageSlice diagram K (frozen o a j)
                  (diagram x).2 (diagram x).1 = frozen o a j x) ∧
                ∀ o a j z, ∃ i, ∀ y,
                  ‖positiveImageSlice diagram K (frozen o a j) z y - centers i y‖ ≤ ε

end Erdos3.RationalFilteredNilmanifold

end

section

universe u uO uR uIO uX

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

attribute [local instance_reducible] optionLieSpace

theorem DiagramNativeExternalNetConclusion.exists_physical_family (s t k : ℕ)
{H M L₀ ι : Type u} [Fintype ι] [DecidableEq ι]
      {L : ι → Type u}
      [LieRing H] [LieAlgebra ℚ H] [LieRing M] [LieAlgebra ℚ M]
      [LieRing L₀] [LieAlgebra ℚ L₀] [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [TopologicalSpace (ℝ ⊗[ℚ] H)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] H)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] H)] [T2Space (ℝ ⊗[ℚ] H)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      [TopologicalSpace (ℝ ⊗[ℚ] L₀)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₀)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₀)] [T2Space (ℝ ⊗[ℚ] L₀)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {e f d₀ : ℕ} {d : ι → ℕ}
      (E : RationalFilteredNilmanifold H t e) (D : RationalFilteredNilmanifold M t f)
      (Q : RationalFilteredNilmanifold L₀ s d₀)
      (F : ∀ i, RationalFilteredNilmanifold (L i) t (d i))
      (φ : H →ₗ⁅ℚ⁆ M) (ψ₀ : H →ₗ⁅ℚ⁆ L₀) (ψ : ∀ i, H →ₗ⁅ℚ⁆ L i) (p cost : ℝ) (q : ℕ)
    (h : DiagramNativeExternalNetConclusion.{u, uO, uR, uIO} s t k E D Q F φ ψ₀ ψ p cost q) :
      let Z₀ := pi F
      letI := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, L i))
      letI := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i, L i))
      letI := realification_moduleTopology_t2 Z₀.basis
      ∃ Q' : RationalFilteredNilmanifold L₀ s d₀,
        Q'.filtration = Q.filtration ∧ Q'.basis = Q.basis ∧ Q'.lattice ≤ Q.lattice ∧
        Q'.GeometryComplexityLE cost ∧
        ∃ Z : RationalFilteredNilmanifold (∀ i, L i) t (Fintype.card (Σ i, Fin (d i))),
          Z.filtration = Z₀.filtration ∧ Z.basis = Z₀.basis ∧ Z.lattice ≤ Z₀.lattice ∧
          Z.GeometryComplexityLE cost ∧
          ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp cost ∧
          letI := Q'.metricSpace
          letI := Z.metricSpace
          let diagram := fun x : E.RealGroup =>
            ((QuotientGroup.mk (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                (hM := Q'.filtration.lowerCentralSeries_eq_bot) ψ₀ x) : Q'.Space),
              (QuotientGroup.mk (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                (hM := Z.filtration.lowerCentralSeries_eq_bot) (liePiMap ψ) x) : Z.Space))
          ∀ {O : Type uO} {R : Type uR} {IO : Type uIO} [Fintype R] [Fintype IO]
            (S : O → D.Space → ℂ) (oc : IO → O) (r : R → D.RealGroup)
            (ℓ B : ℝ≥0) {ε : ℝ},
            (ℓ : ℝ) ≤ Real.exp p → 1 ≤ B → (B : ℝ) ≤ Real.exp ((p + 2) ^ k) →
            0 < ε → 1 / ε ≤ Real.exp p →
            (Fintype.card IO : ℝ) ≤ Real.exp p → (Fintype.card R : ℝ) ≤ Real.exp p →
            (∀ o, letI := D.metricSpace; LipschitzWith ℓ (S o)) →
            (∀ o x, (S o x).im = 0 ∧ 0 ≤ (S o x).re ∧ (S o x).re ≤ 1) →
            (∀ o, ∃ i, ∀ x, ‖S o x - S (oc i) x‖ ≤ ε / 3) →
            (∀ j, (D.basis.baseChange ℝ).equivFun (r j).coord ∈ realDenominatorGrid q) →
            let A := coordinateBox (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
              (D.basis.baseChange ℝ) B
            let frozen := fun o (a : A) j (x : E.RealGroup) =>
              S o (QuotientGroup.mk (a.val * realificationMap
                (hnil := E.filtration.lowerCentralSeries_eq_bot)
                (hM := D.filtration.lowerCentralSeries_eq_bot) φ x * r j))
            ∃ n : ℕ, (n : ℝ) ≤ Real.exp cost ∧
              ∃ centers : Fin n → Q'.Space → ℂ,
                (∀ i, LipschitzWith K (centers i)) ∧
                (∀ i y, (centers i y).im = 0 ∧ 0 ≤ (centers i y).re ∧ (centers i y).re ≤ 1) ∧
                (∀ i y, ‖centers i y‖ ≤ 1) ∧
                (∀ o a j x, positiveImageSlice diagram K (frozen o a j)
                  (diagram x).2 (diagram x).1 = frozen o a j x) ∧
                (∀ o a j z, ∃ i, ∀ y,
                  ‖positiveImageSlice diagram K (frozen o a j) z y - centers i y‖ ≤ ε) ∧
                ∀ {X : Type uX} [Nonempty X]
                  (observableAt : X → O) (leftAt : X → A) (rightAt : X → R)
                  (externalAt : X → Z.Space),
                  let physicalFunction := fun x y => positiveImageSlice diagram K
                    (frozen (observableAt x) (leftAt x) (rightAt x)) (externalAt x) y
                  (∀ x, LipschitzWith K (physicalFunction x)) ∧
                  (∀ x y, (physicalFunction x y).im = 0 ∧
                    0 ≤ (physicalFunction x y).re ∧ (physicalFunction x y).re ≤ 1) ∧
                  (∀ x y, ‖physicalFunction x y‖ ≤ 1) ∧
                  (∀ x, ∃ i, ∀ y, ‖physicalFunction x y - centers i y‖ ≤ ε) ∧
                  ∀ x (source : E.RealGroup), externalAt x = (diagram source).2 →
                    physicalFunction x (diagram source).1 =
                      frozen (observableAt x) (leftAt x) (rightAt x) source := by
  let Z₀ := pi F
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, L i))
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i, L i))
  let := realification_moduleTopology_t2 Z₀.basis
  obtain ⟨Q', hQF, hQb, hQle, hQgeom, Z, hZF, hZb, hZle, hZgeom,
    K, hK, hnet⟩ := h
  refine ⟨Q', hQF, hQb, hQle, hQgeom, Z, hZF, hZb, hZle, hZgeom, K, hK, ?_⟩
  let := Q'.metricSpace
  let := Z.metricSpace
  intro diagram O J IO _ _ S oc r ℓ Bbox ε hℓ hB hBbound hε hεinv hIO hJ hS hpositive hO hr
  obtain ⟨n, hn, centers, hLip, hunit, hcap, heval, hcover⟩ :=
    hnet (O := O) (R := J) (IO := IO) S oc r ℓ Bbox hℓ hB hBbound hε hεinv hIO hJ
      hS hpositive hO hr
  refine ⟨n, hn, centers, hLip, hunit, hcap, heval, hcover, ?_⟩
  intro X _ observableAt leftAt rightAt externalAt physicalFunction
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact positiveImageSlice_lipschitz diagram K _
      (fun source => (hpositive (observableAt x) _).2.1) (externalAt x)
  · intro x y
    exact positiveImageExtension_unit_interval diagram K _ (y, externalAt x)
  · intro x y
    exact positiveImageExtension_norm_le_one diagram K _ (y, externalAt x)
  · intro x
    exact hcover (observableAt x) (leftAt x) (rightAt x) (externalAt x)
  · intro x source hexternal
    change positiveImageSlice diagram K _ (externalAt x) (diagram source).1 = _
    rw [hexternal]
    exact heval (observableAt x) (leftAt x) (rightAt x) source

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v w z

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

attribute [local instance_reducible] optionLieSpace

theorem DiagramNativeExternalNetConclusion.mono (s t k : ℕ)
{H M L₀ ι : Type u} [Fintype ι] [DecidableEq ι]
      {L : ι → Type u}
      [LieRing H] [LieAlgebra ℚ H] [LieRing M] [LieAlgebra ℚ M]
      [LieRing L₀] [LieAlgebra ℚ L₀] [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [TopologicalSpace (ℝ ⊗[ℚ] H)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] H)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] H)] [T2Space (ℝ ⊗[ℚ] H)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      [TopologicalSpace (ℝ ⊗[ℚ] L₀)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₀)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₀)] [T2Space (ℝ ⊗[ℚ] L₀)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {e f d₀ : ℕ} {d : ι → ℕ}
      (E : RationalFilteredNilmanifold H t e) (D : RationalFilteredNilmanifold M t f)
      (Q : RationalFilteredNilmanifold L₀ s d₀)
      (F : ∀ i, RationalFilteredNilmanifold (L i) t (d i))
      (φ : H →ₗ⁅ℚ⁆ M) (ψ₀ : H →ₗ⁅ℚ⁆ L₀) (ψ : ∀ i, H →ₗ⁅ℚ⁆ L i) {p p' cost cost' : ℝ} (q : ℕ)
    (h : DiagramNativeExternalNetConclusion.{u, v, w, z} s t k E D Q F φ ψ₀ ψ p cost q)
    (hp' : 0 ≤ p') (hpp : p' ≤ p) (hcost : cost ≤ cost') :
    DiagramNativeExternalNetConclusion.{u, v, w, z} s t k E D Q F φ ψ₀ ψ p' cost' q := by
  let Z₀ := pi F
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, L i))
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i, L i))
  let := realification_moduleTopology_t2 Z₀.basis
  obtain ⟨Q', hQF, hQb, hQle, hQgeom, Z, hZF, hZb, hZle, hZgeom, K, hK, hnet⟩ := h
  refine ⟨Q', hQF, hQb, hQle, hQgeom.mono Q' hcost,
    Z, hZF, hZb, hZle, hZgeom.mono Z hcost,
    K, hK.trans (Real.exp_le_exp.mpr hcost), ?_⟩
  let := Q'.metricSpace
  let := Z.metricSpace
  intro diagram O R IO _ _ S oc r ℓ B ε hℓ hB hBbound hε hεinv hIO hR hS hpositive hO hr
  have hexp := Real.exp_le_exp.mpr hpp
  have hBbound' : (B : ℝ) ≤ Real.exp ((p + 2) ^ k) := hBbound.trans
    (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith) (by linarith) k))
  obtain ⟨n, hn, centers, hLip, hunit, hcap, heval, hcover⟩ :=
    hnet (O := O) (R := R) (IO := IO) S oc r ℓ B (hℓ.trans hexp) hB hBbound' hε
      (hεinv.trans hexp) (hIO.trans hexp) (hR.trans hexp) hS hpositive hO hr
  exact ⟨n, hn.trans (Real.exp_le_exp.mpr hcost), centers, hLip, hunit, hcap, heval, hcover⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI

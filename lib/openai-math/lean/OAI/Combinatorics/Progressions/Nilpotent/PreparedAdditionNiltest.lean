import OAI.Combinatorics.Progressions.Estimates.DilationCost
import OAI.Combinatorics.Progressions.Geometry.NativeTripleObservableMetric

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

variable {σ L I : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  [Fintype I] {s d r n : ℕ} {D : RationalFilteredNilmanifold L (s + 1) d} {bound : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (M : D.MultidegreeStructure bound) (i : σ) (hi : bound i = 1) (hs : ∑ j, bound j = s + 1)
  (E : RationalFilteredNilmanifold (M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) (s + 1) r)
  (hEF : E.filtration = M.filtration.additiveTripleFiltration i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))
  (hEL : E.lattice = M.additiveTripleLattice i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))]
  [T2Space (ℝ ⊗[ℚ] M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))]
  (Q : RationalFilteredNilmanifold ((M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  (hQF : Q.filtration = E.filtration.quotientTop)
  (hQL : Q.lattice = E.lattice.map (E.filtration.quotientStepHom
    (E.filtration.layerIdeal (s + 1)) (t := s) le_rfl))
  [TopologicalSpace (ℝ ⊗[ℚ] ((M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) ⧸ E.filtration.layerIdeal (s + 1)))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] ((M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) ⧸ E.filtration.layerIdeal (s + 1)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] ((M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) ⧸ E.filtration.layerIdeal (s + 1)))]
  [T2Space (ℝ ⊗[ℚ] ((M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) ⧸ E.filtration.layerIdeal (s + 1)))]

include hs hEF hQF hQL

theorem exists_addition_niltest_of_data {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ j k, RationalHeightLE
      (Q.basis.repr (lieQuotientMap (E.filtration.layerIdeal (s + 1)) (E.basis k)) j) H)
    (hstructure : ∀ a b c, RationalHeightLE (lieStructureConstants Q.basis a b c) H)
    {p : ℝ} (V : D.UnitVerticalObservable (M.realSubgroup bound) I p)
    (g : M.filtration.realification.PolynomialOrbit) (ε γ : D.RealGroup)
    (hγ : γ ∈ D.realLattice) (hfactor : M.filtration.realification.polynomialOrbitEval 0 g = ε * γ)
    (a : Fin 3 → I) (A : ℝ≥0)
    (hLip : letI := E.metricSpace
      LipschitzWith A (M.tripleObservable i hi.le _ (omittedCoordinateWeight_le_one i)
        E hEL ε (fun j => V.observable (a j)))) :
    ∃ T : Q.Niltest (fun _ : Option σ => 1), T.normBound = 1 ∧
      T.lipBound = rationalReconstructionLipschitzBound s r n H A 1 ∧
      Q.filtration.realification.polynomialOrbitEval _ 0 T.orbit = 1 ∧
      ∀ x, T.eval x = coordinateAdditionProduct
        (fun j y => V.observable j (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval y g)))
        a i x := by
  obtain ⟨q, hq0, hq⟩ := M.exists_native_addition_orbit i hi.le E hEF g ε γ hγ hfactor
  obtain ⟨T, hTnorm, hTlip, hTorbit, hTval⟩ := M.exists_unitVertical_triple_quotient_niltest
    i hi hs E hEF hEL Q hQL hQF hH hentries hstructure V ε a A hLip q
  refine ⟨T, hTnorm, hTlip, ?_, ?_⟩
  · rw [hTorbit, E.topQuotientOrbit_eval Q hQF, hq0, map_one]
  · intro x
    rw [hTval]
    exact M.tripleObservable_of_addition_values i hi.le E hEL g ε q hq
      (fun j => V.observable (a j)) x

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

variable {σ L I : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  [Fintype I] {s d r n : ℕ} {D : RationalFilteredNilmanifold L (s + 1) d} {bound : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (M : D.MultidegreeStructure bound) (i : σ) (hi : bound i = 1) (hs : ∑ j, bound j = s + 1)
  (E : RationalFilteredNilmanifold (M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) (s + 1) r)
  (hEF : E.filtration = M.filtration.additiveTripleFiltration i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))
  (hEL : E.lattice = M.additiveTripleLattice i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))]
  [T2Space (ℝ ⊗[ℚ] M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))]
  (Q : RationalFilteredNilmanifold ((M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  (hQF : Q.filtration = E.filtration.quotientTop)
  (hQL : Q.lattice = E.lattice.map (E.filtration.quotientStepHom
    (E.filtration.layerIdeal (s + 1)) (t := s) le_rfl))
  [TopologicalSpace (ℝ ⊗[ℚ] ((M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) ⧸ E.filtration.layerIdeal (s + 1)))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] ((M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) ⧸ E.filtration.layerIdeal (s + 1)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] ((M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) ⧸ E.filtration.layerIdeal (s + 1)))]
  [T2Space (ℝ ⊗[ℚ] ((M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) ⧸ E.filtration.layerIdeal (s + 1)))]

include hs hEF hEL hQF hQL

theorem exists_prepared_addition_niltest
    {p : ℝ} (hp : 0 ≤ p)
    (hD : D.GeometryComplexityLE (MultilinearityBudget.ambient p))
    (hE : E.GeometryComplexityLE (MultilinearityBudget.ambient p))
    (he : ∀ j a k, rationalLogHeight (D.basis.repr
      (M.filtration.additiveTripleProjection i hi.le _ (omittedCoordinateWeight_le_one i) j (E.basis a)) k) ≤
        MultilinearityBudget.ambient p)
    (hQ : Q.GeometryComplexityLE (MultilinearityBudget.quotient p))
    (hq : ∀ j k, rationalLogHeight
      (Q.basis.repr (lieQuotientMap (E.filtration.layerIdeal (s + 1)) (E.basis k)) j) ≤
        MultilinearityBudget.quotient p)
    (V : D.UnitVerticalObservable (M.realSubgroup bound) I p)
    (g : M.filtration.realification.PolynomialOrbit) (C : ℕ) (ε γ : D.RealGroup)
    (hγ : γ ∈ D.realLattice) (hfactor : M.filtration.realification.polynomialOrbitEval 0 g = ε * γ)
    (A : ℝ≥0) (hA : (A : ℝ) ≤ Real.exp ((p + C) ^ C))
    (hε : letI := D.metricSpace; LipschitzWith A (fun x : D.Space => ε • x))
    (a : Fin 3 → I) :
    ∃ T : Q.Niltest (fun _ : Option σ => 1), T.normBound = 1 ∧
      T.ComplexityLE (MultilinearityBudget.total C (MultilinearityBudget.reconstructionExponent s) p) ∧
      Q.filtration.realification.polynomialOrbitEval _ 0 T.orbit = 1 ∧
      ∀ x, T.eval x = coordinateAdditionProduct
        (fun j y => V.observable j (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval y g)))
        a i x := by
  let H := ⌈Real.exp (MultilinearityBudget.quotient p)⌉₊
  let A₃ : ℝ≥0 := 3 * (V.lipBound * (A *
    ⟨Real.exp ((MultilinearityBudget.ambient p + 3) ^ 2), (Real.exp_pos _).le⟩))
  have hLip : letI := E.metricSpace
      LipschitzWith A₃ (M.tripleObservable i hi.le _ (omittedCoordinateWeight_le_one i)
        E hEL ε (fun j => V.observable (a j))) :=
    M.tripleObservable_lipschitz i hi.le _ (omittedCoordinateWeight_le_one i) E hEL
      (MultilinearityBudget.ambient_bounds hp).1 hD hE he ε (fun j => V.observable (a j))
      V.lipBound A (fun j x => V.norm (a j) x) (fun j => V.lipschitz (a j)) hε
  obtain ⟨T, hTnorm, hTlip, hTzero, hTeval⟩ := M.exists_addition_niltest_of_data
    i hi hs E hEF hEL Q hQF hQL (one_le_ceil_exp _)
    (fun j k => rationalHeightLE_ceil_exp (hq j k))
    (fun j k l => rationalHeightLE_ceil_exp (hQ.2.2.1 j k l))
    V g ε γ hγ hfactor a A₃ hLip
  have hR := MultilinearityBudget.reconstruction_bounds C hp
  have hHb : (H : ℝ) ≤ Real.exp (MultilinearityBudget.reconstruction C p) :=
    (ceil_exp_le_exp_add_one (MultilinearityBudget.quotient_bounds hp).1).trans
      (Real.exp_le_exp.mpr hR.2.2.1)
  have hA₃ : (A₃ : ℝ) ≤ Real.exp (MultilinearityBudget.reconstruction C p) := by
    change (3 : ℝ) * (V.lipBound * (A * Real.exp ((MultilinearityBudget.ambient p + 3) ^ 2))) ≤ _
    exact (MultilinearityBudget.observable_bound C p V.lipBound A V.lip_bound hA).trans
      (Real.exp_le_exp.mpr hR.2.2.2)
  exact ⟨T, hTnorm, MultilinearityBudget.niltest_complexity Q T C r H A₃ hp hQ
    (hE.1.trans hR.2.1) hHb hA₃ hTnorm hTlip, hTzero, hTeval⟩

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI

import OAI.Combinatorics.Progressions.Estimates.DilationCost
import OAI.Combinatorics.Progressions.Estimates.NativeDilationDescent
import OAI.Combinatorics.Progressions.Geometry.NativeDilationObservableMetric

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

variable {σ L I : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  [Fintype I] {s d r n : ℕ} {D : RationalFilteredNilmanifold L (s + 1) d} {bound : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (M : D.MultidegreeStructure bound) (q : ℤ) (hs : ∑ j, bound j = s + 1)
  (E : RationalFilteredNilmanifold (M.filtration.ordinary.dilationPairSubalgebra (q : ℚ)) (s + 1) r)
  (hEF : E.filtration = M.filtration.ordinary.dilationPairFiltration (q : ℚ))
  (hEL : E.lattice = M.dilationPairLattice (q : ℚ))
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.ordinary.dilationPairSubalgebra (q : ℚ))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.ordinary.dilationPairSubalgebra (q : ℚ))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.ordinary.dilationPairSubalgebra (q : ℚ))]
  [T2Space (ℝ ⊗[ℚ] M.filtration.ordinary.dilationPairSubalgebra (q : ℚ))]
  (Q : RationalFilteredNilmanifold
    ((M.filtration.ordinary.dilationPairSubalgebra (q : ℚ)) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  (hQF : Q.filtration = E.filtration.quotientTop)
  (hQL : Q.lattice = E.lattice.map
    (E.filtration.quotientStepHom (E.filtration.layerIdeal (s + 1)) (t := s) le_rfl))
  [TopologicalSpace (ℝ ⊗[ℚ]
    ((M.filtration.ordinary.dilationPairSubalgebra (q : ℚ)) ⧸ E.filtration.layerIdeal (s + 1)))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ]
    ((M.filtration.ordinary.dilationPairSubalgebra (q : ℚ)) ⧸ E.filtration.layerIdeal (s + 1)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ]
    ((M.filtration.ordinary.dilationPairSubalgebra (q : ℚ)) ⧸ E.filtration.layerIdeal (s + 1)))]
  [T2Space (ℝ ⊗[ℚ]
    ((M.filtration.ordinary.dilationPairSubalgebra (q : ℚ)) ⧸ E.filtration.layerIdeal (s + 1)))]

include hs hEF hEL hQF hQL

theorem exists_prepared_dilation_niltest {p : ℝ} (hp : 0 ≤ p)
    (hD : D.GeometryComplexityLE p) (hE : E.GeometryComplexityLE p)
    (hheight : ∀ j a k, rationalLogHeight
      (D.basis.repr (M.filtration.ordinary.dilationPairProjection (q : ℚ) j (E.basis a)) k) ≤ p)
    (hQ : Q.GeometryComplexityLE p)
    (hq : ∀ j k, rationalLogHeight
      (Q.basis.repr (lieQuotientMap (E.filtration.layerIdeal (s + 1)) (E.basis k)) j) ≤ p)
    (V : D.UnitVerticalObservable (M.realSubgroup bound) I p)
    (g : M.filtration.realification.PolynomialOrbit) (ε γ : D.RealGroup)
    (hγ : γ ∈ D.realLattice) (hfactor : M.filtration.realification.polynomialOrbitEval 0 g = ε * γ)
    (A : ℝ≥0) (hA : (A : ℝ) ≤ Real.exp p)
    (hε : letI := D.metricSpace; LipschitzWith A (fun x : D.Space => ε • x))
    (a₀ : I) (a : Fin (q ^ (s + 1)).natAbs → I) :
    ∃ T : Q.Niltest (fun _ : σ => 1), T.normBound = 1 ∧
      T.ComplexityLE (DilationBudget.total (s + 1) q (MultilinearityBudget.reconstructionExponent s) p) ∧
      Q.filtration.realification.polynomialOrbitEval _ 0 T.orbit = 1 ∧
      ∀ x, T.eval x =
        V.observable a₀ (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval
          (fun i => q * x i) g)) *
        star (signedTensorProduct (q ^ (s + 1)) (fun j => V.observable (a j)
          (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g)))) := by
  let H := ⌈Real.exp p⌉₊
  let B : ℝ≥0 := ((q ^ (s + 1)).natAbs + 1 : ℝ≥0) *
    (V.lipBound * (A * ⟨Real.exp ((p + 3) ^ 2), (Real.exp_pos _).le⟩))
  have hLip : letI := E.metricSpace
      LipschitzWith B (M.dilationObservable (q : ℚ) E hEL (q ^ (s + 1)) ε
        (V.observable a₀) (fun j => V.observable (a j))) :=
    M.dilationObservable_lipschitz (q : ℚ) E hEL hp hD hE hheight
      (q ^ (s + 1)) ε (V.observable a₀) (fun j => V.observable (a j)) V.lipBound A
      (V.norm a₀) (fun j => V.norm (a j)) (V.lipschitz a₀) (fun j => V.lipschitz (a j)) hε
  obtain ⟨T, hTn, hTl, hTzero, hTe⟩ := M.exists_dilation_niltest_of_data q hs E hEF hEL Q hQF hQL
    (one_le_ceil_exp p) (fun j k => rationalHeightLE_ceil_exp (hq j k))
    (fun j k l => rationalHeightLE_ceil_exp (hQ.2.2.1 j k l)) V g ε γ hγ hfactor a₀ a B hLip
  have hB : (B : ℝ) ≤ Real.exp (DilationBudget.reconstruction (s + 1) q p) := by
    change (((q ^ (s + 1)).natAbs : ℝ) + 1) *
      (V.lipBound * (A * Real.exp ((p + 3) ^ 2))) ≤ _
    exact DilationBudget.observable_bound (s + 1) q hp V.lipBound A V.lip_bound hA
  exact ⟨T, hTn, DilationBudget.niltest_complexity Q T (s + 1) q r H B hp hQ hE.1
    (ceil_exp_le_exp_add_one hp) hB hTn hTl, hTzero, hTe⟩

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI

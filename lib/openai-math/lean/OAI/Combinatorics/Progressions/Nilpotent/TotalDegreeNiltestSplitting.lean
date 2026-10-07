import OAI.Combinatorics.Progressions.Estimates.TwoDownsetPrecision
import OAI.Combinatorics.Progressions.Polynomial.NativeTotalDegreeMultifiltration

namespace OAI

section

namespace Erdos3

open Module VectorPolynomial RationalFilteredNilmanifold
open RationalFilteredNilmanifold.MultidegreeStructure
open scoped TensorProduct BigOperators NNReal

theorem exists_totalDegree_niltest_splitting (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} {D : RationalFilteredNilmanifold L s d} {p : ℝ}
      (T : D.Niltest (fun _ : Fin 2 => 1)), T.ComplexityLE p → T.normBound ≤ 1 →
      ∀ epsilon : ℝ, 0 < epsilon → 1 / epsilon ≤ Real.exp ((p + 2) ^ a) →
      Nonempty (NativeTwoVariableSplit s d ((p + C) ^ C) epsilon T.eval) := by
  obtain ⟨C, hC, hsplit⟩ := exists_two_downset_splitting s (2 * s) a
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D p T hT hnorm epsilon hepsilon hscale
  classical
  let M := D.totalDegreeMultidegree (Fin 2) hT.1
  let J := totalDegreeSplitDownset s
  have hJ : ∀ b, IsLowerSet (J b) := totalDegreeSplitDownset_lower s
  let K := fun b => M.filtration.positivePolynomialAlgebra ⧸
    restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J b) (hJ b)
  let : ∀ b, TopologicalSpace (ℝ ⊗[ℚ] K b) := fun _ => moduleTopology ℝ _
  let : ∀ b, IsTopologicalAddGroup (ℝ ⊗[ℚ] K b) :=
    fun _ => IsModuleTopology.isTopologicalAddGroup ℝ _
  let : ∀ b, T2Space (ℝ ⊗[ℚ] K b) :=
    fun b => realification_moduleTopology_t2 (M.positivePolynomialDownsetFinBasis (J b) (hJ b) p)
  let g := D.filtration.realTotalDegreeOrbit T.orbit
  have hsum : (∑ _ : Fin 2, s) = 2 * s := by simp
  have hM : M.ComplexityLE p := D.totalDegreeMultidegree_complexity (Fin 2) hT.1
  have hcover : ∀ c, c ≠ 0 → c ∉ J false ∪ J true →
      M.filtration.layer (fun i => c i) = ⊥ :=
    fun c _ hc => totalDegreeSplitDownset_terminal D.filtration c hc
  obtain ⟨r, _, _, B, hB, hstable, hresult⟩ :=
    hsplit M J hJ p hsum hM hcover g epsilon hepsilon hscale
  obtain ⟨hE, hdim, hterminal, h, _, happrox⟩ := hresult
  have hlip : (T.lipBound : ℝ) ≤ Real.exp p := by
    have hb := T.observable_budget hT
    have hn := T.normBound.coe_nonneg
    linarith
  have hub : ∀ x, ‖T.observable x‖ ≤ 1 := fun x =>
    (T.norm_le x).trans (show (T.normBound : ℝ) ≤ 1 from hnorm)
  obtain ⟨N, hN, hNbound, A, B', hAnorm, hBnorm, hA, hB', hAg, hBg, herr⟩ :=
    happrox T.observable T.lipBound hlip T.lipschitz hub
  let E := fun b => M.positivePolynomialDownsetModel (J b) (hJ b) r B hB hstable
  let F := fun b => M.positivePolynomialDownsetModelMultidegree (J b) (hJ b) r B hB hstable
  have hzero (b : Bool) (v : Fin 2 → ℕ) (hv : ¬v ≤ totalDegreeSplitBound s b) :
      (F b).filtration.layer v = ⊥ := by
    let c : Fin 2 →₀ ℕ := Finsupp.equivFunOnFinite.symm v
    exact hterminal b c hv
  let R := fun b => (F b).restrictBound (totalDegreeSplitBound s b)
    (totalDegreeSplitBound_le s b) (hzero b)
  let tests : ∀ b, Fin N → (E b).Niltest (fun _ : Fin 2 => 1) :=
    fun b => match b with
      | false => A
      | true => B'
  refine ⟨{
    count := N
    count_pos := hN
    count_bound := hNbound
    L := K
    dim := fun b => Fintype.card (M.PositivePolynomialDownsetIndex (J b))
    model := E
    multi := R
    complexity := fun b => (F b).restrictBound_complexity (totalDegreeSplitBound s b)
      (totalDegreeSplitBound_le s b) (hzero b) (hE b)
    dimension_bound := hdim
    orbit := fun b => (F b).filtration.restrictBoundRealOrbit (totalDegreeSplitBound s b)
      (hzero b) (M.filtration.positivePolynomialDownsetOrbit (J b) (hJ b) h)
    test := tests
    test_norm := ?_
    test_complexity := ?_
    test_orbit := ?_
    approximation := ?_ }⟩
  · intro b j
    cases b
    · exact hAnorm j
    · exact hBnorm j
  · intro b j
    cases b
    · exact hA j
    · exact hB' j
  · intro b j
    cases b
    · exact hAg j
    · exact hBg j
  · intro x
    change ‖T.eval x - ∑ j, (A j).eval x * (B' j).eval x‖ ≤ epsilon
    have heval : T.observable (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g)) =
        T.eval x := by
      change T.observable (QuotientGroup.mk
        ((D.filtration.totalDegreeMultifiltration (Fin 2)).realification.polynomialOrbitEval x
          (D.filtration.realTotalDegreeOrbit T.orbit))) = _
      rw [D.filtration.realTotalDegreeOrbit_eval]
      rfl
    simpa only [heval] using herr x

end Erdos3

end

end OAI

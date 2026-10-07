import OAI.Combinatorics.Progressions.Dynamics.ComparisonEquivalenceBudget
import OAI.Combinatorics.Progressions.Nilpotent.NativeFrozenMultidegreeNiltest
import OAI.Combinatorics.Progressions.Polynomial.ZeroDegreeCoordinate

namespace OAI

section

namespace Erdos3.NativeTwoVariableSplit

open scoped TensorProduct

attribute [local instance] NativeTwoVariableSplit.lie NativeTwoVariableSplit.algebra
  NativeTwoVariableSplit.topology NativeTwoVariableSplit.topologicalAdd
  NativeTwoVariableSplit.continuousSMul NativeTwoVariableSplit.hausdorff

theorem first_eval_eq {s d : ℕ} {p epsilon : ℝ} {f : (Fin 2 → ℤ) → ℂ}
    (R : NativeTwoVariableSplit s d p epsilon f) (j : Fin R.count)
    (x y : Fin 2 → ℤ) (hxy : x 1 = y 1) :
    (R.test false j).eval x = (R.test false j).eval y := by
  unfold RationalFilteredNilmanifold.Niltest.eval
  rw [R.test_orbit false j, (R.multi false).orbitToOrdinary_eval,
    (R.multi false).orbitToOrdinary_eval]
  apply congrArg (R.test false j).observable
  apply congrArg QuotientGroup.mk
  apply (R.multi false).filtration.realification.polynomialOrbitEval_eq_of_zero_coordinate
    0 (show totalDegreeSplitBound s false 0 = 0 from rfl) (R.orbit false) x y
  intro i hi
  fin_cases i
  · exact (hi rfl).elim
  · exact hxy

end Erdos3.NativeTwoVariableSplit

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct NNReal

theorem exists_controlled_basepoint_normalization (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) {w : σ → ℕ} (T : D.Niltest w)
      {p : ℝ}, 0 ≤ p → T.ComplexityLE p →
      ∃ U : D.Niltest w, U.normBound = T.normBound ∧ U.ComplexityLE ((p + C) ^ C) ∧
        D.filtration.realification.polynomialOrbitEval w 0 U.orbit = 1 ∧
        ∀ x : σ → ℤ, U.eval x = T.eval x := by
  obtain ⟨a, _, hrep⟩ := Erdos3.exists_realification_representatives_exp_bound s
  obtain ⟨b, _, hleft⟩ := exists_bounded_normalization_left_lipschitz s a
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (X + (X + Polynomial.C a + 2 + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ _ _ d D w T p hp hT
  have hcost : p + normalizedSquareLeftBudget a b p ≤ (p + C) ^ C := by
    simpa [X, normalizedSquareLeftBudget, Polynomial.eval₂_pow] using hbudget p hp
  obtain ⟨A, _, hA, hLip⟩ := hleft D p hp hT.1
  obtain ⟨ε, hε, γ, hγ, hfactor⟩ :=
    hrep D.basis D.filtration.lowerCentralSeries_eq_bot D.lattice D.grid
      ⌈Real.exp p⌉₊ (p + 1) D.grid_pos D.inner_grid
      (fun i j k => rationalHeightLE_ceil_exp (hT.1.2.2.1 i j k))
      (by linarith) (by simpa only [Fintype.card_fin] using hT.1.1.trans (show p ≤ p + 1 by linarith))
      (ceil_exp_le_exp_add_one hp) (hT.1.2.1.trans (Real.exp_le_exp.mpr (by linarith)))
      (D.filtration.realification.polynomialOrbitEval w 0 T.orbit)
  let U := T.normalizeBasepoint ε γ A (hLip ε hε)
  refine ⟨U, rfl, ?_, ?_, ?_⟩
  · exact (T.normalizeBasepoint_complexity ε γ A (hLip ε hε) hT
      (normalizedSquareLeftBudget_nonneg a b hp) hA).mono hcost
  · exact T.normalizeBasepoint_zero ε γ A (hLip ε hε) hfactor
  · intro x
    exact T.normalizeBasepoint_eval ε γ A (hLip ε hε) hγ x

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

theorem exists_controlled_group_normalization (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      ∀ g : D.RealGroup, ∃ (ε γ : D.RealGroup) (A : ℝ≥0),
        γ ∈ D.realLattice ∧ g = ε * γ ∧ 0 < A ∧ (A : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        letI := D.metricSpace
        LipschitzWith A (fun x : D.Space => ε • x) := by
  obtain ⟨a, _, hrep⟩ := Erdos3.exists_realification_representatives_exp_bound s
  obtain ⟨b, _, hleft⟩ := exists_bounded_normalization_left_lipschitz s a
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C a + 2 + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D p hp hD g
  have hcost : normalizedSquareLeftBudget a b p ≤ (p + C) ^ C := by
    simpa [X, normalizedSquareLeftBudget, Polynomial.eval₂_pow] using hbudget p hp
  obtain ⟨A, hApos, hA, hLip⟩ := hleft D p hp hD
  obtain ⟨ε, hε, γ, hγ, hfactor⟩ :=
    hrep D.basis D.filtration.lowerCentralSeries_eq_bot D.lattice D.grid
      ⌈Real.exp p⌉₊ (p + 1) D.grid_pos D.inner_grid
      (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k))
      (by linarith) (by simpa only [Fintype.card_fin] using hD.1.trans (show p ≤ p + 1 by linarith))
      (ceil_exp_le_exp_add_one hp) (hD.2.1.trans (Real.exp_le_exp.mpr (by linarith))) g
  exact ⟨ε, γ, A, hγ, hfactor, hApos, hA.trans (Real.exp_le_exp.mpr hcost), hLip ε hε⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module
open scoped TensorProduct NNReal

theorem exists_controlled_multidegree_basepoint_normalization (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
      (M : D.MultidegreeStructure bound) {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p →
      ∀ g : M.filtration.realification.PolynomialOrbit,
      ∃ (ε : D.RealGroup) (A : ℝ≥0), (A : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        (letI := D.metricSpace; LipschitzWith A (fun x : D.Space => ε • x)) ∧
        ∃ g' : M.filtration.realification.PolynomialOrbit,
          M.filtration.realification.polynomialOrbitEval 0 g' = 1 ∧
          ∀ x, ε • (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g') : D.Space) =
            QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g) := by
  obtain ⟨a, _, hrep⟩ := Erdos3.exists_realification_representatives_exp_bound s
  obtain ⟨b, _, hleft⟩ := exists_bounded_normalization_left_lipschitz s a
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C a + 2 + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ _ _ _ d D bound M p hp hD g
  have hcost : normalizedSquareLeftBudget a b p ≤ (p + C) ^ C := by
    simpa [X, normalizedSquareLeftBudget, Polynomial.eval₂_pow] using hbudget p hp
  obtain ⟨A, _, hA, hLip⟩ := hleft D p hp hD
  obtain ⟨ε, hε, γ, hγ, hfactor⟩ :=
    hrep D.basis D.filtration.lowerCentralSeries_eq_bot D.lattice D.grid
      ⌈Real.exp p⌉₊ (p + 1) D.grid_pos D.inner_grid
      (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k))
      (by linarith) (by simpa only [Fintype.card_fin] using hD.1.trans (show p ≤ p + 1 by linarith))
      (ceil_exp_le_exp_add_one hp) (hD.2.1.trans (Real.exp_le_exp.mpr (by linarith)))
      (M.filtration.realification.polynomialOrbitEval 0 g)
  refine ⟨ε, A, hA.trans (Real.exp_le_exp.mpr hcost), hLip ε hε,
    M.filtration.realification.normalizeMultidegreeOrbit g ε γ,
    M.filtration.realification.normalizeMultidegreeOrbit_zero g ε γ hfactor, ?_⟩
  intro x
  rw [M.filtration.realification.normalizeMultidegreeOrbit_eval]
  simp only [MulAction.Quotient.smul_mk, smul_eq_mul, ← mul_assoc, mul_inv_cancel, one_mul]
  exact QuotientGroup.mk_mul_of_mem _ (D.realLattice.inv_mem hγ)

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

theorem exists_normalized_common_correlators (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d)
      (T : G → D.Niltest (fun _ : Unit => 1)) (H : Finset G), H.Nonempty →
      ∀ {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p →
      (∀ h, (T h).ComplexityLE p) → (∀ h ∈ H, (T h).normBound ≤ 1) →
      ∀ {N : ℕ} [NeZero N] (weight : G → ZMod N → ℂ),
      (∀ h ∈ H, ∀ x, ‖weight h x‖ ≤ 1) →
      (∀ h ∈ H, Real.exp (-p) ≤
        ‖𝔼 x, weight h x * star ((T h).evalCyclic N (fun _ => x))‖) →
      ∃ (H' : Finset G) (S : G → D.Niltest (fun _ : Unit => 1)),
        H' ⊆ H ∧ H'.Nonempty ∧ Real.exp (-((p + C) ^ C)) * H.card ≤ (H'.card : ℝ) ∧
        (∀ h, (S h).normBound ≤ 1 ∧ (S h).UnitIntervalValued ∧
          (S h).ComplexityLE ((p + C) ^ C) ∧
          D.filtration.realification.polynomialOrbitEval (fun _ => 1) 0 (S h).orbit = 1) ∧
        (∀ h k, (S h).observable = (S k).observable) ∧
        ∀ h ∈ H', Real.exp (-((p + C) ^ C)) ≤
          ‖𝔼 x, weight h x * star ((S h).evalCyclic N (fun _ => x))‖ := by
  obtain ⟨a, _, hnormalize⟩ := exists_controlled_basepoint_normalization s
  obtain ⟨b, _, hfixed⟩ := exists_fixed_observable_correlators s
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + (X + Polynomial.C a) ^ a + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + (Q + Polynomial.C b) ^ b + 2)
  refine ⟨C, hC, ?_⟩
  intro G L _ _ _ _ _ _ d D T H hH p hp hD hT hcap N _ weight hweight hcorr
  let q := p + (p + a) ^ a + 2
  have hpow : 0 ≤ (p + a) ^ a := by positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hnormq : (p + a) ^ a ≤ q := by dsimp [q]; linarith
  have hq : 0 ≤ q := hp.trans hpq
  have hcost : q + (q + b) ^ b + 2 ≤ (p + C) ^ C := by
    simpa [X, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hfixedC : (q + b) ^ b ≤ (p + C) ^ C := by linarith
  choose R hRn hRc hRzero hRvalue using fun h => hnormalize D (T h) hp (hT h)
  have hReval (h : G) (x : ZMod N) :
      (R h).evalCyclic N (fun _ => x) = (T h).evalCyclic N (fun _ => x) := hRvalue h _
  obtain ⟨H', S, hsub, hnonempty, hdense, hS, hsame, hcS⟩ :=
    hfixed D R H hH hq (hD.mono D hpq) (fun h _ => (hRc h).mono hnormq)
      (fun h hh => by rw [hRn h]; exact hcap h hh) weight hweight
      (fun h hh => by
        simp_rw [hReval h]
        exact (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans (hcorr h hh))
  refine ⟨H', S, hsub, hnonempty, ?_, ?_, hsame, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hfixedC))
      (Nat.cast_nonneg _)).trans hdense
  · intro h
    refine ⟨(hS h).2.1, (hS h).2.2.1, (hS h).2.2.2.mono hfixedC, ?_⟩
    rw [(hS h).1]
    exact hRzero h
  · intro h hh
    exact (Real.exp_le_exp.mpr (neg_le_neg hfixedC)).trans (hcS h hh)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

universe u v

open Module
open scoped TensorProduct NNReal

theorem exists_controlled_frozen_niltest (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} {bound : σ → ℕ} (D : RationalFilteredNilmanifold L s d)
      (M : D.MultidegreeStructure bound) (S : Finset σ) (b : σ → ℤ)
      (g : M.filtration.realification.PolynomialOrbit)
      (u : D.Space → ℂ) (ℓ B : ℝ≥0)
      (_hu : letI := D.metricSpace; LipschitzWith ℓ u) (_hub : ∀ x, ‖u x‖ ≤ B)
      {p : ℝ}, M.ComplexityLE p → (ℓ : ℝ) ≤ Real.exp p → (B : ℝ) ≤ Real.exp p →
      ∃ E : RationalFilteredNilmanifold
          (M.filtration.weightedSubalgebra (retainedCoordinateWeight S))
          (multidegreeWeight (retainedCoordinateWeight S) bound)
          (finrank ℚ (M.filtration.weightedSubalgebra (retainedCoordinateWeight S))),
        E.filtration = M.filtration.weightedFiltration (retainedCoordinateWeight S) ∧
        E.lattice = D.lattice.comap
          (NilpotentLieBCHGroup.mapOfSteps
            (M.filtration.weightedSubalgebra (retainedCoordinateWeight S)).incl) ∧
        letI := moduleTopology ℝ
          (ℝ ⊗[ℚ] M.filtration.weightedSubalgebra (retainedCoordinateWeight S))
        letI : IsTopologicalAddGroup
            (ℝ ⊗[ℚ] M.filtration.weightedSubalgebra (retainedCoordinateWeight S)) :=
          IsModuleTopology.isTopologicalAddGroup ℝ _
        letI : T2Space (ℝ ⊗[ℚ] M.filtration.weightedSubalgebra (retainedCoordinateWeight S)) :=
          realification_moduleTopology_t2 E.basis
        ∃ T : E.Niltest (fun _ : S => 1), T.normBound = B ∧
          T.ComplexityLE ((p + C) ^ C) ∧
          E.filtration.realification.polynomialOrbitEval _ 0 T.orbit = 1 ∧
          ∀ x, T.eval x = u (QuotientGroup.mk
            (M.filtration.realification.polynomialOrbitEval (freezeCoordinates S b x) g)) := by
  obtain ⟨a, _, hrep⟩ := Erdos3.exists_realification_representatives_exp_bound s
  obtain ⟨k, _, hleft⟩ := exists_bounded_normalization_left_lipschitz s a
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget
    ((X + 3) ^ 11 + 2 * X + (X + Polynomial.C a + 2 + Polynomial.C k) ^ k + (X + 4) ^ 2 + 4)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ _ _ _ _ d bound D M S b g u ℓ B hu hub p hM hℓ hB
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  let c := retainedCoordinateWeight S
  let K := M.filtration.weightedSubalgebra c
  let r := normalizedSquareLeftBudget a k p
  have hr : 0 ≤ r := normalizedSquareLeftBudget_nonneg a k hp
  have hcost : (p + 3) ^ 11 + (2 * p + r + (p + 4) ^ 2 + 4) ≤ (p + C) ^ C := by
    convert hpoly p hp using 1
    simp [X, r, normalizedSquareLeftBudget, Polynomial.eval₂_pow]
    ring
  have hgeom : (p + 3) ^ 11 ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ 2 * p + r + (p + 4) ^ 2 + 4)).trans hcost
  have hobs : 2 * p + r + (p + 4) ^ 2 + 4 ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (by positivity : 0 ≤ (p + 3) ^ 11)).trans hcost
  obtain ⟨E, hEF, hEL, hE, he⟩ := M.exists_weighted_model c hM
  obtain ⟨A, _, hAb, hA⟩ := hleft D p hp hM.1
  obtain ⟨ε, hε, γ, hγ, hfactor⟩ :=
    hrep D.basis D.filtration.lowerCentralSeries_eq_bot D.lattice D.grid
      ⌈Real.exp p⌉₊ (p + 1) D.grid_pos D.inner_grid
      (fun i j k => rationalHeightLE_ceil_exp (hM.1.2.2.1 i j k))
      (by linarith) (by simpa only [Fintype.card_fin] using hM.1.1.trans (show p ≤ p + 1 by linarith))
      (ceil_exp_le_exp_add_one hp) (hM.1.2.1.trans (Real.exp_le_exp.mpr (by linarith)))
      (M.filtration.realification.polynomialOrbitEval (freezeCoordinates S b 0) g)
  refine ⟨E, hEF, hEL, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] K)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] K) := IsModuleTopology.isTopologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] K) := realification_moduleTopology_t2 E.basis
  let H := ⌈Real.exp (p + 1)⌉₊
  obtain ⟨T, hTnorm, hTlip, hTzero, hTeval⟩ := M.exists_frozen_niltest S E hEF hEL b g
    u ℓ B hu hub ε γ hγ hfactor A (hA ε hε) H
    (fun i j => rationalHeightLE_ceil_exp (he i j))
  have hdim : (finrank ℚ K : ℝ) ≤ p :=
    (Nat.cast_le.mpr (lie_subalgebra_finrank_le D.basis K)).trans
      (by simpa only [Fintype.card_fin] using hM.1.1)
  have hH : (H : ℝ) ≤ Real.exp (p + 2) := by
    simpa only [show p + 1 + 1 = p + 2 by ring] using
      ceil_exp_le_exp_add_one (by linarith : 0 ≤ p + 1)
  have hP : (coordinateLipschitzBound d (finrank ℚ K) H : ℝ) ≤ Real.exp ((p + 4) ^ 2) := by
    simpa only [NNReal.coe_natCast, show p + 2 + 2 = p + 4 by ring] using
      coordinateLipschitzBound_le_exp d (finrank ℚ K) H (by linarith : 0 ≤ p + 2)
        (hM.1.1.trans (by linarith)) (hdim.trans (by linarith)) hH
  have hTL : (T.lipBound : ℝ) ≤ Real.exp (p + r + (p + 4) ^ 2) := by
    rw [hTlip]
    change (ℓ : ℝ) * ((A : ℝ) * (coordinateLipschitzBound d (finrank ℚ K) H : ℝ)) ≤ _
    calc
      _ ≤ Real.exp p * (Real.exp r * Real.exp ((p + 4) ^ 2)) := by gcongr
      _ = _ := by simp only [← Real.exp_add]; congr 1; ring
  refine ⟨T, hTnorm, ⟨hE.mono E hgeom, ?_⟩, hTzero, hTeval⟩
  have hn : (T.normBound : ℝ) ≤ Real.exp p := by rw [hTnorm]; exact hB
  have hb := niltest_log_bound_of_exp T.normBound T.lipBound hp
    (by positivity : 0 ≤ p + r + (p + 4) ^ 2) hn hTL
  exact hb.trans (by linarith)

noncomputable def freezingExponent (s : ℕ) : ℕ :=
  Classical.choose (exists_controlled_frozen_niltest.{u, v} s)

theorem freezingExponent_ge_two (s : ℕ) : 2 ≤ freezingExponent.{u, v} s :=
  (Classical.choose_spec (exists_controlled_frozen_niltest.{u, v} s)).1

theorem freezingExponent_control {σ : Type u} {L : Type v} [Fintype σ] [DecidableEq σ]
    [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d : ℕ} {bound : σ → ℕ} (D : RationalFilteredNilmanifold L s d)
    (M : D.MultidegreeStructure bound) (S : Finset σ) (b : σ → ℤ)
    (g : M.filtration.realification.PolynomialOrbit)
    (f : D.Space → ℂ) (ℓ B : ℝ≥0)
    (hf : letI := D.metricSpace; LipschitzWith ℓ f) (hfb : ∀ x, ‖f x‖ ≤ B)
    {p : ℝ} (hM : M.ComplexityLE p) (hℓ : (ℓ : ℝ) ≤ Real.exp p) (hB : (B : ℝ) ≤ Real.exp p) :
    ∃ E : RationalFilteredNilmanifold
        (M.filtration.weightedSubalgebra (retainedCoordinateWeight S))
        (multidegreeWeight (retainedCoordinateWeight S) bound)
        (finrank ℚ (M.filtration.weightedSubalgebra (retainedCoordinateWeight S))),
      E.filtration = M.filtration.weightedFiltration (retainedCoordinateWeight S) ∧
      E.lattice = D.lattice.comap
        (NilpotentLieBCHGroup.mapOfSteps
          (M.filtration.weightedSubalgebra (retainedCoordinateWeight S)).incl) ∧
      letI := moduleTopology ℝ
        (ℝ ⊗[ℚ] M.filtration.weightedSubalgebra (retainedCoordinateWeight S))
      letI : IsTopologicalAddGroup
          (ℝ ⊗[ℚ] M.filtration.weightedSubalgebra (retainedCoordinateWeight S)) :=
        IsModuleTopology.isTopologicalAddGroup ℝ _
      letI : T2Space (ℝ ⊗[ℚ] M.filtration.weightedSubalgebra (retainedCoordinateWeight S)) :=
        realification_moduleTopology_t2 E.basis
      ∃ T : E.Niltest (fun _ : S => 1), T.normBound = B ∧
        T.ComplexityLE ((p + freezingExponent.{u, v} s) ^ freezingExponent.{u, v} s) ∧
        E.filtration.realification.polynomialOrbitEval _ 0 T.orbit = 1 ∧
        ∀ x, T.eval x = f (QuotientGroup.mk
          (M.filtration.realification.polynomialOrbitEval (freezeCoordinates S b x) g)) :=
  (Classical.choose_spec (exists_controlled_frozen_niltest.{u, v} s)).2
    D M S b g f ℓ B hf hfb hM hℓ hB

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

universe u

open Module
open RationalFilteredNilmanifold.MultidegreeStructure
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem exists_freezing_niltest {σ : Type u} [Fintype σ] [DecidableEq σ] (bound : σ → ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter bound p)
      (S : Finset σ) (b : σ → ℤ) (i : Fin W.outputDim),
      ∃ t n : ℕ, t = (∑ j ∈ S, bound j) ∧ n ≤ W.dim ∧
        ∃ E : RationalFilteredNilmanifold
          (W.multi.filtration.weightedSubalgebra (retainedCoordinateWeight S)) t n,
          letI := moduleTopology ℝ
            (ℝ ⊗[ℚ] W.multi.filtration.weightedSubalgebra (retainedCoordinateWeight S))
          letI : IsTopologicalAddGroup
              (ℝ ⊗[ℚ] W.multi.filtration.weightedSubalgebra (retainedCoordinateWeight S)) :=
            IsModuleTopology.isTopologicalAddGroup ℝ _
          letI : T2Space
              (ℝ ⊗[ℚ] W.multi.filtration.weightedSubalgebra (retainedCoordinateWeight S)) :=
            realification_moduleTopology_t2 E.basis
          ∃ T : E.Niltest (fun _ : S => 1), T.normBound = 1 ∧
            T.ComplexityLE ((p + C) ^ C) ∧
            E.filtration.realification.polynomialOrbitEval _ 0 T.orbit = 1 ∧
            ∀ x, T.eval x = W.eval i (freezeCoordinates S b x) := by
  refine ⟨freezingExponent.{u, 0} (∑ j, bound j), freezingExponent_ge_two.{u, 0} _, ?_⟩
  intro p W S b i
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  obtain ⟨E, _, _, hE⟩ := freezingExponent_control W.model W.multi S b W.orbit (W.vertical.observable i)
    W.vertical.lipBound 1 (W.vertical.lipschitz i) (W.vertical.norm i) W.complexity
    W.vertical.lip_bound (by simpa only [NNReal.coe_one] using Real.one_le_exp hp)
  refine ⟨multidegreeWeight (retainedCoordinateWeight S) bound,
    finrank ℚ (W.multi.filtration.weightedSubalgebra (retainedCoordinateWeight S)),
    retainedCoordinate_degree S bound, ?_, E, hE⟩
  simpa only [Fintype.card_fin] using
    lie_subalgebra_finrank_le W.model.basis
      (W.multi.filtration.weightedSubalgebra (retainedCoordinateWeight S))

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeTwoVariableSplit

open Module RationalFilteredNilmanifold.MultidegreeStructure
open scoped TensorProduct BigOperators

attribute [local instance] NativeTwoVariableSplit.lie NativeTwoVariableSplit.algebra
  NativeTwoVariableSplit.topology NativeTwoVariableSplit.topologicalAdd
  NativeTwoVariableSplit.continuousSMul NativeTwoVariableSplit.hausdorff

theorem exists_second_expansion_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {d : ℕ} {p epsilon : ℝ} {f : (Fin 2 → ℤ) → ℂ}
      (R : NativeTwoVariableSplit s d p epsilon f) (j : Fin R.count) (h : ℤ),
      ∃ E : NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) ((p + C) ^ C)
          (fun x => (R.test true j).eval ![h, x ()]), E.count = 1 := by
  obtain ⟨C, hC, hfreeze⟩ := exists_controlled_frozen_niltest (∑ _ : Fin 2, s)
  refine ⟨C, hC, ?_⟩
  intro d p epsilon f R j h
  classical
  let S : Finset (Fin 2) := {1}
  have hp : 0 ≤ p := (Nat.cast_nonneg (R.dim true)).trans (R.complexity true).1.1
  have hlip : ((R.test true j).lipBound : ℝ) ≤ Real.exp p := by
    have hb := (R.test true j).observable_budget (R.test_complexity true j)
    have hn := (R.test true j).normBound.coe_nonneg
    linarith
  have hub : ∀ x, ‖(R.test true j).observable x‖ ≤ (1 : ℝ) := fun x =>
    ((R.test true j).norm_le x).trans
      (show ((R.test true j).normBound : ℝ) ≤ 1 from R.test_norm true j)
  obtain ⟨E, _, _, hE⟩ := hfreeze (R.model true) (R.multi true) S ![h, 0]
    (R.orbit true) (R.test true j).observable (R.test true j).lipBound 1
    (R.test true j).lipschitz hub (R.complexity true) hlip
    (by simpa only [NNReal.coe_one] using Real.one_le_exp hp)
  let K := (R.multi true).filtration.weightedSubalgebra (retainedCoordinateWeight S)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] K)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] K) := IsModuleTopology.isTopologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] K) := realification_moduleTopology_t2 E.basis
  obtain ⟨T, _, hT, _, hTeval⟩ := hE
  let U := T.affinePullback (fun _ (_ : Unit) => (1 : ℤ)) 0
  have hU : U.ComplexityLE ((p + C) ^ C) := hT
  have hval (x : Unit → ℤ) : U.eval x = (R.test true j).eval ![h, x ()] := by
    rw [RationalFilteredNilmanifold.Niltest.eval_affinePullback, hTeval]
    unfold RationalFilteredNilmanifold.Niltest.eval
    rw [R.test_orbit true j, (R.multi true).orbitToOrdinary_eval]
    congr 2
    apply congrArg (fun z => (R.multi true).filtration.realification.polynomialOrbitEval z
      (R.orbit true))
    funext i
    fin_cases i <;> simp [S, freezeCoordinates, integerAffineMap]
  have hdegree : multidegreeWeight (retainedCoordinateWeight S) (totalDegreeSplitBound s true) =
      s - 1 := by
    rw [retainedCoordinate_degree]
    simp [S, totalDegreeSplitBound]
  have hresult : ∃ Q : NativeIntegerExpansion (fun _ : Unit => 1)
      (multidegreeWeight (retainedCoordinateWeight S) (totalDegreeSplitBound s true))
      ((p + C) ^ C) (fun x => (R.test true j).eval ![h, x ()]), Q.count = 1 :=
    ⟨NativeIntegerExpansion.ofTest U hU (fun x => (hval x).symm), rfl⟩
  exact hdegree ▸ hresult

end Erdos3.NativeTwoVariableSplit

end

end OAI

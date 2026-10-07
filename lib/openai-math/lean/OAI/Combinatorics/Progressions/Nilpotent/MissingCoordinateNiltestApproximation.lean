import OAI.Combinatorics.Progressions.Estimates.TwoDownsetPrecision
import OAI.Combinatorics.Progressions.Geometry.MissingCoordinateDownsets
import OAI.Combinatorics.Progressions.Geometry.NativeCoordinateSplitFreezing
import OAI.Combinatorics.Progressions.Polynomial.NativeTotalDegreeMultifiltration

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open scoped TensorProduct

theorem niltest_eval_eq_of_zero_coordinate {σ L : Type*} [Fintype σ]
    [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
    (M : D.MultidegreeStructure bound) (i : σ) (hi : bound i = 0)
    (T : D.Niltest (fun _ : σ => 1)) (g : M.filtration.realification.PolynomialOrbit)
    (hT : T.orbit = M.orbitToOrdinary g) (x y : σ → ℤ)
    (hxy : ∀ j, j ≠ i → x j = y j) : T.eval x = T.eval y := by
  unfold RationalFilteredNilmanifold.Niltest.eval
  rw [hT, M.orbitToOrdinary_eval, M.orbitToOrdinary_eval]
  apply congrArg T.observable
  apply congrArg QuotientGroup.mk
  exact M.filtration.realification.polynomialOrbitEval_eq_of_zero_coordinate i hi g x y hxy

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3

open Module VectorPolynomial RationalFilteredNilmanifold
open RationalFilteredNilmanifold.MultidegreeStructure
open scoped TensorProduct BigOperators NNReal

theorem exists_missing_coordinate_niltest_approximation (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} {D : RationalFilteredNilmanifold L s d} {p : ℝ}
      (T : D.Niltest (fun _ : Fin (s + 1) => 1)), T.ComplexityLE p → T.normBound ≤ 1 →
      ∀ epsilon : ℝ, 0 < epsilon → 1 / epsilon ≤ Real.exp ((p + 2) ^ a) →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (c : Fin m → ℂ) (F : Fin (s + 1) → Fin m → (Fin (s + 1) → ℤ) → ℂ),
          (∀ j, ‖c j‖ ≤ 2) ∧ (∀ i j x, ‖F i j x‖ ≤ 1) ∧
          (∀ i j x y, (∀ k, k ≠ i → x k = y k) → F i j x = F i j y) ∧
          ∀ x, ‖T.eval x - ∑ j, c j * ∏ i, F i j x‖ ≤ epsilon := by
  obtain ⟨B, _, hsplit⟩ := exists_multidegree_downset_splitting s ((s + 1) * s) a
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C (s + 1) + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D p T hT hnorm epsilon hepsilon hscale
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hT.1.1
  let q := p + (s + 1 : ℕ)
  have hpq : p ≤ q := le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hq : 0 ≤ q := hp.trans hpq
  have hcost : (q + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, q, Polynomial.eval₂_pow] using hbudget p hp
  let M := D.totalDegreeMultidegree (Fin (s + 1)) hT.1
  let J := missingCoordinateDownset s
  have hJ : ∀ i, IsLowerSet (J i) := missingCoordinateDownset_lower s
  let K := fun i => M.filtration.positivePolynomialAlgebra ⧸
    restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)
  let : ∀ i, TopologicalSpace (ℝ ⊗[ℚ] K i) := fun _ => moduleTopology ℝ _
  let : ∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] K i) :=
    fun _ => IsModuleTopology.isTopologicalAddGroup ℝ _
  let : ∀ i, T2Space (ℝ ⊗[ℚ] K i) :=
    fun i => realification_moduleTopology_t2 (M.positivePolynomialDownsetFinBasis (J i) (hJ i) q)
  have hM : M.ComplexityLE q := (D.totalDegreeMultidegree_complexity (Fin (s + 1)) hT.1).mono M hpq
  have hfamily : (Fintype.card (Fin (s + 1)) : ℝ) ≤ q + 2 := by
    simp only [Fintype.card_fin]
    dsimp [q]
    linarith only [hp]
  have hcover : ∀ b, b ≠ 0 → (∀ i, b ∉ J i) → M.filtration.layer (fun k => b k) = ⊥ :=
    fun b _ hb => missingCoordinateDownset_terminal D.filtration b hb
  have hscaleq : 1 / epsilon ≤ Real.exp ((q + 2) ^ a) :=
    hscale.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) (by linarith only [hpq]) a))
  obtain ⟨r, _, _, b, hb, hstable, hE, _, h, _, n, hn, _, hcount, U,
    hUnorm, _, _, hUorbit, happrox⟩ :=
    hsplit (I := Unit) (α := Fin (s + 1)) M J hJ q (by simp) hM hfamily hcover
      (D.filtration.realTotalDegreeOrbit T.orbit) epsilon hepsilon hscaleq
      (by simpa using Real.one_le_exp hq)
  let V := fun i => M.positivePolynomialDownsetModelMultidegree (J i) (hJ i) r b hb hstable
  have hzero (i : Fin (s + 1)) (v : Fin (s + 1) → ℕ)
      (hv : ¬v ≤ missingCoordinateBound s i) : (V i).filtration.layer v = ⊥ := by
    let c : Fin (s + 1) →₀ ℕ := Finsupp.equivFunOnFinite.symm v
    exact M.filtration.positivePolynomialDownsetQuotient_terminal (J i) (hJ i) c hv
  let V' := fun i => (V i).restrictBound (missingCoordinateBound s i)
    (missingCoordinateBound_le s i) (hzero i)
  have hindependent (i : Fin (s + 1)) (j : Fin (n i)) (x y : Fin (s + 1) → ℤ)
      (hxy : ∀ k, k ≠ i → x k = y k) : (U i j).eval x = (U i j).eval y := by
    let g : (V i).filtration.realification.PolynomialOrbit :=
      M.filtration.positivePolynomialDownsetOrbit (J i) (hJ i) h
    let g' := (V i).filtration.restrictBoundRealOrbit (missingCoordinateBound s i) (hzero i) g
    exact (V' i).niltest_eval_eq_of_zero_coordinate i (by simp [missingCoordinateBound])
      (U i j) g' (hUorbit i j) x y hxy
  have hlip : (T.lipBound : ℝ) ≤ Real.exp q := by
    have hobs := T.observable_budget hT
    have hnonneg := T.normBound.coe_nonneg
    exact (by linarith only [hobs, hnonneg] : (T.lipBound : ℝ) ≤ Real.exp p).trans
      (Real.exp_le_exp.mpr hpq)
  have hub : ∀ x, ‖T.observable x‖ ≤ 1 := fun x =>
    (T.norm_le x).trans (show (T.normBound : ℝ) ≤ 1 from hnorm)
  obtain ⟨coeff, hcoeff, _, herr⟩ := happrox (fun _ : Unit => T.observable) T.lipBound hlip
    (fun _ => T.lipschitz) (fun _ => hub)
  have hscalar := scalar_error_le_of_vector_error (I := Unit) (J := ∀ i, Fin (n i))
    (S := (Fin (s + 1) → ℤ)) (epsilon := epsilon)
    (fun _ : Unit => fun x => T.observable (QuotientGroup.mk
      (M.filtration.realification.polynomialOrbitEval x (D.filtration.realTotalDegreeOrbit T.orbit))))
    (fun j x => ∏ i, (U i (j i)).eval x) coeff herr ()
  let W := ∀ i, Fin (n i)
  let : Nonempty W := ⟨fun i => ⟨0, hn i⟩⟩
  let e : Fin (Fintype.card W) ≃ W := (Fintype.equivFin W).symm
  refine ⟨Fintype.card W, Fintype.card_pos, hcount.trans (Real.exp_le_exp.mpr hcost),
    (fun j => coeff (e j) ()), (fun i j x => (U i (e j i)).eval x),
    (fun j => hcoeff (e j) ()), ?_, ?_, ?_⟩
  · intro i j x
    exact ((U i (e j i)).norm_eval_le x).trans (by rw [hUnorm]; rfl)
  · intro i j x y hxy
    exact hindependent i (e j i) x y hxy
  · intro x
    have hval : T.observable (QuotientGroup.mk
        (M.filtration.realification.polynomialOrbitEval x
          (D.filtration.realTotalDegreeOrbit T.orbit))) = T.eval x := by
      exact congrArg (fun z => T.observable (QuotientGroup.mk z))
        (D.filtration.realTotalDegreeOrbit_eval T.orbit x)
    have hs := hscalar x
    rw [hval] at hs
    have hsum := e.sum_comp (fun j => coeff j () * ∏ i, (U i (j i)).eval x)
    rw [hsum]
    simpa only [mul_comm] using hs

end Erdos3

end

end OAI

import OAI.Combinatorics.Progressions.Linear.CommonFreeSpanBounds
import OAI.Combinatorics.Progressions.Linear.LowerRankObservableDifference

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L M I : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [Fintype I] {s t d e : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
  {D : RationalFilteredNilmanifold L s d} {E : RationalFilteredNilmanifold M t e}
  {T : Subgroup E.RealGroup} {p : ℝ} (V : E.UnitVerticalObservable T I p)
  (φ : L →ₗ⁅ℚ⁆ M)
  (hφ : D.lattice ≤ E.lattice.comap (mapOfSteps
    (hL := D.filtration.lowerCentralSeries_eq_bot) (hM := E.filtration.lowerCentralSeries_eq_bot) φ))
  (S : Subgroup D.RealGroup)
  (hS : S ≤ T.comap (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
    (hM := E.filtration.lowerCentralSeries_eq_bot) φ))
  (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) (hE : E.GeometryComplexityLE p)
  (hentries : ∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p)

noncomputable def controlledPullback :
    D.UnitVerticalObservable S I (p + (p + 3) ^ 2 + (p + 2) ^ 4) :=
  V.pullback φ hφ S hS ⟨Real.exp ((p + 3) ^ 2), (Real.exp_pos _).le⟩
    (D.nativeSpaceMap_lipschitz E φ hφ hp hD hE hentries)
    (by
      change (V.lipBound : ℝ) * Real.exp ((p + 3) ^ 2) ≤ _
      calc
        _ ≤ Real.exp p * Real.exp ((p + 3) ^ 2) :=
          mul_le_mul_of_nonneg_right V.lip_bound (Real.exp_pos _).le
        _ = Real.exp (p + (p + 3) ^ 2) := (Real.exp_add _ _).symm
        _ ≤ _ := Real.exp_le_exp.mpr (le_add_of_nonneg_right (by positivity)))
    (by
      intro i
      exact (rational_functional_value_logHeight E.basis V.frequency hp
        (by simpa only [Fintype.card_fin] using hE.1) V.height (φ (D.basis i))
        (fun j => hentries j i)).trans
          (le_add_of_nonneg_left (add_nonneg hp (sq_nonneg (p + 3)))))

theorem controlledPullback_frequency :
    (V.controlledPullback φ hφ S hS hp hD hE hentries).frequency =
      V.frequency.comp φ.toLinearMap := rfl

theorem controlledPullback_observable_mk (i : I) (x : D.RealGroup) :
    (V.controlledPullback φ hφ S hS hp hD hE hentries).observable i (QuotientGroup.mk x) =
      V.observable i (QuotientGroup.mk
        (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := E.filtration.lowerCentralSeries_eq_bot) φ x)) := rfl

end Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup

theorem exists_native_free_evaluation (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (X L : Type*) [Fintype X] [LieRing L] [LieAlgebra ℚ L]
      (r d : ℕ) (hr : r ≤ s) (D : RationalFilteredNilmanifold L s d)
      (R : D.DegreeRankStructure r) (w : X → ℕ) (hw : ∀ x, 0 < w x)
      (f : X → L) (hf : ∀ x, f x ∈ R.filtration.layer (w x) 0)
      (p : ℝ), 0 ≤ p → (Fintype.card X : ℝ) ≤ p → R.ComplexityLE p →
      (∀ x i, rationalLogHeight (D.basis.repr (f x) i) ≤ p) →
      ∃ E : RationalFilteredNilmanifold (FreeDegreeRankLieAlgebra X s r w hw) s
          (finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw)),
        ∃ Q : E.DegreeRankStructure r,
          Q.filtration = FreeDegreeRankLieAlgebra.filtration X s r w hw hr ∧
          Q.ComplexityLE ((p + C) ^ C) ∧ IsCentralLieBasis E.basis ∧
          Nonempty (FreeCoordinateFrame E.basis ((p + C) ^ C)) ∧
          (∀ i j, rationalLogHeight (D.basis.repr
            (FreeDegreeRankLieAlgebra.lift R.filtration w hw f hf (E.basis j)) i) ≤ (p + C) ^ C) ∧
          E.lattice ≤ D.lattice.comap (mapOfSteps
            (hL := E.filtration.lowerCentralSeries_eq_bot) (hM := D.filtration.lowerCentralSeries_eq_bot)
            (FreeDegreeRankLieAlgebra.lift R.filtration w hw f hf)) := by
  obtain ⟨a, _, hfree⟩ := exists_free_degree_rank_nilmanifold s
  obtain ⟨c, _, hcover⟩ := RationalFilteredNilmanifold.exists_native_source_cover
  let B₀ : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let Q₀ := Polynomial.X + B₀
  let V₀ := ((Q₀ + 3) ^ (6 * s + 2) + Q₀ + 2) ^ 4
  let P₀ := Q₀ + V₀
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P₀ + (P₀ + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro X L _ _ _ r d hr D R w hw f hf p hp hX hR hfH
  let B := (p + a) ^ a
  let q := p + B
  let v := ((q + 3) ^ (6 * s + 2) + q + 2) ^ 4
  let P := q + v
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hpq : p ≤ q := le_add_of_nonneg_right hB
  have hBq : B ≤ q := le_add_of_nonneg_left hp
  have hq : 0 ≤ q := hp.trans hpq
  have hqP : q ≤ P := le_add_of_nonneg_right (by dsimp only [v]; positivity)
  have hvP : v ≤ P := le_add_of_nonneg_left hq
  have hP : 0 ≤ P := hq.trans hqP
  have hsum : P + (P + c) ^ c ≤ (p + C) ^ C := by
    simpa [B₀, Q₀, V₀, P₀, B, q, v, P, Polynomial.eval₂_pow] using hbudget p hp
  have hPC : P ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ (P + c) ^ c)).trans hsum
  have hcoverC : (P + c) ^ c ≤ (p + C) ^ C := (le_add_of_nonneg_left hP).trans hsum
  have hBC : B ≤ (p + C) ^ C := hBq.trans (hqP.trans hPC)
  obtain ⟨E₀, Q, hQ, hQcomplex, hcentral, _, _, htree, e, he, hdim, S, hS, hSH⟩ :=
    hfree X r hr w hw 1 (by decide) p hp hX
      (by simpa only [Nat.cast_one, Real.exp_zero] using Real.exp_le_exp.mpr hp)
  let φ := FreeDegreeRankLieAlgebra.lift R.filtration w hw f hf
  have hφ (i j) : rationalLogHeight (D.basis.repr (φ (E₀.basis j)) i) ≤ v := by
    have h := FreeDegreeRankLieAlgebra.lift_basis_matrix_logHeight R.filtration w hw f hf e he
      E₀.basis D.basis S hS hq (hdim.trans hBq)
      (by simpa only [Fintype.card_fin] using hR.1.1.trans hpq)
      (fun i j => (hSH i j).trans hBq)
      (fun i j k => (hR.1.2.2.1 i j k).trans hpq)
      (fun x i => (hfH x i).trans hpq) i j
    rw [LinearMap.toMatrix_apply] at h
    exact h
  obtain ⟨Λ, _, _, _, _, _, N, hN, hin, hout, hgeom, hmap⟩ :=
    hcover E₀ D φ hP (hQcomplex.1.mono E₀ (hBq.trans hqP))
      (hR.1.mono D (hpq.trans hqP)) (fun i j => (hφ i j).trans hvP)
  refine ⟨E₀.withLattice Λ N hN hin hout, Q.withLattice Λ N hN hin hout, hQ, ?_,
    hcentral, ⟨{
      tree_height := fun x hx i => (htree x hx i).trans hBC
      sourceBasis := e
      sourceBasis_trees := he
      sourceDimension := hdim.trans hBC
      sectionMatrix := S
      section_right_inverse := hS
      section_height := fun i j => (hSH i j).trans hBC
    }⟩, fun i j => (hφ i j).trans (hvP.trans hPC), hmap⟩
  exact Q.withLattice_complexity Λ N hN hin hout hQcomplex hBC
    (hgeom.mono _ hcoverC)

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_native_free_unit_observable (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (X L I : Type*) [Fintype X] [Fintype I]
      [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (r d : ℕ) (hr : r ≤ s) (D : RationalFilteredNilmanifold L s d)
      (R : D.DegreeRankStructure r) (w : X → ℕ) (hw : ∀ x, 0 < w x)
      (f : X → L) (hf : ∀ x, f x ∈ R.filtration.layer (w x) 0)
      (p : ℝ), 0 ≤ p → (Fintype.card X : ℝ) ≤ p → R.ComplexityLE p →
      (∀ x i, rationalLogHeight (D.basis.repr (f x) i) ≤ p) →
      ∀ U : D.UnitVerticalObservable (R.realSubgroup s r) I p,
      let φ := FreeDegreeRankLieAlgebra.lift R.filtration w hw f hf
      ∃ E : RationalFilteredNilmanifold (FreeDegreeRankLieAlgebra X s r w hw) s
          (finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw)),
        ∃ Q : E.DegreeRankStructure r,
          Q.filtration = FreeDegreeRankLieAlgebra.filtration X s r w hw hr ∧
          Q.ComplexityLE ((p + C) ^ C) ∧ IsCentralLieBasis E.basis ∧
          Nonempty (FreeCoordinateFrame E.basis ((p + C) ^ C)) ∧
          (∀ i j, rationalLogHeight (D.basis.repr (φ (E.basis j)) i) ≤ (p + C) ^ C) ∧
          E.lattice ≤ D.lattice.comap (mapOfSteps
            (hL := E.filtration.lowerCentralSeries_eq_bot)
            (hM := D.filtration.lowerCentralSeries_eq_bot) φ) ∧
          (letI := moduleTopology ℝ (ℝ ⊗[ℚ] FreeDegreeRankLieAlgebra X s r w hw)
           letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] FreeDegreeRankLieAlgebra X s r w hw) :=
             IsModuleTopology.isTopologicalAddGroup ℝ _
           letI := realification_moduleTopology_t2 E.basis
           ∃ V : E.UnitVerticalObservable (Q.realSubgroup s r) I ((p + C) ^ C),
             V.frequency = U.frequency.comp φ.toLinearMap ∧
             ∀ i x, V.observable i (QuotientGroup.mk x) =
               U.observable i (QuotientGroup.mk (realificationMap
                 (hnil := E.filtration.lowerCentralSeries_eq_bot)
                 (hM := D.filtration.lowerCentralSeries_eq_bot) φ x))) := by
  obtain ⟨a, _, hfree⟩ := exists_native_free_evaluation s
  let A₀ : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let T₀ := Polynomial.X + A₀
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (A₀ + (T₀ + (T₀ + 3) ^ 2 + (T₀ + 2) ^ 4))
  refine ⟨C, hC, ?_⟩
  intro X L I _ _ _ _ _ _ _ _ r d hr D R w hw f hf p hp hX hR hfH U φ
  let A := (p + a) ^ a
  let t := p + A
  let q := t + (t + 3) ^ 2 + (t + 2) ^ 4
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hpt : p ≤ t := le_add_of_nonneg_right hA
  have hAt : A ≤ t := le_add_of_nonneg_left hp
  have ht : 0 ≤ t := hp.trans hpt
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hcost : A + q ≤ (p + C) ^ C := by
    simpa [A₀, T₀, A, t, q, Polynomial.eval₂_pow] using hbudget p hp
  have hAC : A ≤ (p + C) ^ C := (le_add_of_nonneg_right hq).trans hcost
  have hqC : q ≤ (p + C) ^ C := (le_add_of_nonneg_left hA).trans hcost
  obtain ⟨E, Q, hQ, hcomplex, hcentral, ⟨frame⟩, hmatrix, hlattice⟩ :=
    hfree X L r d hr D R w hw f hf p hp hX hR hfH
  let := moduleTopology ℝ (ℝ ⊗[ℚ] FreeDegreeRankLieAlgebra X s r w hw)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] FreeDegreeRankLieAlgebra X s r w hw) :=
    IsModuleTopology.isTopologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 E.basis
  have hlayer (i j : ℕ) :
      (Q.filtration.layer i j).map φ.toLinearMap ≤ R.filtration.layer i j := by
    rintro y ⟨x, hx, rfl⟩
    rw [hQ] at hx
    exact FreeDegreeRankLieAlgebra.lift_mem_layer R.filtration w hw f hf hr hx
  have htop : Q.realSubgroup s r ≤ (R.realSubgroup s r).comap
      (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot) φ) := by
    intro z hz
    change realificationLieHom φ z.coord ∈ (R.filtration.layer s r).baseChange ℝ
    have hz' : z.coord ∈ (Q.filtration.layer s r).baseChange ℝ := hz
    have h := Submodule.baseChange_mono ℝ (hlayer s r)
    rw [realification_map] at h
    exact h ⟨z.coord, hz', rfl⟩
  let V := (U.mono hpt).controlledPullback φ hlattice (Q.realSubgroup s r) htop ht
    (hcomplex.1.mono E hAt) (hR.1.mono D hpt) (fun i j => (hmatrix i j).trans hAt)
  refine ⟨E, Q, hQ, hcomplex.mono Q hAC, hcentral,
    ⟨frame.mono hAC⟩, (fun i j => (hmatrix i j).trans hAC), hlattice, ?_⟩
  exact ⟨V.mono hqC, rfl, fun i x => rfl⟩

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

variable {L M I J : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [Fintype I] [Fintype J] {s t d e : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
  {D : RationalFilteredNilmanifold L s d} {E : RationalFilteredNilmanifold M t e}
  {T : Subgroup D.RealGroup} {S : Subgroup E.RealGroup} {p : ℝ}
  (V : D.UnitVerticalObservable T I p) (U : E.UnitVerticalObservable S J p)
  (φ : L →ₗ⁅ℚ⁆ M)
  (hφ : D.lattice ≤ E.lattice.comap (mapOfSteps
    (hL := D.filtration.lowerCentralSeries_eq_bot) (hM := E.filtration.lowerCentralSeries_eq_bot) φ))

noncomputable def mapDifferenceObservable (a : I × J) (x : D.Space) : ℂ :=
  V.observable a.1 x * star (U.observable a.2 (D.nativeSpaceMap E φ hφ x))

theorem mapDifferenceObservable_reconstruct (i : I) (x : D.Space) :
    ∑ j, mapDifferenceObservable V U φ hφ (i, j) x *
      U.observable j (D.nativeSpaceMap E φ hφ x) = V.observable i x := by
  exact (complex_unit_vector_resolution (fun j => U.observable j (D.nativeSpaceMap E φ hφ x))
    (U.unit _) (V.observable i x)).symm

theorem exists_uniform_lower_rank_map_difference (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M I J σ : Type*}
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] [Fintype I] [Fintype J]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      {r d e : ℕ} (D : RationalFilteredNilmanifold L s d)
      (E : RationalFilteredNilmanifold M s e)
      (R : D.DegreeRankStructure (r + 1)) (S : E.DegreeRankStructure (r + 1))
      (φ : L →ₗ⁅ℚ⁆ M)
      (hφ : D.lattice ≤ E.lattice.comap (mapOfSteps
        (hL := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ))
      {p : ℝ} (V : D.UnitVerticalObservable (R.realSubgroup s (r + 1)) I p)
      (U : E.UnitVerticalObservable (S.realSubgroup s (r + 1)) J p),
      0 ≤ p → R.ComplexityLE p → S.ComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      (∀ x ∈ R.filtration.layer s (r + 1), φ x ∈ S.filtration.layer s (r + 1)) →
      (∀ x ∈ R.filtration.layer s (r + 1), V.frequency x = U.frequency (φ x)) →
      ∀ w : σ → ℕ,
        HasUniformLowerRankUnitFamily D R (mapDifferenceObservable V U φ hφ) w ((p + C) ^ C) := by
  obtain ⟨a, _, hdescent⟩ := UnitVerticalObservable.exists_uniform_lower_rank_difference_family s
  let X : Polynomial ℕ := Polynomial.X
  let P := X + (X + 3) ^ 2 + (X + 2) ^ 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((P + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro L M I J σ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r d e D E R S φ hφ p V U hp hR hS hentries htop hfreq w
  let q := p + (p + 3) ^ 2 + (p + 2) ^ 4
  have hpq : p ≤ q := by
    dsimp only [q]
    linarith [sq_nonneg (p + 3), show 0 ≤ (p + 2) ^ 4 from by positivity]
  have hq : 0 ≤ q := hp.trans hpq
  have hb : (q + a) ^ a ≤ (p + C) ^ C := by
    simpa [P, X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hreal : R.realSubgroup s (r + 1) ≤ (S.realSubgroup s (r + 1)).comap
      (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ) := by
    intro z hz
    change realificationLieHom φ z.coord ∈ (S.filtration.layer s (r + 1)).baseChange ℝ
    have hmap : (R.filtration.layer s (r + 1)).map φ.toLinearMap ≤
        S.filtration.layer s (r + 1) := by
      rintro y ⟨x, hx, rfl⟩
      exact htop x hx
    have h := Submodule.baseChange_mono ℝ hmap
    rw [realification_map] at h
    exact h ⟨z.coord, hz, rfl⟩
  let U' := U.controlledPullback φ hφ (R.realSubgroup s (r + 1)) hreal hp hR.1 hS.1 hentries
  have heq : ∀ x ∈ R.filtration.layer s (r + 1), (V.mono hpq).frequency x = U'.frequency x := hfreq
  have h := hdescent D R (V.mono hpq) U' hq (hR.mono R hpq) heq w
  exact h.mono hb

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

variable {L M I J X : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [Fintype I] [Fintype J] {s t d e : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
  {D : RationalFilteredNilmanifold L s d} {E : RationalFilteredNilmanifold M t e}
  {T : Subgroup D.RealGroup} {S : Subgroup E.RealGroup} {p : ℝ}
  (V : D.UnitVerticalObservable T I p) (U : E.UnitVerticalObservable S J p)
  (φ : L →ₗ⁅ℚ⁆ M)
  (hφ : D.lattice ≤ E.lattice.comap (mapOfSteps
    (hL := D.filtration.lowerCentralSeries_eq_bot) (hM := E.filtration.lowerCentralSeries_eq_bot) φ))

theorem exists_quotient_comparison_correlation (A : Finset X) (f : X → ℂ)
    (g : X → D.Space) (i : I) {ρ B : ℝ} (hρ : 0 < ρ) (hB : 0 < B)
    (hcard : (Fintype.card J : ℝ) ≤ B)
    (hcorr : ρ ≤ ‖𝔼 x ∈ A, f x * star (V.observable i (g x))‖) :
    ∃ j, ρ / B ≤ ‖𝔼 x ∈ A,
      f x * star (U.observable j (D.nativeSpaceMap E φ hφ (g x))) *
        star (mapDifferenceObservable V U φ hφ (i, j) (g x))‖ := by
  classical
  let P (j : J) (x : X) := star (U.observable j (D.nativeSpaceMap E φ hφ (g x)))
  let ψ (j : J) (_ : Unit) (x : X) := star (mapDifferenceObservable V U φ hφ (i, j) (g x))
  have hunit (x : X) (_hx : x ∈ A) : ∑ j, ‖P j x‖ ^ 2 = 1 := by
    simpa only [P, norm_star] using U.unit (D.nativeSpaceMap E φ hφ (g x))
  have hexp (j : J) (x : X) (_hx : x ∈ A) :
      star (V.observable i (g x)) * star (P j x) = ∑ a : Unit, (1 : ℂ) * ψ j a x := by
    simp only [P, ψ, mapDifferenceObservable, star_star, star_mul,
      one_mul, Fintype.sum_unique]
    ring
  obtain ⟨j, a, h⟩ := exists_unit_expansion_correlation A f
    (fun x => star (V.observable i (g x))) P (fun (_ : J) (_ : Unit) => (1 : ℂ)) ψ
    hunit hexp hρ hB (by norm_num : (0 : ℝ) < 1) hcard (fun _ => by simp) hcorr
  exact ⟨j, by simpa only [mul_one, P, ψ] using h⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

variable {L M A I J : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [Fintype I] [Fintype J] {s t d e N degree : ℕ} [NeZero N]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
  {D : RationalFilteredNilmanifold L s d} {E : RationalFilteredNilmanifold M t e}
  {T : Subgroup D.RealGroup} {S : Subgroup E.RealGroup} {p q : ℝ}
  (V : D.UnitVerticalObservable T I q) (U : E.UnitVerticalObservable S J q)
  (φ : L →ₗ⁅ℚ⁆ M)
  (hφ : D.lattice ≤ E.lattice.comap (mapOfSteps
    (hL := D.filtration.lowerCentralSeries_eq_bot) (hM := E.filtration.lowerCentralSeries_eq_bot) φ))

theorem exists_native_quotient_comparison_correlation (f : A → ZMod N → ℂ)
    (g : ZMod N → D.Space) (hq : 0 ≤ q) (hcard : (Fintype.card J : ℝ) ≤ Real.exp q)
    (W : NativeVectorCorrelation degree N p
      (fun ai : A × I => fun x => f ai.1 x * star (V.observable ai.2 (g x)))) :
    Nonempty (NativeVectorCorrelation degree N (p + q)
      (fun aij : A × (I × J) => fun x =>
        f aij.1 x * star (U.observable aij.2.2 (D.nativeSpaceMap E φ hφ (g x))) *
          star (mapDifferenceObservable V U φ hφ aij.2 (g x)))) := by
  have hcorr : Real.exp (-p) ≤ ‖𝔼 x ∈ (Finset.univ : Finset (ZMod N)),
      (f W.coordinate.1 x * star (W.test.evalCyclic N (fun _ => x))) *
        star (V.observable W.coordinate.2 (g x))‖ := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using W.correlation
  obtain ⟨j, hj⟩ := exists_quotient_comparison_correlation V U φ hφ Finset.univ
    (fun x => f W.coordinate.1 x * star (W.test.evalCyclic N (fun _ => x)))
    g W.coordinate.2 (Real.exp_pos (-p)) (Real.exp_pos q) hcard hcorr
  have hfrac : Real.exp (-p) / Real.exp q = Real.exp (-(p + q)) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [hfrac] at hj
  exact ⟨{
    L := W.L
    dim := W.dim
    model := W.model
    test := W.test
    complexity := W.complexity.mono (le_add_of_nonneg_right hq)
    coordinate := (W.coordinate.1, W.coordinate.2, j)
    correlation := by simpa only [mul_assoc, mul_left_comm, mul_comm] using hj
  }⟩

omit [LieRing M] [LieAlgebra ℚ M] [Fintype J]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)] in
theorem UnitVerticalObservable.onSublattice_native_correlation {r : ℕ}
    (R : D.DegreeRankStructure r) (V : D.UnitVerticalObservable (R.realSubgroup s r) I q)
    (Λ : Subgroup D.filtration.Group) (hΛ : Λ ≤ D.lattice)
    (m : ℕ) (hm : 0 < m)
    (hin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates D.basis Λ)
    (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid m)
    (f : A → ZMod N → ℂ) (g : ZMod N → D.RealGroup)
    (W : NativeVectorCorrelation degree N p
      (fun ai : A × I => fun x => f ai.1 x * star (V.observable ai.2 (QuotientGroup.mk (g x))))) :
    Nonempty (NativeVectorCorrelation degree N p
      (fun ai : A × I => fun x => f ai.1 x *
        star ((V.onSublattice R Λ hΛ m hm hin hout).observable ai.2 (QuotientGroup.mk (g x))))) :=
  ⟨W⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI

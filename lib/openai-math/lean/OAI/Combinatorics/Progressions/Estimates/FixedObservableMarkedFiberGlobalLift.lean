import OAI.Combinatorics.Progressions.Dynamics.TopInvariantReconstructionBudget
import OAI.Combinatorics.Progressions.Nilpotent.TopInvariantNiltestBudget

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L σ τ Ω : Type*} [LieRing L] [LieAlgebra ℚ L] {s d n : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (D : RationalFilteredNilmanifold L (s + 1) d)
  [TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))]
  [T2Space (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))]

theorem exists_fixedObservable_topInvariant_descent
    (Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n)
    (hQF : Q.filtration = D.filtration.quotientTop)
    (hQL : Q.lattice = D.lattice.map
      (D.filtration.quotientStepHom (D.filtration.layerIdeal (s + 1)) le_rfl))
    {v : σ → ℕ} {w : τ → ℕ} (T : D.Niltest v)
    (localTests : Ω → D.Niltest w)
    (hcommon : ∀ a, (localTests a).observable = T.observable)
    (hunit : T.UnitIntervalValued)
    (hinv : ∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
      T.observable (z • x) = T.observable x)
    (H : ℕ) (hH : 1 ≤ H)
    (he : ∀ i j, RationalHeightLE (Q.basis.repr
      (lieQuotientMap (D.filtration.layerIdeal (s + 1)) (D.basis j)) i) H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants Q.basis i j k) H) :
    ∃ (S : Q.Niltest v) (quotientTests : Ω → Q.Niltest w),
      S.orbit = D.topQuotientOrbit Q hQF T.orbit ∧
      S.normBound = T.normBound ∧
      S.lipBound = rationalReconstructionLipschitzBound s d n H T.lipBound T.normBound ∧
      S.UnitIntervalValued ∧
      (∀ g : D.RealGroup, S.observable (QuotientGroup.mk
        (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := Q.filtration.lowerCentralSeries_eq_bot)
          (lieQuotientMap (D.filtration.layerIdeal (s + 1))) g)) =
        T.observable (QuotientGroup.mk g)) ∧
      (∀ x, S.eval x = T.eval x) ∧
      ∀ a, (quotientTests a).observable = S.observable ∧
        (quotientTests a).orbit = D.topQuotientOrbit Q hQF (localTests a).orbit ∧
        (quotientTests a).normBound = S.normBound ∧
        (quotientTests a).lipBound = S.lipBound ∧
        (quotientTests a).UnitIntervalValued ∧
        ∀ x, (quotientTests a).eval x = (localTests a).eval x := by
  have hcover : Q.lattice ≤ D.lattice.map
      (mapOfSteps (lieQuotientMap (D.filtration.layerIdeal (s + 1)))) := by
    rw [hQL]
    exact le_rfl
  obtain ⟨f, hf, hfLip, hfBound⟩ := exists_lipschitz_realification_reconstruction
    D.basis Q.basis (lieQuotientMap (D.filtration.layerIdeal (s + 1)))
    (lieQuotientMap_surjective _) D.lattice Q.lattice hcover
    D.grid Q.grid H D.grid_pos Q.grid_pos hH D.outer_grid Q.outer_grid he hc
    T.observable (fun k hk x => hinv k (by
      apply (realification_mkQ_eq_zero_iff
        (D.filtration.layerIdeal (s + 1)).toSubmodule k.coord).mp
      exact congrArg (fun z : Q.RealGroup => z.coord) (MonoidHom.mem_ker.mp hk))
      (QuotientGroup.mk x)) T.lipBound T.normBound T.lipschitz T.norm_le
  let S : Q.Niltest v := {
    orbit := D.topQuotientOrbit Q hQF T.orbit
    observable := f
    normBound := T.normBound
    lipBound := rationalReconstructionLipschitzBound s d n H T.lipBound T.normBound
    norm_le := hfBound
    lipschitz := by
      let : MetricSpace (Q.RealGroup ⧸ Q.lattice.map realificationHom) :=
        realificationQuotientMetricSpace Q.basis Q.lattice Q.grid Q.grid_pos Q.outer_grid
      exact hfLip.weaken (by simp only [Fintype.card_fin]; exact le_rfl)
  }
  have hsurj : Function.Surjective
      (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Q.filtration.lowerCentralSeries_eq_bot)
        (lieQuotientMap (D.filtration.layerIdeal (s + 1)))) := by
    intro g
    obtain ⟨x, hx⟩ := LinearMap.lTensor_surjective ℝ
      (lieQuotientMap_surjective (D.filtration.layerIdeal (s + 1))) g.coord
    exact ⟨⟨x⟩, NilpotentLieBCHGroup.ext hx⟩
  have hSunit : S.UnitIntervalValued := by
    intro y
    induction y using Quotient.inductionOn with
    | h g =>
      obtain ⟨x, rfl⟩ := hsurj g
      change (f _).im = 0 ∧ 0 ≤ (f _).re ∧ (f _).re ≤ 1
      exact Eq.mpr (congrArg (fun z : ℂ => z.im = 0 ∧ 0 ≤ z.re ∧ z.re ≤ 1)
        (hf x)) (hunit (QuotientGroup.mk x))
  refine ⟨S, fun a => S.withOrbit (D.topQuotientOrbit Q hQF (localTests a).orbit),
    rfl, rfl, rfl, hSunit, hf, ?_, ?_⟩
  · intro x
    exact (congrArg (fun z : Q.RealGroup => f (QuotientGroup.mk z))
      (D.topQuotientOrbit_eval Q hQF T.orbit x)).trans (hf _)
  · intro a
    refine ⟨rfl, rfl, rfl, rfl, hSunit, ?_⟩
    intro x
    change f (QuotientGroup.mk (Q.filtration.realification.polynomialOrbitEval w x
      (D.topQuotientOrbit Q hQF (localTests a).orbit))) = _
    rw [D.topQuotientOrbit_eval Q hQF (localTests a).orbit x, hf]
    exact (congrFun (hcommon a) _).symm

 theorem exists_fixedObservable_topInvariant_descent_budget (s : ℕ) :
     ∃ C : ℕ, 2 ≤ C ∧ ∀ {L σ τ Ω : Type*} [LieRing L] [LieAlgebra ℚ L]
       [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
       [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
       {d n : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
       [TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))]
       [IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))]
       [ContinuousSMul ℝ (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))]
       [T2Space (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))]
       (Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n)
       (hQF : Q.filtration = D.filtration.quotientTop)
       (_hQL : Q.lattice = D.lattice.map
         (D.filtration.quotientStepHom (D.filtration.layerIdeal (s + 1)) le_rfl))
       {v : σ → ℕ} {w : τ → ℕ} (T : D.Niltest v)
       (localTests : Ω → D.Niltest w),
       (∀ a, (localTests a).observable = T.observable) → T.UnitIntervalValued →
       ∀ p : ℝ, 0 ≤ p → T.ComplexityLE p → Q.GeometryComplexityLE p →
       (∀ i j, rationalLogHeight (Q.basis.repr
         (lieQuotientMap (D.filtration.layerIdeal (s + 1)) (D.basis j)) i) ≤ p) →
       (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
         T.observable (z • x) = T.observable x) →
       ∃ (S : Q.Niltest v) (quotientTests : Ω → Q.Niltest w),
         S.orbit = D.topQuotientOrbit Q hQF T.orbit ∧
         S.normBound = T.normBound ∧
         S.lipBound = rationalReconstructionLipschitzBound s d n ⌈Real.exp p⌉₊
           T.lipBound T.normBound ∧
         S.UnitIntervalValued ∧ S.ComplexityLE ((p + C) ^ C) ∧
         (∀ g : D.RealGroup, S.observable (QuotientGroup.mk
           (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
             (hM := Q.filtration.lowerCentralSeries_eq_bot)
             (lieQuotientMap (D.filtration.layerIdeal (s + 1))) g)) =
           T.observable (QuotientGroup.mk g)) ∧
         (∀ x, S.eval x = T.eval x) ∧
         ∀ a, (quotientTests a).observable = S.observable ∧
           (quotientTests a).orbit = D.topQuotientOrbit Q hQF (localTests a).orbit ∧
           (quotientTests a).normBound = S.normBound ∧
           (quotientTests a).lipBound = S.lipBound ∧
           (quotientTests a).UnitIntervalValued ∧
           (quotientTests a).ComplexityLE ((p + C) ^ C) ∧
           ∀ x, (quotientTests a).eval x = (localTests a).eval x := by
   obtain ⟨C, hC, hbudget⟩ := exists_topInvariant_reconstruction_budget s
   refine ⟨C, hC, ?_⟩
   intro L σ τ Ω _ _ _ _ _ _ d n D _ _ _ _ Q hQF hQL v w T localTests
     hcommon hunit p hp hT hQ he hinv
   obtain ⟨S, quotientTests, hSo, hSn, hSl, hSu, hrec, hSe, hfamily⟩ :=
     D.exists_fixedObservable_topInvariant_descent Q hQF hQL T localTests hcommon hunit
       hinv ⌈Real.exp p⌉₊ (one_le_ceil_exp p)
       (fun i j => rationalHeightLE_ceil_exp (he i j))
       (fun i j k => rationalHeightLE_ceil_exp (hQ.2.2.1 i j k))
   have hSc := hbudget D Q T S p hp hT hQ hSn hSl
   refine ⟨S, quotientTests, hSo, hSn, hSl, hSu, hSc, hrec, hSe, ?_⟩
   intro a
   obtain ⟨hobs, ho, hn, hl, hu, heval⟩ := hfamily a
   refine ⟨hobs, ho, hn, hl, hu, ?_, heval⟩
   change Q.GeometryComplexityLE _ ∧ _
   rw [hn, hl]
   exact hSc

 end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L σ τ : Type*} [LieRing L] [LieAlgebra ℚ L] {s d n : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (D : RationalFilteredNilmanifold L (s + 1) d)
  [TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))]
  [T2Space (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))]

theorem exists_fixedObservable_topInvariant_global_lift
    (Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n)
    (hQF : Q.filtration = D.filtration.quotientTop)
    {v : σ → ℕ} {w : τ → ℕ} (T : D.Niltest v) (S : Q.Niltest v)
    (hrec : ∀ g : D.RealGroup, S.observable (QuotientGroup.mk
      (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Q.filtration.lowerCentralSeries_eq_bot)
        (lieQuotientMap (D.filtration.layerIdeal (s + 1))) g)) =
      T.observable (QuotientGroup.mk g))
    (ambient : Q.Niltest w) (hcommon : ambient.observable = S.observable)
    (hunit : T.UnitIntervalValued) :
    ∃ lifted : D.Niltest w,
      lifted.observable = T.observable ∧
      lifted.normBound = T.normBound ∧ lifted.lipBound = T.lipBound ∧
      lifted.UnitIntervalValued ∧
      D.topQuotientOrbit Q hQF lifted.orbit = ambient.orbit ∧
      (∀ p, lifted.ComplexityLE p ↔ T.ComplexityLE p) ∧
      ∀ x, lifted.eval x = ambient.eval x := by
  obtain ⟨g, hg⟩ := D.topQuotientOrbit_surjective Q hQF ambient.orbit
  refine ⟨T.withOrbit g, rfl, rfl, rfl, hunit, hg, fun _ => Iff.rfl, ?_⟩
  intro x
  have heval := D.topQuotientOrbit_eval Q hQF g x
  rw [hg] at heval
  calc
    (T.withOrbit g).eval x = S.observable (QuotientGroup.mk
        (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := Q.filtration.lowerCentralSeries_eq_bot)
          (lieQuotientMap (D.filtration.layerIdeal (s + 1)))
          (D.filtration.realification.polynomialOrbitEval w x g))) := (hrec _).symm
    _ = S.observable (QuotientGroup.mk
        (Q.filtration.realification.polynomialOrbitEval w x ambient.orbit)) :=
      congrArg (fun z : Q.RealGroup => S.observable (QuotientGroup.mk z)) heval.symm
    _ = ambient.eval x := (congrFun hcommon _).symm

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup NilpotentLieFiltration VectorPolynomial
open scoped TensorProduct NNReal

variable {L M σ τ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d n : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L (s + 1) d)
    [TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))]
    [T2Space (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))]

theorem exists_fixedObservable_marked_fiber_global_lift
    (G : NilpotentLieFiltration M (s + 1))
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ G.layer j)
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n)
    (hQF : Q.filtration = D.filtration.quotientTop)
    {v : σ → ℕ} {w : τ → ℕ} (T : D.Niltest v) (S : Q.Niltest v)
    (hrec : ∀ g : D.RealGroup, S.observable (QuotientGroup.mk
      (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Q.filtration.lowerCentralSeries_eq_bot)
        (lieQuotientMap (D.filtration.layerIdeal (s + 1))) g)) =
      T.observable (QuotientGroup.mk g))
    (ambient : Q.Niltest w) (hcommon : ambient.observable = S.observable)
    (hunit : T.UnitIntervalValued)
    (marked : G.realification.PolynomialOrbit w)
    (hcompat : map
      (realLieHomToRat (realificationLieHom
        (lieQuotientProjection (D.filtration.layerIdeal (s + 1))
          (G.layerIdeal (s + 1)) φ (hφ (s + 1))))).toLinearMap ambient.orbit.log =
      map (realLieHomToRat (realificationLieHom
        (lieQuotientMap (G.layerIdeal (s + 1))))).toLinearMap marked.log) :
    ∃ lifted : D.Niltest w,
      lifted.observable = T.observable ∧
      lifted.normBound = T.normBound ∧ lifted.lipBound = T.lipBound ∧
      lifted.UnitIntervalValued ∧
      D.topQuotientOrbit Q hQF lifted.orbit = ambient.orbit ∧
      map (realLieHomToRat (realificationLieHom φ)).toLinearMap lifted.orbit.log =
        marked.log ∧
      (∀ p, lifted.ComplexityLE p ↔ T.ComplexityLE p) ∧
      (∀ x, lifted.eval x = ambient.eval x) ∧
      ∀ z : τ → ℝ, realificationMap
        (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := G.lowerCentralSeries_eq_bot) φ
        (D.filtration.realification.polynomialOrbitRealEval w z lifted.orbit) =
          G.realification.polynomialOrbitRealEval w z marked := by
  obtain ⟨g, hg, hm, _, hmeval⟩ :=
    D.exists_prescribed_marked_topQuotientOrbit_lift G φ hφ Q hQF hsurj
      ambient.orbit marked hcompat
  refine ⟨T.withOrbit g, rfl, rfl, rfl, hunit, hg, hm, fun _ => Iff.rfl, ?_, hmeval⟩
  intro x
  have heval := D.topQuotientOrbit_eval Q hQF g x
  rw [hg] at heval
  calc
    (T.withOrbit g).eval x = S.observable (QuotientGroup.mk
        (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := Q.filtration.lowerCentralSeries_eq_bot)
          (lieQuotientMap (D.filtration.layerIdeal (s + 1)))
          (D.filtration.realification.polynomialOrbitEval w x g))) := (hrec _).symm
    _ = S.observable (QuotientGroup.mk
        (Q.filtration.realification.polynomialOrbitEval w x ambient.orbit)) :=
      congrArg (fun z : Q.RealGroup => S.observable (QuotientGroup.mk z)) heval.symm
    _ = ambient.eval x := (congrFun hcommon _).symm

end Erdos3.RationalFilteredNilmanifold

end

end OAI

import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateAdaptedOptionQuotientFactors
import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateSelectedDescentRegularity

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_external_kernelProjection_native_descent (t : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L σ X : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {s d n : ℕ} (D : RationalFilteredNilmanifold L s d) (I : LieIdeal ℚ L)
      [TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ I))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ I))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (L ⧸ I))] [T2Space (ℝ ⊗[ℚ] (L ⧸ I))]
      (hI : D.filtration.layer (t + 1) ≤ I.toSubmodule)
      (Q : RationalFilteredNilmanifold (L ⧸ I) t n)
      (hQF : Q.filtration = D.filtration.quotientLie I hI)
      (_hQL : Q.lattice = D.lattice.map (D.filtration.quotientStepHom I hI))
      (htop : I.toSubmodule ≤ D.filtration.layer s)
      {w : σ → ℕ} (tests : X → D.Niltest w) (p : ℝ),
      0 ≤ p → (∀ x, (tests x).ComplexityLE p) →
      (∀ x, (tests x).UnitIntervalValued) → Q.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (Q.basis.repr (lieQuotientMap I (D.basis j)) i) ≤ p) →
      ∃ descended : X → Q.Niltest w,
        (∀ x, (descended x).orbit = D.quotientOrbit I hI Q hQF (tests x).orbit) ∧
        (∀ x, (descended x).normBound = (tests x).normBound) ∧
        (∀ x, (descended x).UnitIntervalValued) ∧
        (∀ x, (descended x).ComplexityLE ((p + 2) ^ C)) ∧
        (∀ x, ((descended x).lipBound : ℝ) ≤ Real.exp ((p + 2) ^ C)) ∧
        (∀ x (g : D.RealGroup), (descended x).observable (QuotientGroup.mk
          (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap I) g)) =
          ((tests x).kernelProjection I.toSubmodule htop).observable (QuotientGroup.mk g)) ∧
        (∀ x z, (descended x).eval z = ((tests x).kernelProjection I.toSubmodule htop).eval z) ∧
        (∀ x y η, (∀ z, ‖(tests x).observable z - (tests y).observable z‖ ≤ η) →
          ∀ q, ‖(descended x).observable q - (descended y).observable q‖ ≤ η) := by
  obtain ⟨C, hC, hdescent⟩ := exists_idealInvariant_niltest_budget t
  refine ⟨C, hC, ?_⟩
  intro L σ X _ _ _ _ _ _ s d n D I _ _ _ _ hI Q hQF hQL htop w tests p
    hp htests hunit hQ he
  have hex (x : X) := hdescent D I hI Q hQF hQL
    ((tests x).kernelProjection I.toSubmodule htop) p hp
    ((tests x).kernelProjection_complexity I.toSubmodule htop (htests x)) hQ he
    (fun z hz y => (tests x).kernelProjection_invariant I.toSubmodule htop z hz y)
  choose descended horbit hnorm hcomplex hrec heval hpos using hex
  have hpositive (x : X) : (descended x).UnitIntervalValued :=
    hpos x ((tests x).kernelProjection_unitInterval I.toSubmodule htop (hunit x))
  refine ⟨descended, horbit, hnorm, hpositive, hcomplex, ?_, hrec, heval, ?_⟩
  · intro x
    have hb := (descended x).observable_budget (hcomplex x)
    linarith [(descended x).normBound.coe_nonneg]
  · intro x y η hxy
    exact Niltest.nativeQuotient_observable_sub_norm_le
      (tests x) (tests y) I htop Q (descended x).observable (descended y).observable
      (hrec x) (hrec y) hxy

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold
open VectorPolynomial NilpotentLieFiltration
open scoped TensorProduct NNReal

theorem exists_external_kernel_quotient_transfer (t : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L σ X : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {s d n : ℕ} (D : RationalFilteredNilmanifold L s d) (I : LieIdeal ℚ L)
      [TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ I))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ I))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (L ⧸ I))] [T2Space (ℝ ⊗[ℚ] (L ⧸ I))]
      (hI : D.filtration.layer (t + 1) ≤ I.toSubmodule)
      (Q : RationalFilteredNilmanifold (L ⧸ I) t n)
      (_hQF : Q.filtration = D.filtration.quotientLie I hI)
      (_hQL : Q.lattice = D.lattice.map (D.filtration.quotientStepHom I hI))
      (_htop : I.toSubmodule ≤ D.filtration.layer s)
      {w : σ → ℕ} (tests : X → D.Niltest w) (p : ℝ),
      0 ≤ p → (∀ x, (tests x).ComplexityLE p) →
      (∀ x, (tests x).UnitIntervalValued) → Q.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (Q.basis.repr (lieQuotientMap I (D.basis j)) i) ≤ p) →
      ∃ descended : X → Q.Niltest w,
        (∀ x, (descended x).UnitIntervalValued) ∧
        (∀ x, (descended x).ComplexityLE ((p + 2) ^ C)) ∧
        (∀ x y η, (∀ z, ‖(tests x).observable z - (tests y).observable z‖ ≤ η) →
          ∀ q, ‖(descended x).observable q - (descended y).observable q‖ ≤ η) ∧
        ∀ {M Ω J : Type*} [LieRing M] [LieAlgebra ℚ M] [Fintype Ω] [Fintype J]
          {u : ℕ} (G : NilpotentLieFiltration M u) (φ : L →ₗ⁅ℚ⁆ M)
          (hker : ∀ x ∈ I, φ x = 0)
          (q : Q.filtration.realification.PolynomialOrbit w)
          (marked : G.realification.PolynomialOrbit w),
          map ((realificationLieHom (quotientInducedMark I φ hker)).toLinearMap.restrictScalars ℚ)
            q.log = marked.log →
          ∀ (outer : FiniteProbabilityWeights Ω) (H : Finset Ω), 0 < outer.mass H →
          ∀ (localLaw : Ω → FiniteProbabilityWeights J)
            (physical : Ω → J → X) (point : Ω → J → σ → ℤ) (weight : X → ℂ)
            {B δ : ℝ}, 0 < B → 0 < δ →
            (∀ a ∈ H, ∀ j, ‖weight (physical a j)‖ ≤ B) →
            (∀ a ∈ H, δ ≤ ((localLaw a).complexMean (fun j => weight (physical a j) *
              ((descended (physical a j)).withOrbit q).eval (point a j))).re) →
          ∃ restored : D.filtration.realification.PolynomialOrbit w,
            map (realLieHomToRat (realificationLieHom φ)).toLinearMap restored.log = marked.log ∧
            (∀ x, ((tests x).withOrbit restored).observable = (tests x).observable ∧
              ((tests x).withOrbit restored).UnitIntervalValued ∧
              ∀ p', ((tests x).withOrbit restored).ComplexityLE p' ↔ (tests x).ComplexityLE p') ∧
            ∃ H' : Finset Ω, H' ⊆ H ∧ 0 < outer.mass H' ∧
              δ / (2 * B) * outer.mass H ≤ outer.mass H' ∧
              ∀ a ∈ H', δ / 2 ≤ ((localLaw a).complexMean (fun j => weight (physical a j) *
                ((tests (physical a j)).withOrbit restored).eval (point a j))).re := by
  obtain ⟨C, hC, hdescent⟩ := exists_external_kernelProjection_native_descent t
  refine ⟨C, hC, ?_⟩
  intro L σ X _ _ _ _ _ _ s d n D I _ _ _ _ hI Q hQF hQL htop w tests p
    hp htests hunit hQ he
  obtain ⟨descended, _, _, hpositive, hcomplex, _, hrec, _, hcontraction⟩ :=
    hdescent D I hI Q hQF hQL htop tests p hp htests hunit hQ he
  refine ⟨descended, hpositive, hcomplex, hcontraction, ?_⟩
  intro M Ω J _ _ _ _ u G φ hker q marked hmark outer H hH localLaw physical point weight
    B δ hB hδ hweight hscore
  exact D.exists_external_marked_quotient_restoration I hI Q hQF G φ hker htop
    tests hunit (fun x => (descended x).observable) hrec q marked hmark
    outer H hH localLaw physical point weight hB hδ hweight hscore

end Erdos3.RationalFilteredNilmanifold

end

end OAI

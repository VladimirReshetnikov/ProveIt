import OAI.Combinatorics.Progressions.Estimates.NativeDilationOrbit
import OAI.Combinatorics.Progressions.Estimates.SourceUnitCover
import OAI.Combinatorics.Progressions.Fourier.DilationFrequencyPhase
import OAI.Combinatorics.Progressions.Geometry.FiniteSumCoordinate
import OAI.Combinatorics.Progressions.Linear.NativeTripleProjections
import OAI.Combinatorics.Progressions.Nilpotent.TopInvariantNiltestBudget
import OAI.Combinatorics.Progressions.Polynomial.TriplePhaseCancellation

namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def realifiedAdditiveTripleOrbit {τ : Type*} (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) {v : τ → ℕ}
    (q : (F.realification.additiveTripleFiltration i hi c hc).PolynomialOrbit v) :
    (F.additiveTripleFiltration i hi c hc).realification.PolynomialOrbit v :=
  NilpotentLieFiltration.polynomialOrbitOfLog
    (VectorPolynomial.map (F.realifiedAdditiveTripleEquiv i hi c hc).symm.toLinearMap q.log)
    ((F.realification.additiveTripleFiltration i hi c hc).adapted_map
      (F.additiveTripleFiltration i hi c hc).realification
      (F.realifiedAdditiveTripleEquiv i hi c hc).symm.toLinearMap
      (fun n x hx => (F.realifiedAdditiveTripleEquiv_symm_mem_layer i hi c hc n x).mpr hx) v q.adapted)

theorem realifiedAdditiveTripleOrbit_eval {τ : Type*} (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) {v : τ → ℕ}
    (q : (F.realification.additiveTripleFiltration i hi c hc).PolynomialOrbit v) (x : τ → ℤ) :
    F.realifiedAdditiveTripleEquiv i hi c hc
      (((F.additiveTripleFiltration i hi c hc).realification.polynomialOrbitEval v x
        (F.realifiedAdditiveTripleOrbit i hi c hc q)).coord) =
      ((F.realification.additiveTripleFiltration i hi c hc).polynomialOrbitEval v x q).coord := by
  change F.realifiedAdditiveTripleEquiv i hi c hc
    (eval (fun j => (x j : ℚ)) (VectorPolynomial.map
      (F.realifiedAdditiveTripleEquiv i hi c hc).symm.toLinearMap q.log)) = _
  rw [eval_map]
  exact (F.realifiedAdditiveTripleEquiv i hi c hc).apply_symm_apply _

theorem realifiedAdditiveTripleOrbit_zero {τ : Type*} (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) {v : τ → ℕ}
    (q : (F.realification.additiveTripleFiltration i hi c hc).PolynomialOrbit v)
    (hq : (F.realification.additiveTripleFiltration i hi c hc).polynomialOrbitEval v 0 q = 1) :
    (F.additiveTripleFiltration i hi c hc).realification.polynomialOrbitEval v 0
      (F.realifiedAdditiveTripleOrbit i hi c hc q) = 1 := by
  apply NilpotentLieBCHGroup.ext
  apply (F.realifiedAdditiveTripleEquiv i hi c hc).injective
  rw [F.realifiedAdditiveTripleOrbit_eval, hq]
  exact (map_zero _).symm

theorem exists_real_normalized_addition_orbit (i : σ) (hi : bound i ≤ 1)
    (p : F.realification.PolynomialOrbit) (a b : F.realification.Group)
    (hp0 : F.realification.polynomialOrbitEval 0 p = a * b) :
    ∃ g : (F.additiveTripleFiltration i hi (omittedCoordinateWeight i)
        (omittedCoordinateWeight_le_one i)).realification.PolynomialOrbit (fun _ : Option σ => 1),
      (F.additiveTripleFiltration i hi (omittedCoordinateWeight i)
        (omittedCoordinateWeight_le_one i)).realification.polynomialOrbitEval _ 0 g = 1 ∧
      ∀ x : Option σ → ℤ,
        let h := (F.additiveTripleFiltration i hi (omittedCoordinateWeight i)
          (omittedCoordinateWeight_le_one i)).realification.polynomialOrbitEval _ x g
        F.realAdditiveTripleProjection i hi _ (omittedCoordinateWeight_le_one i) 0 h =
          a⁻¹ * F.realification.polynomialOrbitEval
            (Function.update (fun j => x (some j)) i (x (some i) + x none)) p * b⁻¹ ∧
        F.realAdditiveTripleProjection i hi _ (omittedCoordinateWeight_le_one i) 1 h =
          a⁻¹ * F.realification.polynomialOrbitEval (fun j => x (some j)) p * b⁻¹ ∧
        F.realAdditiveTripleProjection i hi _ (omittedCoordinateWeight_le_one i) 2 h =
          a⁻¹ * F.realification.polynomialOrbitEval
            (Function.update (fun j => x (some j)) i (x none)) p * b⁻¹ := by
  obtain ⟨q, hq0, hq⟩ := F.realification.exists_normalizedCoordinateAddition_orbit i hi p a b hp0
  refine ⟨F.realifiedAdditiveTripleOrbit i hi _ (omittedCoordinateWeight_le_one i) q,
    F.realifiedAdditiveTripleOrbit_zero i hi _ (omittedCoordinateWeight_le_one i) q hq0, ?_⟩
  intro x
  dsimp only
  have he (j : Fin 3) := F.realAdditiveTripleProjection_coord i hi _
    (omittedCoordinateWeight_le_one i) j
    ((F.additiveTripleFiltration i hi (omittedCoordinateWeight i)
      (omittedCoordinateWeight_le_one i)).realification.polynomialOrbitEval _ x
      (F.realifiedAdditiveTripleOrbit i hi _ (omittedCoordinateWeight_le_one i) q))
  simp only [F.realifiedAdditiveTripleOrbit_eval, hq x] at he
  exact ⟨NilpotentLieBCHGroup.ext (he 0), NilpotentLieBCHGroup.ext (he 1),
    NilpotentLieBCHGroup.ext (he 2)⟩

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3

namespace RationalFilteredNilmanifold.MultidegreeStructure

open CircleFourier
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)
  (i : σ) (hi : bound i ≤ 1) (c : σ → ℕ) (hc : ∀ j, c j ≤ 1)
  (E : RationalFilteredNilmanifold (M.filtration.additiveTripleSubalgebra i hi c hc) s r)
  (hEL : E.lattice = M.additiveTripleLattice i hi c hc)

noncomputable def tripleObservable (ε : D.RealGroup) (u : Fin 3 → D.Space → ℂ) (x : E.Space) : ℂ :=
  u 0 (ε • M.tripleSpaceProjection i hi c hc E hEL 0 x) *
    star (u 1 (ε • M.tripleSpaceProjection i hi c hc E hEL 1 x)) *
    star (u 2 (ε • M.tripleSpaceProjection i hi c hc E hEL 2 x))

theorem tripleObservable_mk (ε : D.RealGroup) (u : Fin 3 → D.Space → ℂ) (g : E.RealGroup) :
    M.tripleObservable i hi c hc E hEL ε u (QuotientGroup.mk g) =
      u 0 (QuotientGroup.mk (ε * M.filtration.realAdditiveTripleProjection i hi c hc 0 g)) *
        star (u 1 (QuotientGroup.mk (ε * M.filtration.realAdditiveTripleProjection i hi c hc 1 g))) *
        star (u 2 (QuotientGroup.mk (ε * M.filtration.realAdditiveTripleProjection i hi c hc 2 g))) := rfl

theorem tripleObservable_norm_le (ε : D.RealGroup) (u : Fin 3 → D.Space → ℂ)
    (hu : ∀ j x, ‖u j x‖ ≤ 1) (x : E.Space) :
    ‖M.tripleObservable i hi c hc E hEL ε u x‖ ≤ 1 := by
  simp only [tripleObservable, norm_mul, norm_star]
  have h01 : ‖u 0 (ε • M.tripleSpaceProjection i hi c hc E hEL 0 x)‖ *
      ‖u 1 (ε • M.tripleSpaceProjection i hi c hc E hEL 1 x)‖ ≤ 1 := by
    simpa only [mul_one] using mul_le_mul (hu 0 _) (hu 1 _) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  simpa only [mul_one] using mul_le_mul h01 (hu 2 _) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

theorem tripleSpaceProjection_top_smul (ε : D.RealGroup) (j : Fin 3) (k : E.RealGroup)
    (hk : k ∈ (M.filtration.additiveTripleFiltration i hi c hc).realification.subgroup s)
    (x : E.Space) :
    ε • M.tripleSpaceProjection i hi c hc E hEL j (k • x) =
      M.filtration.realAdditiveTripleProjection i hi c hc j k •
        (ε • M.tripleSpaceProjection i hi c hc E hEL j x) := by
  have hz := M.filtration.realAdditiveTripleProjection_mem i hi c hc j hk
  rw [M.tripleSpaceProjection_smul, ← mul_smul, ← mul_smul,
    (M.filtration.realification.ordinary.top_commutes _ hz ε).eq]

theorem tripleObservable_component_top (ε : D.RealGroup) (u : D.Space → ℂ)
    (χ : D.RealGroup → CircleFourier.Circle)
    (hu : ∀ z, z ∈ M.filtration.realification.ordinary.subgroup s →
      ∀ x, u (z • x) = character (χ z) * u x)
    (j : Fin 3) (k : E.RealGroup)
    (hk : k ∈ (M.filtration.additiveTripleFiltration i hi c hc).realification.subgroup s)
    (x : E.Space) :
    u (ε • M.tripleSpaceProjection i hi c hc E hEL j (k • x)) =
      character (χ (M.filtration.realAdditiveTripleProjection i hi c hc j k)) *
        u (ε • M.tripleSpaceProjection i hi c hc E hEL j x) := by
  rw [M.tripleSpaceProjection_top_smul i hi c hc E hEL ε j k hk x]
  exact hu _ (M.filtration.realAdditiveTripleProjection_mem i hi c hc j hk) _

theorem tripleObservable_top_invariant
    (ε : D.RealGroup) (u : Fin 3 → D.Space → ℂ) (χ : D.RealGroup → CircleFourier.Circle)
    (hu : ∀ j z, z ∈ M.filtration.realification.ordinary.subgroup s →
      ∀ x, u j (z • x) = character (χ z) * u j x)
    (k : E.RealGroup)
    (hk : k ∈ (M.filtration.additiveTripleFiltration i hi c hc).realification.subgroup s)
    (hphase : χ (M.filtration.realAdditiveTripleProjection i hi c hc 0 k) =
      χ (M.filtration.realAdditiveTripleProjection i hi c hc 1 k) +
        χ (M.filtration.realAdditiveTripleProjection i hi c hc 2 k))
    (x : E.Space) :
    M.tripleObservable i hi c hc E hEL ε u (k • x) =
      M.tripleObservable i hi c hc E hEL ε u x := by
  have hvalue (j : Fin 3) := M.tripleObservable_component_top i hi c hc E hEL ε (u j) χ (hu j) j k hk x
  have hprod := congrArg₂ (fun a b : ℂ => a * b)
    (congrArg₂ (fun a b : ℂ => a * star b) (hvalue 0) (hvalue 1))
    (congrArg star (hvalue 2))
  exact hprod.trans (triple_phase_cancellation
    (fun j => u j (ε • M.tripleSpaceProjection i hi c hc E hEL j x))
    (fun j => χ (M.filtration.realAdditiveTripleProjection i hi c hc j k)) hphase)

end RationalFilteredNilmanifold.MultidegreeStructure
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem exists_native_addition_orbit (i : σ) (hi : bound i ≤ 1)
    (E : RationalFilteredNilmanifold (M.filtration.additiveTripleSubalgebra i hi
      (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) s r)
    (hEF : E.filtration = M.filtration.additiveTripleFiltration i hi
      (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))
    (g : M.filtration.realification.PolynomialOrbit) (ε γ : D.RealGroup)
    (hγ : γ ∈ D.realLattice) (hfactor : M.filtration.realification.polynomialOrbitEval 0 g = ε * γ) :
    ∃ q : E.filtration.realification.PolynomialOrbit (fun _ : Option σ => 1),
      E.filtration.realification.polynomialOrbitEval _ 0 q = 1 ∧
      ∀ (x : Option σ → ℤ) (j : Fin 3),
        (QuotientGroup.mk (ε * M.filtration.realAdditiveTripleProjection i hi
          (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i) j
          (E.filtration.realification.polynomialOrbitEval _ x q)) : D.Space) =
          QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval (coordinateAdditionInputs i x j) g) := by
  let F := M.filtration.additiveTripleFiltration i hi
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)
  obtain ⟨q, hq0, hq⟩ := M.filtration.exists_real_normalized_addition_orbit i hi g ε γ hfactor
  have hF : F.realification = E.filtration.realification := by rw [hEF]
  let qE := F.realification.orbitEquivOfEq hF (fun _ : Option σ => 1) q
  have hqE (x : Option σ → ℤ) : E.filtration.realification.polynomialOrbitEval _ x qE =
      F.realification.polynomialOrbitEval _ x q := F.realification.orbitEquivOfEq_eval hF _ q x
  have hvalues (x : Option σ → ℤ) (j : Fin 3) :
      M.filtration.realAdditiveTripleProjection i hi _ (omittedCoordinateWeight_le_one i) j
        (F.realification.polynomialOrbitEval _ x q) =
          ε⁻¹ * M.filtration.realification.polynomialOrbitEval (coordinateAdditionInputs i x j) g * γ⁻¹ := by
    fin_cases j
    · exact (hq x).1
    · exact (hq x).2.1
    · exact (hq x).2.2
  refine ⟨qE, (hqE 0).trans hq0, ?_⟩
  intro x j
  rw [hqE, hvalues]
  simp only [← mul_assoc, mul_inv_cancel, one_mul]
  exact QuotientGroup.mk_mul_of_mem _ (D.realLattice.inv_mem hγ)

theorem tripleObservable_of_addition_values (i : σ) (hi : bound i ≤ 1)
    (E : RationalFilteredNilmanifold (M.filtration.additiveTripleSubalgebra i hi
      (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) s r)
    (hEL : E.lattice = M.additiveTripleLattice i hi
      (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))
    (g : M.filtration.realification.PolynomialOrbit) (ε : D.RealGroup)
    (q : E.filtration.realification.PolynomialOrbit (fun _ : Option σ => 1))
    (hvalues : ∀ (x : Option σ → ℤ) (j : Fin 3),
      (QuotientGroup.mk (ε * M.filtration.realAdditiveTripleProjection i hi
        (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i) j
        (E.filtration.realification.polynomialOrbitEval _ x q)) : D.Space) =
        QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval (coordinateAdditionInputs i x j) g))
    (u : Fin 3 → D.Space → ℂ) (x : Option σ → ℤ) :
    M.tripleObservable i hi _ (omittedCoordinateWeight_le_one i) E hEL ε u
      (QuotientGroup.mk (E.filtration.realification.polynomialOrbitEval _ x q)) =
        u 0 (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval (coordinateAdditionInputs i x 0) g)) *
        star (u 1 (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval (coordinateAdditionInputs i x 1) g))) *
        star (u 2 (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval (coordinateAdditionInputs i x 2) g))) := by
  rw [M.tripleObservable_mk, hvalues x 0, hvalues x 1, hvalues x 2]

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3

open CircleFourier
open scoped TensorProduct BigOperators

theorem real_top_frequency_mul {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (η : L →ₗ[ℚ] ℚ)
    (z w : F.realification.Group) (hz : z ∈ F.realification.subgroup s) :
    ((realifyFunctional η (z * w).coord : ℝ) : CircleFourier.Circle) =
      (realifyFunctional η z.coord : CircleFourier.Circle) +
        (realifyFunctional η w.coord : CircleFourier.Circle) := by
  change ((realifyFunctional η (lieBCH s z.coord w.coord) : ℝ) : CircleFourier.Circle) = _
  rw [lieBCH_eq_add_of_lie_eq_zero F.realification.lowerCentralSeries_eq_bot
    (F.realification.top_layer_central hz w.coord), map_add, AddCircle.coe_add]

theorem MultidegreeLieFiltration.realAdditiveTriple_frequency_phase
    {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)
    (i : σ) (hi : bound i ≤ 1) (c : σ → ℕ) (hc : ∀ j, c j ≤ 1)
    (htop : F.realification.weightedLayer c s = ⊥) (η : L →ₗ[ℚ] ℚ)
    (g : (F.additiveTripleFiltration i hi c hc).realification.Group)
    (hg : g ∈ (F.additiveTripleFiltration i hi c hc).realification.subgroup s) :
    (realifyFunctional η (F.realAdditiveTripleProjection i hi c hc 0 g).coord : CircleFourier.Circle) =
      (realifyFunctional η (F.realAdditiveTripleProjection i hi c hc 1 g).coord : CircleFourier.Circle) +
        (realifyFunctional η (F.realAdditiveTripleProjection i hi c hc 2 g).coord : CircleFourier.Circle) := by
  apply F.realAdditiveTriple_top_phase i hi c hc htop
    (fun z => (realifyFunctional η z.coord : CircleFourier.Circle)) ?_ g hg
  intro z w hz _
  exact real_top_frequency_mul F.ordinary η z w hz

theorem MultidegreeLieFiltration.realAdditiveTriple_omitted_frequency_phase
    {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)
    (i : σ) (hi : bound i = 1) (hs : ∑ j, bound j = s) (η : L →ₗ[ℚ] ℚ)
    (g : (F.additiveTripleFiltration i hi.le (omittedCoordinateWeight i)
      (omittedCoordinateWeight_le_one i)).realification.Group)
    (hg : g ∈ (F.additiveTripleFiltration i hi.le (omittedCoordinateWeight i)
      (omittedCoordinateWeight_le_one i)).realification.subgroup s) :
    (realifyFunctional η (F.realAdditiveTripleProjection i hi.le _
      (omittedCoordinateWeight_le_one i) 0 g).coord : CircleFourier.Circle) =
      (realifyFunctional η (F.realAdditiveTripleProjection i hi.le _
        (omittedCoordinateWeight_le_one i) 1 g).coord : CircleFourier.Circle) +
      (realifyFunctional η (F.realAdditiveTripleProjection i hi.le _
        (omittedCoordinateWeight_le_one i) 2 g).coord : CircleFourier.Circle) :=
  F.realAdditiveTriple_frequency_phase i hi.le _ (omittedCoordinateWeight_le_one i)
    (F.realification.omitted_weighted_top i hi hs) η g hg

namespace RationalFilteredNilmanifold.MultidegreeStructure

variable {σ L I : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  [Fintype I] {s d r : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (M : D.MultidegreeStructure bound)

omit [DecidableEq σ] in
theorem unitVertical_top_action (hs : ∑ j, bound j = s)
    {p : ℝ} (V : D.UnitVerticalObservable (M.realSubgroup bound) I p)
    (a : I) (z : D.RealGroup) (hz : z ∈ M.filtration.realification.ordinary.subgroup s)
    (x : D.Space) : V.observable a (z • x) =
      character (realifyFunctional V.frequency z.coord : CircleFourier.Circle) * V.observable a x := by
  have htop : M.realSubgroup bound = M.filtration.realification.ordinary.subgroup s := by
    rw [M.realSubgroup_top, hs]
    change D.filtration.realification.subgroup s = M.filtration.ordinary.realification.subgroup s
    rw [M.ordinary]
  exact V.vertical a z (htop.symm ▸ hz) x

theorem unitVertical_triple_top_invariant (i : σ) (hi : bound i = 1)
    (hs : ∑ j, bound j = s)
    (E : RationalFilteredNilmanifold (M.filtration.additiveTripleSubalgebra i hi.le
      (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) s r)
    (hEL : E.lattice = M.additiveTripleLattice i hi.le
      (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))
    {p : ℝ} (V : D.UnitVerticalObservable (M.realSubgroup bound) I p)
    (ε : D.RealGroup) (a : Fin 3 → I) (k : E.RealGroup)
    (hk : k ∈ (M.filtration.additiveTripleFiltration i hi.le
      (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)).realification.subgroup s)
    (x : E.Space) :
    M.tripleObservable i hi.le _ (omittedCoordinateWeight_le_one i) E hEL ε
        (fun j => V.observable (a j)) (k • x) =
      M.tripleObservable i hi.le _ (omittedCoordinateWeight_le_one i) E hEL ε
        (fun j => V.observable (a j)) x := by
  apply M.tripleObservable_top_invariant i hi.le _ (omittedCoordinateWeight_le_one i) E hEL
    ε (fun j => V.observable (a j))
    (fun z => (realifyFunctional V.frequency z.coord : CircleFourier.Circle)) ?_ k hk ?_ x
  · intro j z hz y
    exact M.unitVertical_top_action hs V (a j) z hz y
  · exact M.filtration.realAdditiveTriple_omitted_frequency_phase i hi hs V.frequency ⟨k.coord⟩ hk

end RationalFilteredNilmanifold.MultidegreeStructure
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

variable {σ L I : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  [Fintype I] {s d r n : ℕ} {D : RationalFilteredNilmanifold L (s + 1) d} {bound : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (M : D.MultidegreeStructure bound) (i : σ) (hi : bound i = 1)
  (hs : ∑ j, bound j = s + 1)

variable (E : RationalFilteredNilmanifold (M.filtration.additiveTripleSubalgebra i hi.le (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) (s + 1) r)
  (hEF : E.filtration = M.filtration.additiveTripleFiltration i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))
  (hEL : E.lattice = M.additiveTripleLattice i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))
  [TopologicalSpace (ℝ ⊗[ℚ] (M.filtration.additiveTripleSubalgebra i hi.le (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (M.filtration.additiveTripleSubalgebra i hi.le (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (M.filtration.additiveTripleSubalgebra i hi.le (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)))] [T2Space (ℝ ⊗[ℚ] (M.filtration.additiveTripleSubalgebra i hi.le (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)))]

variable (Q : RationalFilteredNilmanifold ((M.filtration.additiveTripleSubalgebra i hi.le (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) ⧸ (E.filtration.layerIdeal (s + 1))) s n)
  (hQL : Q.lattice = E.lattice.map (E.filtration.quotientStepHom (E.filtration.layerIdeal (s + 1)) (t := s) le_rfl))
  [TopologicalSpace (ℝ ⊗[ℚ] ((M.filtration.additiveTripleSubalgebra i hi.le (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) ⧸ (E.filtration.layerIdeal (s + 1))))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] ((M.filtration.additiveTripleSubalgebra i hi.le (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) ⧸ (E.filtration.layerIdeal (s + 1))))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] ((M.filtration.additiveTripleSubalgebra i hi.le (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) ⧸ (E.filtration.layerIdeal (s + 1))))] [T2Space (ℝ ⊗[ℚ] ((M.filtration.additiveTripleSubalgebra i hi.le (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) ⧸ (E.filtration.layerIdeal (s + 1))))]

include hs hEF hQL

theorem exists_lipschitz_unitVertical_triple_descent
    {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ j k, RationalHeightLE (Q.basis.repr (lieQuotientMap (E.filtration.layerIdeal (s + 1)) (E.basis k)) j) H)
    (hstructure : ∀ a b c, RationalHeightLE (lieStructureConstants Q.basis a b c) H)
    {p : ℝ} (V : D.UnitVerticalObservable (M.realSubgroup bound) I p)
    (ε : D.RealGroup) (a : Fin 3 → I) (A : ℝ≥0)
    (hLip : letI := E.metricSpace
      LipschitzWith A (M.tripleObservable i hi.le _ (omittedCoordinateWeight_le_one i)
        E hEL ε (fun j => V.observable (a j)))) :
    letI := Q.metricSpace
    ∃ v : Q.Space → ℂ,
      (∀ g : E.RealGroup, v (QuotientGroup.mk (realificationMap
        (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap (E.filtration.layerIdeal (s + 1))) g)) =
          M.tripleObservable i hi.le _ (omittedCoordinateWeight_le_one i)
            E hEL ε (fun j => V.observable (a j)) (QuotientGroup.mk g)) ∧
      LipschitzWith (rationalReconstructionLipschitzBound s r n H A 1) v ∧
      ∀ x, ‖v x‖ ≤ 1 := by
  let : MetricSpace (Q.RealGroup ⧸ Q.lattice.map realificationHom) :=
    realificationQuotientMetricSpace Q.basis Q.lattice Q.grid Q.grid_pos Q.outer_grid
  have hcover : Q.lattice ≤ E.lattice.map (mapOfSteps
      (hL := E.filtration.lowerCentralSeries_eq_bot)
      (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap (E.filtration.layerIdeal (s + 1)))) := by
    rw [hQL]
    exact le_rfl
  have hker : ∀ k ∈ (realificationMap
      (hnil := E.filtration.lowerCentralSeries_eq_bot)
      (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap (E.filtration.layerIdeal (s + 1)))).ker,
      ∀ x : E.RealGroup,
        M.tripleObservable i hi.le _ (omittedCoordinateWeight_le_one i)
          E hEL ε (fun j => V.observable (a j)) (QuotientGroup.mk (k * x)) =
        M.tripleObservable i hi.le _ (omittedCoordinateWeight_le_one i)
          E hEL ε (fun j => V.observable (a j)) (QuotientGroup.mk x) := by
    intro k hk x
    have hkE : k ∈ E.filtration.realification.subgroup (s + 1) :=
      (E.filtration.mem_realQuotientStepHom_ker (E.filtration.layerIdeal (s + 1)) (t := s) le_rfl k).mp hk
    have hkF : k ∈ (M.filtration.additiveTripleFiltration i hi.le
        (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)).realification.subgroup (s + 1) := by
      rw [← hEF]
      exact hkE
    exact M.unitVertical_triple_top_invariant i hi hs E hEL V ε a k hkF (QuotientGroup.mk x)
  obtain ⟨v, hv, hvlip, hvnorm⟩ := exists_lipschitz_realification_reconstruction
    (hL := E.filtration.lowerCentralSeries_eq_bot) (hM := Q.filtration.lowerCentralSeries_eq_bot)
    E.basis Q.basis (lieQuotientMap (E.filtration.layerIdeal (s + 1))) (lieQuotientMap_surjective (E.filtration.layerIdeal (s + 1))) E.lattice Q.lattice hcover
    E.grid Q.grid H E.grid_pos Q.grid_pos hH E.outer_grid Q.outer_grid hentries hstructure
    (M.tripleObservable i hi.le _ (omittedCoordinateWeight_le_one i)
      E hEL ε (fun j => V.observable (a j))) hker A 1 hLip
    (M.tripleObservable_norm_le i hi.le _ (omittedCoordinateWeight_le_one i)
      E hEL ε (fun j => V.observable (a j)) (fun j x => V.norm (a j) x))
  let vQ : Q.Space → ℂ := v
  refine ⟨vQ, hv, ?_, ?_⟩
  · exact hvlip.weaken (by simp only [Fintype.card_fin, le_refl])
  · intro x
    exact hvnorm x

theorem exists_unitVertical_triple_quotient_niltest {τ : Type*} {w : τ → ℕ}
    (hQF : Q.filtration = E.filtration.quotientTop)
    {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ j k, RationalHeightLE (Q.basis.repr (lieQuotientMap (E.filtration.layerIdeal (s + 1)) (E.basis k)) j) H)
    (hstructure : ∀ a b c, RationalHeightLE (lieStructureConstants Q.basis a b c) H)
    {p : ℝ} (V : D.UnitVerticalObservable (M.realSubgroup bound) I p)
    (ε : D.RealGroup) (a : Fin 3 → I) (A : ℝ≥0)
    (hLip : letI := E.metricSpace
      LipschitzWith A (M.tripleObservable i hi.le _ (omittedCoordinateWeight_le_one i)
        E hEL ε (fun j => V.observable (a j))))
    (g : E.filtration.realification.PolynomialOrbit w) :
    ∃ T : Q.Niltest w, T.normBound = 1 ∧
      T.lipBound = rationalReconstructionLipschitzBound s r n H A 1 ∧
      T.orbit = E.topQuotientOrbit Q hQF g ∧
      ∀ x : τ → ℤ, T.eval x =
        M.tripleObservable i hi.le _ (omittedCoordinateWeight_le_one i)
          E hEL ε (fun j => V.observable (a j))
          (QuotientGroup.mk (E.filtration.realification.polynomialOrbitEval w x g)) := by
  obtain ⟨v, hv, hvlip, hvnorm⟩ := M.exists_lipschitz_unitVertical_triple_descent
    i hi hs E hEF hEL Q hQL hH hentries hstructure V ε a A hLip
  let T : Q.Niltest w :=
    { orbit := E.topQuotientOrbit Q hQF g
      observable := v
      normBound := 1
      lipBound := rationalReconstructionLipschitzBound s r n H A 1
      norm_le := hvnorm
      lipschitz := hvlip }
  refine ⟨T, rfl, rfl, rfl, fun x => ?_⟩
  change v (QuotientGroup.mk (Q.filtration.realification.polynomialOrbitEval w x
    (E.topQuotientOrbit Q hQF g))) = _
  rw [E.topQuotientOrbit_eval Q hQF]
  exact hv _

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open CircleFourier
open scoped TensorProduct BigOperators

variable {σ L I : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] [Fintype I]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (M : D.MultidegreeStructure bound)

theorem unitVertical_dilation_top_invariant (q : ℤ) (hs : ∑ j, bound j = s)
    (E : RationalFilteredNilmanifold (M.filtration.ordinary.dilationPairSubalgebra (q : ℚ)) s r)
    (hEL : E.lattice = M.dilationPairLattice (q : ℚ))
    {p : ℝ} (V : D.UnitVerticalObservable (M.realSubgroup bound) I p)
    (ε : D.RealGroup) (a₀ : I) (a : Fin (q ^ s).natAbs → I) (k : E.RealGroup)
    (hk : k ∈ (M.filtration.ordinary.dilationPairFiltration (q : ℚ)).realification.subgroup s)
    (x : E.Space) :
    M.dilationObservable (q : ℚ) E hEL (q ^ s) ε (V.observable a₀)
        (fun j => V.observable (a j)) (k • x) =
      M.dilationObservable (q : ℚ) E hEL (q ^ s) ε (V.observable a₀)
        (fun j => V.observable (a j)) x := by
  apply M.dilationObservable_top_invariant (q : ℚ) E hEL (q ^ s) ε
    (V.observable a₀) (fun j => V.observable (a j))
    (fun z => (realifyFunctional V.frequency z.coord : CircleFourier.Circle)) ?_ ?_ k hk ?_ x
  · exact fun z hz y => M.unitVertical_top_action hs V a₀ z hz y
  · exact fun j z hz y => M.unitVertical_top_action hs V (a j) z hz y
  · exact M.filtration.ordinary.realDilationPair_frequency_phase q V.frequency ⟨k.coord⟩ hk

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

include hs hEF hQF hQL

omit [DecidableEq σ] in
theorem exists_unitVertical_dilation_quotient_niltest {τ : Type*} {w : τ → ℕ}
    {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ j k, RationalHeightLE
      (Q.basis.repr (lieQuotientMap (E.filtration.layerIdeal (s + 1)) (E.basis k)) j) H)
    (hstructure : ∀ a b c, RationalHeightLE (lieStructureConstants Q.basis a b c) H)
    {p : ℝ} (V : D.UnitVerticalObservable (M.realSubgroup bound) I p)
    (ε : D.RealGroup) (a₀ : I) (a : Fin (q ^ (s + 1)).natAbs → I) (A : ℝ≥0)
    (hLip : letI := E.metricSpace
      LipschitzWith A (M.dilationObservable (q : ℚ) E hEL (q ^ (s + 1)) ε
        (V.observable a₀) (fun j => V.observable (a j))))
    (g : E.filtration.realification.PolynomialOrbit w) :
    ∃ T : Q.Niltest w, T.normBound = 1 ∧
      T.lipBound = rationalReconstructionLipschitzBound s r n H A 1 ∧
      T.orbit = E.topQuotientOrbit Q hQF g ∧
      ∀ x : τ → ℤ, T.eval x =
        M.dilationObservable (q : ℚ) E hEL (q ^ (s + 1)) ε
          (V.observable a₀) (fun j => V.observable (a j))
          (QuotientGroup.mk (E.filtration.realification.polynomialOrbitEval w x g)) := by
  let U : E.Niltest w :=
    { orbit := g
      observable := M.dilationObservable (q : ℚ) E hEL (q ^ (s + 1)) ε
        (V.observable a₀) (fun j => V.observable (a j))
      normBound := 1
      lipBound := A
      norm_le := M.dilationObservable_norm_le (q : ℚ) E hEL (q ^ (s + 1)) ε
        (V.observable a₀) (fun j => V.observable (a j)) (V.norm a₀) (fun j => V.norm (a j))
      lipschitz := hLip }
  have hinv : ∀ k ∈ E.filtration.realification.subgroup (s + 1), ∀ x,
      U.observable (k • x) = U.observable x := by
    intro k hk x
    have hk' : k ∈ (M.filtration.ordinary.dilationPairFiltration (q : ℚ)).realification.subgroup
        (s + 1) := by rw [← hEF]; exact hk
    exact M.unitVertical_dilation_top_invariant q hs E hEL V ε a₀ a k hk' x
  obtain ⟨T, hTo, hTn, hTl, hTe⟩ := E.exists_topInvariant_niltest Q hQF hQL U hinv H hH hentries hstructure
  exact ⟨T, hTn, hTl, hTo, hTe⟩

theorem exists_dilation_niltest_of_data {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ j k, RationalHeightLE
      (Q.basis.repr (lieQuotientMap (E.filtration.layerIdeal (s + 1)) (E.basis k)) j) H)
    (hstructure : ∀ a b c, RationalHeightLE (lieStructureConstants Q.basis a b c) H)
    {p : ℝ} (V : D.UnitVerticalObservable (M.realSubgroup bound) I p)
    (g : M.filtration.realification.PolynomialOrbit) (ε γ : D.RealGroup)
    (hγ : γ ∈ D.realLattice) (hfactor : M.filtration.realification.polynomialOrbitEval 0 g = ε * γ)
    (a₀ : I) (a : Fin (q ^ (s + 1)).natAbs → I) (A : ℝ≥0)
    (hLip : letI := E.metricSpace
      LipschitzWith A (M.dilationObservable (q : ℚ) E hEL (q ^ (s + 1)) ε
        (V.observable a₀) (fun j => V.observable (a j)))) :
    ∃ T : Q.Niltest (fun _ : σ => 1), T.normBound = 1 ∧
      T.lipBound = rationalReconstructionLipschitzBound s r n H A 1 ∧
      Q.filtration.realification.polynomialOrbitEval _ 0 T.orbit = 1 ∧
      ∀ x, T.eval x =
        V.observable a₀ (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval
          (fun i => q * x i) g)) *
        star (signedTensorProduct (q ^ (s + 1)) (fun j => V.observable (a j)
          (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g)))) := by
  obtain ⟨h, hh0, hh⟩ := M.exists_native_dilation_orbit q E hEF g ε γ hγ hfactor
  obtain ⟨T, hTn, hTl, hTo, hTe⟩ := M.exists_unitVertical_dilation_quotient_niltest
    q hs E hEF hEL Q hQF hQL hH hentries hstructure V ε a₀ a A hLip h
  refine ⟨T, hTn, hTl, ?_, ?_⟩
  · rw [hTo, E.topQuotientOrbit_eval Q hQF, hh0, map_one]
  · intro x
    rw [hTe, M.dilationObservable_mk, (hh x).1, (hh x).2]

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI

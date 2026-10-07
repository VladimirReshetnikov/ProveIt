import OAI.Combinatorics.Progressions.Linear.ExternalFamilyCircleProjection
import OAI.Combinatorics.Progressions.Linear.RationalKernelInvariance

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open CircleFourier
open scoped TensorProduct BigOperators NNReal

variable {σ α L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

noncomputable def averageCircles (T : D.Niltest w)
    (A : let := D.metricSpace; α → IsometricCircleAction D.Space) (is : List α) : D.Niltest w := by
  let := D.metricSpace
  exact {
    orbit := T.orbit
    observable := iteratedCircleAverage A is T.observable
    normBound := T.normBound
    lipBound := T.lipBound
    norm_le := iteratedCircleAverage_norm_le A is T.norm_le
    lipschitz := iteratedCircleAverage_lipschitz A is T.lipschitz }

theorem averageCircles_orbit (T : D.Niltest w)
    (A : let := D.metricSpace; α → IsometricCircleAction D.Space) (is : List α) :
    (T.averageCircles A is).orbit = T.orbit := rfl

theorem averageCircles_complexity (T : D.Niltest w)
    (A : let := D.metricSpace; α → IsometricCircleAction D.Space) (is : List α)
    {p : ℝ} (hT : T.ComplexityLE p) : (T.averageCircles A is).ComplexityLE p := hT

theorem averageCircles_unit_interval (T : D.Niltest w)
    (A : let := D.metricSpace; α → IsometricCircleAction D.Space) (is : List α)
    (hT : T.UnitIntervalValued) : (T.averageCircles A is).UnitIntervalValued := by
  let := D.metricSpace
  exact iteratedCircleAverage_unit_interval A is T.lipschitz hT

theorem averageCircles_invariant (T : D.Niltest w)
    (A : let := D.metricSpace; α → IsometricCircleAction D.Space) (is : List α)
    (hcomm : let := D.metricSpace; ∀ i ∈ is, ∀ j ∈ is, (A i).Commutes (A j))
    (j : α) (hj : j ∈ is) (t : CircleFourier.Circle) (x : D.Space) :
    let := D.metricSpace
    (T.averageCircles A is).observable ((A j).act t x) = (T.averageCircles A is).observable x := by
  let := D.metricSpace
  exact iteratedCircleAverage_invariant A is hcomm T.observable j hj t x

theorem averageCircles_evalCyclic (T : D.Niltest w)
    (A : let := D.metricSpace; α → IsometricCircleAction D.Space) (is : List α)
    (N : ℕ) [NeZero N] (x : σ → ZMod N) :
    (T.averageCircles A is).evalCyclic N x =
      (let := D.metricSpace; iteratedCircleAverage A is T.observable (D.cyclicOrbitPoint T.orbit N x)) := rfl

theorem averageCircles_tested_error (T : D.Niltest (fun _ : Unit => 1))
    (A : let := D.metricSpace; α → IsometricCircleAction D.Space) (is : List α)
    {J : Type*} [Fintype J] (U : J → D.Niltest (fun _ : Unit => 1)) (n : J → α → ℤ)
    (horbit : ∀ j, (U j).orbit = T.orbit) {N : ℕ} [NeZero N] (weight : ZMod N → ℂ)
    {B rho tau : ℝ} (hB : 0 ≤ B) (htau : 0 ≤ tau) (hweight : ∀ x, ‖weight x‖ ≤ B)
    (happrox : ∀ x, ‖T.observable x - ∑ j, (U j).observable x‖ ≤ rho)
    (heigen : let := D.metricSpace; ∀ j i, i ∈ is → ∀ t x,
      (U j).observable ((A i).act t x) = character (n j i • t) * (U j).observable x)
    (hdiscard : ∀ j, ¬ (∀ i ∈ is, n j i = 0) →
      ‖𝔼 x, weight x * (U j).evalCyclic N (fun _ => x)‖ ≤ tau) :
    ‖(𝔼 x, weight x * T.evalCyclic N (fun _ => x)) -
      (𝔼 x, weight x * (T.averageCircles A is).evalCyclic N (fun _ => x))‖ ≤
      2 * B * rho + Fintype.card J * tau := by
  let := D.metricSpace
  let path : ZMod N → D.Space := fun x => D.cyclicOrbitPoint T.orbit N (fun _ => x)
  have heval (j : J) (x : ZMod N) :
      (U j).observable (path x) = (U j).evalCyclic N (fun _ => x) := by
    change (U j).observable (D.cyclicOrbitPoint T.orbit N (fun _ => x)) =
      (U j).observable (D.cyclicOrbitPoint (U j).orbit N (fun _ => x))
    rw [horbit j]
  have hdiscard' (j : J) (hj : ¬ (∀ i ∈ is, n j i = 0)) :
      ‖𝔼 x, weight x * (U j).observable (path x)‖ ≤ tau := by
    simpa only [heval] using hdiscard j hj
  exact iteratedCircleAverage_tested_error A is T.observable (fun j => (U j).observable)
    n path weight T.lipBound (fun j => (U j).lipBound) T.lipschitz (fun j => (U j).lipschitz)
    hB htau hweight happrox heigen hdiscard'

theorem exists_positive_circle_projection (T : D.Niltest (fun _ : Unit => 1))
    (hT : T.UnitIntervalValued) {p : ℝ} (hTc : T.ComplexityLE p)
    (A : let := D.metricSpace; α → IsometricCircleAction D.Space) (is : List α)
    (hcomm : let := D.metricSpace; ∀ i ∈ is, ∀ j ∈ is, (A i).Commutes (A j))
    {J : Type*} [Fintype J] (U : J → D.Niltest (fun _ : Unit => 1)) (n : J → α → ℤ)
    (horbit : ∀ j, (U j).orbit = T.orbit) {N : ℕ} [NeZero N] (weight : ZMod N → ℂ)
    {B rho tau : ℝ} (hB : 0 ≤ B) (htau : 0 ≤ tau) (hweight : ∀ x, ‖weight x‖ ≤ B)
    (happrox : ∀ x, ‖T.observable x - ∑ j, (U j).observable x‖ ≤ rho)
    (heigen : let := D.metricSpace; ∀ j i, i ∈ is → ∀ t x,
      (U j).observable ((A i).act t x) = character (n j i • t) * (U j).observable x)
    (hsignificant : ∀ j, tau < ‖𝔼 x, weight x * (U j).evalCyclic N (fun _ => x)‖ →
      ∀ i ∈ is, n j i = 0) :
    let := D.metricSpace
    ∃ S : D.Niltest (fun _ : Unit => 1), S.UnitIntervalValued ∧ S.ComplexityLE p ∧
      S.orbit = T.orbit ∧
      (∀ i ∈ is, ∀ t x, S.observable ((A i).act t x) = S.observable x) ∧
      ‖(𝔼 x, weight x * T.evalCyclic N (fun _ => x)) -
        (𝔼 x, weight x * S.evalCyclic N (fun _ => x))‖ ≤
        2 * B * rho + Fintype.card J * tau := by
  let := D.metricSpace
  refine ⟨T.averageCircles A is, T.averageCircles_unit_interval A is hT,
    T.averageCircles_complexity A is hTc, T.averageCircles_orbit A is, ?_, ?_⟩
  · intro i hi t x
    exact T.averageCircles_invariant A is hcomm i hi t x
  · apply T.averageCircles_tested_error A is U n horbit weight hB htau hweight happrox heigen
    intro j hj
    exact le_of_not_gt (fun h => hj (hsignificant j h))

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open CircleFourier
open scoped TensorProduct BigOperators NNReal

variable {σ α L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem averageCircles_weighted_error (T : D.Niltest w)
    (A : let := D.metricSpace; α → IsometricCircleAction D.Space) (is : List α)
    {J G : Type*} [Fintype J] [Fintype G] (U : J → D.Niltest w) (n : J → α → ℤ)
    (horbit : ∀ j, (U j).orbit = T.orbit) (path : G → σ → ℤ) (weight : G → ℂ)
    {B rho tau : ℝ} (hmass : (∑ x, ‖weight x‖) ≤ B) (hrho : 0 ≤ rho) (htau : 0 ≤ tau)
    (happrox : ∀ x, ‖T.observable x - ∑ j, (U j).observable x‖ ≤ rho)
    (heigen : let := D.metricSpace; ∀ j i, i ∈ is → ∀ t x,
      (U j).observable ((A i).act t x) = character (n j i • t) * (U j).observable x)
    (hdiscard : ∀ j, ¬ (∀ i ∈ is, n j i = 0) →
      ‖∑ x, weight x * (U j).eval (path x)‖ ≤ tau) :
    ‖(∑ x, weight x * T.eval (path x)) -
      (∑ x, weight x * (T.averageCircles A is).eval (path x))‖ ≤
      2 * B * rho + Fintype.card J * tau := by
  let := D.metricSpace
  let orbitPath : G → D.Space := fun x =>
    QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w (path x) T.orbit)
  have heval (j : J) (x : G) :
      (U j).observable (orbitPath x) = (U j).eval (path x) := by
    change (U j).observable (QuotientGroup.mk
      (D.filtration.realification.polynomialOrbitEval w (path x) T.orbit)) =
      (U j).observable (QuotientGroup.mk
        (D.filtration.realification.polynomialOrbitEval w (path x) (U j).orbit))
    rw [horbit j]
  have hdiscard' (j : J) (hj : ¬ (∀ i ∈ is, n j i = 0)) :
      ‖∑ x, weight x * (U j).observable (orbitPath x)‖ ≤ tau := by
    simpa only [heval] using hdiscard j hj
  exact iteratedCircleAverage_weighted_error A is T.observable (fun j => (U j).observable)
    n orbitPath weight T.lipBound (fun j => (U j).lipBound) T.lipschitz
    (fun j => (U j).lipschitz) hmass hrho htau happrox heigen hdiscard'

theorem exists_positive_circle_projection_family (T : D.Niltest w)
    (hT : T.UnitIntervalValued) {p : ℝ} (hTc : T.ComplexityLE p)
    (A : let := D.metricSpace; α → IsometricCircleAction D.Space) (is : List α)
    (hcomm : let := D.metricSpace; ∀ i ∈ is, ∀ j ∈ is, (A i).Commutes (A j))
    {J β : Type*} {G : β → Type*} [Fintype J] [∀ a, Fintype (G a)]
    (U : J → D.Niltest w) (n : J → α → ℤ) (horbit : ∀ j, (U j).orbit = T.orbit)
    (path : ∀ a, G a → σ → ℤ) (weight : ∀ a, G a → ℂ) (B tau : β → ℝ)
    {rho : ℝ} (hmass : ∀ a, (∑ x, ‖weight a x‖) ≤ B a)
    (hrho : 0 ≤ rho) (htau : ∀ a, 0 ≤ tau a)
    (happrox : ∀ x, ‖T.observable x - ∑ j, (U j).observable x‖ ≤ rho)
    (heigen : let := D.metricSpace; ∀ j i, i ∈ is → ∀ t x,
      (U j).observable ((A i).act t x) = character (n j i • t) * (U j).observable x)
    (hsignificant : ∀ j, (∃ a, tau a < ‖∑ x, weight a x * (U j).eval (path a x)‖) →
      ∀ i ∈ is, n j i = 0) :
    let := D.metricSpace
    ∃ S : D.Niltest w, S.UnitIntervalValued ∧ S.ComplexityLE p ∧ S.orbit = T.orbit ∧
      (∀ i ∈ is, ∀ t x, S.observable ((A i).act t x) = S.observable x) ∧
      ∀ a, ‖(∑ x, weight a x * T.eval (path a x)) -
        (∑ x, weight a x * S.eval (path a x))‖ ≤
          2 * B a * rho + Fintype.card J * tau a := by
  let := D.metricSpace
  refine ⟨T.averageCircles A is, T.averageCircles_unit_interval A is hT,
    T.averageCircles_complexity A is hTc, T.averageCircles_orbit A is, ?_, ?_⟩
  · intro i hi t x
    exact T.averageCircles_invariant A is hcomm i hi t x
  · intro a
    apply T.averageCircles_weighted_error A is U n horbit (path a) (weight a)
      (hmass a) hrho (htau a) happrox heigen
    intro j hj
    exact le_of_not_gt (fun h => hj (hsignificant j ⟨a, h⟩))

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open Module CircleFourier
open scoped TensorProduct BigOperators

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem exists_positive_kernel_projection_family (T : D.Niltest w)
    (hT : T.UnitIntervalValued) {p : ℝ} (hTc : T.ComplexityLE p)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s)
    {J β : Type*} {G : β → Type*} [Fintype J] [∀ a, Fintype (G a)]
    (eta : J → L →ₗ[ℚ] ℚ) (U : J → D.Niltest w)
    (horbit : ∀ j, (U j).orbit = T.orbit)
    (hvertical : ∀ j (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
      (U j).observable (z • x) =
        character ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) * (U j).observable x)
    (path : ∀ a, G a → σ → ℤ) (weight : ∀ a, G a → ℂ) (B tau : β → ℝ)
    {rho : ℝ} (hmass : ∀ a, (∑ x, ‖weight a x‖) ≤ B a)
    (hrho : 0 ≤ rho) (htau : ∀ a, 0 ≤ tau a)
    (happrox : ∀ x, ‖T.observable x - ∑ j, (U j).observable x‖ ≤ rho)
    (hkill : ∀ j, (∃ a, tau a < ‖∑ x, weight a x * (U j).eval (path a x)‖) →
      ∀ v ∈ K, eta j v = 0) :
    ∃ S : D.Niltest w, S.UnitIntervalValued ∧ S.ComplexityLE p ∧ S.orbit = T.orbit ∧
      (∀ z : D.RealGroup, z.coord ∈ K.baseChange ℝ →
        ∀ x, S.observable (z • x) = S.observable x) ∧
      ∀ a, ‖(∑ x, weight a x * T.eval (path a x)) -
        (∑ x, weight a x * S.eval (path a x))‖ ≤
          2 * B a * rho + Fintype.card J * tau a := by
  classical
  let := D.metricSpace
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  let b := Module.finBasis ℚ K
  let v : Fin (finrank ℚ K) → L := fun i => b i
  have hv (i : Fin (finrank ℚ K)) : v i ∈ D.filtration.layer s := hK (b i).property
  let A : Fin (finrank ℚ K) → IsometricCircleAction D.Space :=
    fun i => D.centralRationalCircle (v i) (hv i)
  have hfreq (j : J) (i : Fin (finrank ℚ K)) : ∃ n : ℤ,
      (∀ t x, (U j).observable ((A i).act t x) = character (n • t) * (U j).observable x) ∧
      (eta j (v i) = 0 → n = 0) :=
    D.exists_centralRationalCircle_frequency (v i) (hv i) (eta j) (U j).observable (hvertical j)
  choose n heigen hzero using hfreq
  let is := List.finRange (finrank ℚ K)
  have hcomm : ∀ i ∈ is, ∀ j ∈ is, (A i).Commutes (A j) :=
    fun i _ j _ => D.centralRationalCircle_commutes (v i) (v j) (hv i) (hv j)
  have hsignificant (j : J)
      (hj : ∃ a, tau a < ‖∑ x, weight a x * (U j).eval (path a x)‖) :
      ∀ i ∈ is, n j i = 0 := by
    intro i _
    exact hzero j i (hkill j hj (v i) (b i).property)
  obtain ⟨S, hS, hSc, hSo, hSinv, herror⟩ := T.exists_positive_circle_projection_family hT hTc
    A is hcomm U n horbit path weight B tau hmass hrho htau happrox
    (fun j i _ => heigen j i) hsignificant
  refine ⟨S, hS, hSc, hSo, ?_, herror⟩
  intro z hz x
  exact D.invariant_of_kernel_circles K hK b S.observable
    (fun i t y => hSinv i (by simp [is]) t y) z hz x

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open CircleFourier
open scoped TensorProduct BigOperators

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem exists_probability_kernel_projection_family (T : D.Niltest w)
    (hT : T.UnitIntervalValued) {p : ℝ} (hTc : T.ComplexityLE p)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s)
    {J β : Type*} {G : β → Type*} [Fintype J] [∀ a, Fintype (G a)]
    (eta : J → L →ₗ[ℚ] ℚ) (U : J → D.Niltest w)
    (horbit : ∀ j, (U j).orbit = T.orbit)
    (hvertical : ∀ j (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
      (U j).observable (z • x) =
        character ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) * (U j).observable x)
    (law : ∀ a, FiniteProbabilityWeights (G a)) (path : ∀ a, G a → σ → ℤ)
    (tau : β → ℝ) {rho : ℝ} (hrho : 0 ≤ rho) (htau : ∀ a, 0 ≤ tau a)
    (happrox : ∀ x, ‖T.observable x - ∑ j, (U j).observable x‖ ≤ rho)
    (hkill : ∀ j, (∃ a, tau a < ‖(law a).complexMean (fun x => (U j).eval (path a x))‖) →
      ∀ v ∈ K, eta j v = 0) :
    ∃ S : D.Niltest w, S.UnitIntervalValued ∧ S.ComplexityLE p ∧ S.orbit = T.orbit ∧
      (∀ z : D.RealGroup, z.coord ∈ K.baseChange ℝ →
        ∀ x, S.observable (z • x) = S.observable x) ∧
      ∀ a, ‖(law a).complexMean (fun x => T.eval (path a x)) -
        (law a).complexMean (fun x => S.eval (path a x))‖ ≤
          2 * rho + Fintype.card J * tau a := by
  have hmass (a : β) : (∑ x, ‖((law a).weight x : ℂ)‖) ≤ 1 := by
    have hnorm (x : G a) : ‖((law a).weight x : ℂ)‖ = (law a).weight x := by
      rw [Complex.norm_real, Real.norm_of_nonneg ((law a).nonneg x)]
    simp_rw [hnorm]
    exact (law a).total.le
  simpa only [FiniteProbabilityWeights.complexMean, mul_one] using
    T.exists_positive_kernel_projection_family hT hTc K hK eta U horbit hvertical path
      (fun a x => ((law a).weight x : ℂ)) (fun _ => 1) tau hmass hrho htau happrox hkill

theorem exists_finset_kernel_projection_family (T : D.Niltest w)
    (hT : T.UnitIntervalValued) {p : ℝ} (hTc : T.ComplexityLE p)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s)
    {J β : Type*} [Fintype J]
    (eta : J → L →ₗ[ℚ] ℚ) (U : J → D.Niltest w)
    (horbit : ∀ j, (U j).orbit = T.orbit)
    (hvertical : ∀ j (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
      (U j).observable (z • x) =
        character ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) * (U j).observable x)
    (boxes : β → Finset (σ → ℤ)) (hboxes : ∀ a, (boxes a).Nonempty)
    (tau : β → ℝ) {rho : ℝ} (hrho : 0 ≤ rho) (htau : ∀ a, 0 ≤ tau a)
    (happrox : ∀ x, ‖T.observable x - ∑ j, (U j).observable x‖ ≤ rho)
    (hkill : ∀ j, (∃ a, tau a < ‖𝔼 x ∈ boxes a, (U j).eval x‖) →
      ∀ v ∈ K, eta j v = 0) :
    ∃ S : D.Niltest w, S.UnitIntervalValued ∧ S.ComplexityLE p ∧ S.orbit = T.orbit ∧
      (∀ z : D.RealGroup, z.coord ∈ K.baseChange ℝ →
        ∀ x, S.observable (z • x) = S.observable x) ∧
      ∀ a, ‖(𝔼 x ∈ boxes a, T.eval x) - (𝔼 x ∈ boxes a, S.eval x)‖ ≤
        2 * rho + Fintype.card J * tau a := by
  let law (a : β) := FiniteProbabilityWeights.uniformFinset (boxes a) (hboxes a)
  have hkill' : ∀ j, (∃ a, tau a < ‖(law a).complexMean (fun x => (U j).eval x.val)‖) →
      ∀ v ∈ K, eta j v = 0 := by
    simpa only [law, FiniteProbabilityWeights.uniformFinset_complexMean] using hkill
  simpa only [law, FiniteProbabilityWeights.uniformFinset_complexMean] using
    T.exists_probability_kernel_projection_family hT hTc K hK eta U horbit hvertical
      law (fun _ x => x.val) tau hrho htau happrox hkill'

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI

import OAI.Combinatorics.Progressions.Estimates.CommonPivotQuotientTop
import OAI.Combinatorics.Progressions.Nilpotent.NiltestVerticalBounds

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open CircleFourier
open scoped TensorProduct BigOperators

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d}

theorem exists_positive_fourier_projection (T : D.Niltest (fun _ : Unit => 1))
    {p rho tau B : ℝ} (hp : 0 ≤ p) (hT : T.UnitIntervalValued) (hTc : T.ComplexityLE p)
    (hrho : 0 < rho) (hrhop : rho⁻¹ ≤ Real.exp p) (htau : 0 ≤ tau) (hB : 0 ≤ B)
    {N : ℕ} [NeZero N] (weight : ZMod N → ℂ) (hweight : ∀ x, ‖weight x‖ ≤ B) :
    ∃ (J : Type) (inst : Fintype J), letI := inst
    ∃ (eta : J → L →ₗ[ℚ] ℚ) (U : J → D.Niltest (fun _ : Unit => 1))
      (S : D.Niltest (fun _ : Unit => 1)),
      (Fintype.card J : ℝ) ≤ Real.exp (verticalDecompositionBudget p) ∧
      (∀ j i, rationalLogHeight (eta j (D.basis i)) ≤ verticalDecompositionBudget p) ∧
      (∀ j, (U j).ComplexityLE p ∧ (U j).orbit = T.orbit) ∧
      (∀ j (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
        (U j).observable (z • x) =
          character ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) * (U j).observable x) ∧
      (∀ x, ‖(∑ j, (U j).observable x) - T.observable x‖ ≤ rho) ∧
      S.UnitIntervalValued ∧ S.ComplexityLE p ∧ S.orbit = T.orbit ∧
      (∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup s →
        (∀ j, tau < ‖𝔼 n, weight n * (U j).evalCyclic N (fun _ => n)‖ →
          realifyFunctional (eta j) z.coord = 0) →
        ∀ x, S.observable (z • x) = S.observable x) ∧
      ‖(𝔼 n, weight n * T.evalCyclic N (fun _ => n)) -
        (𝔼 n, weight n * S.evalCyclic N (fun _ => n))‖ ≤
          2 * B * rho + Real.exp (verticalDecompositionBudget p) * tau := by
  obtain ⟨J, inst, eta, U, hcard, hheight, hU, hvertical, _, _, happrox, _⟩ :=
    T.exists_controlled_vertical_decomposition hp hTc rho hrho hrhop
  let := inst
  obtain ⟨S, hS, hSc, hSo, hinv, herr⟩ := T.exists_positive_frequency_projection_of_decomposition
    hT hTc eta U (fun j => (hU j).2) hvertical weight hB htau hweight
    (fun x => by simpa only [norm_sub_rev] using happrox x)
  refine ⟨J, inst, eta, U, S, hcard, hheight, hU, hvertical, happrox, hS, hSc, hSo, hinv, ?_⟩
  exact herr.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hcard htau))

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3

open Module
open scoped Classical

variable {V J : Type*} [AddCommGroup V] [Module ℚ V]

def frequencyCodeKernel (P : Submodule ℚ V) (eta : J → V →ₗ[ℚ] ℚ)
    {D : ℕ} (code : Fin D → Option J) : Submodule ℚ V :=
  finiteFrequencyKernel P (fun i => (code i).elim 0 eta) (List.finRange D)

theorem mem_frequencyCodeKernel (P : Submodule ℚ V) (eta : J → V →ₗ[ℚ] ℚ)
    {D : ℕ} (code : Fin D → Option J) (v : V) :
    v ∈ frequencyCodeKernel P eta code ↔ v ∈ P ∧
      ∀ i j, code i = some j → eta j v = 0 := by
  simp only [frequencyCodeKernel, mem_finiteFrequencyKernel, List.mem_finRange, forall_true_left]
  refine and_congr_right (fun _ => ?_)
  constructor
  · intro h i j hij
    simpa only [hij, Option.elim_some] using h i
  · intro h i
    cases hi : code i with
    | none => simp
    | some j => simpa only [Option.elim_some] using h i j hi

theorem exists_frequency_basis_code [FiniteDimensional ℚ V]
    (P : Submodule ℚ V) (eta : J → V →ₗ[ℚ] ℚ) (js : List J) :
    ∃ code : Fin (finrank ℚ P) → Option J,
      (∀ i j, code i = some j → j ∈ js) ∧
      finiteFrequencyKernel P eta js = frequencyCodeKernel P eta code := by
  obtain ⟨m, hm, index, hindex, hlin, hspan⟩ := exists_restricted_frequency_basis P eta js
  let code : Fin (finrank ℚ P) → Option J := fun i =>
    if hi : i.val < m then some (index ⟨i.val, hi⟩) else none
  have hkernel : finiteFrequencyKernel P eta js =
      finiteFrequencyKernel P (fun i => eta (index i)) (List.finRange m) := by
    apply finiteFrequencyKernel_eq_of_span_eq
    rw [restrictedFrequencySpan_finRange]
    exact hspan.symm
  refine ⟨code, ?_, ?_⟩
  · intro i j hij
    dsimp only [code] at hij
    split_ifs at hij with hi
    · cases hij
      exact hindex _
  · rw [hkernel]
    ext v
    rw [mem_finiteFrequencyKernel, mem_frequencyCodeKernel]
    simp only [List.mem_finRange, forall_true_left]
    refine and_congr_right (fun _ => ?_)
    constructor
    · intro h i j hij
      dsimp only [code] at hij
      split_ifs at hij with hi
      · cases hij
        exact h _
    · intro h i
      let k : Fin (finrank ℚ P) := ⟨i.val, lt_of_lt_of_le i.isLt hm⟩
      apply h k (index i)
      simp only [code, k, i.isLt, dite_true]

theorem exists_common_frequency_kernel [FiniteDimensional ℚ V]
    {Ω : Type*} [Fintype Ω] [Fintype J]
    (law : FiniteProbabilityWeights Ω) (productive : Finset Ω)
    (P : Submodule ℚ V) (eta : J → V →ₗ[ℚ] ℚ) (js : Ω → List J) :
    ∃ (code : Fin (finrank ℚ P) → Option J) (retained : Finset Ω),
      retained ⊆ productive ∧
      law.mass productive / (Fintype.card J + 1) ^ finrank ℚ P ≤ law.mass retained ∧
      ∀ a ∈ retained, (∀ i j, code i = some j → j ∈ js a) ∧
        finiteFrequencyKernel P eta (js a) = frequencyCodeKernel P eta code := by
  choose code hmem hkernel using fun a => exists_frequency_basis_code P eta (js a)
  obtain ⟨c, hc⟩ := law.exists_code_fiber_mass productive code
  refine ⟨c, productive.filter (fun a => code a = c), Finset.filter_subset _ _, ?_, ?_⟩
  · have hcard : (Fintype.card (Fin (finrank ℚ P) → Option J) : ℝ) =
        (Fintype.card J + 1 : ℝ) ^ finrank ℚ P := by simp
    rw [hcard] at hc
    convert hc using 1; try rfl
    congr 1
    ext a
    simp only [Finset.mem_filter]
  · intro a ha
    have he := (Finset.mem_filter.mp ha).2
    rw [← he]
    exact ⟨hmem a, hkernel a⟩

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem exists_restricted_frequency_basis_real_kernel
    {V J : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (P : Submodule ℚ V) (eta : J → V →ₗ[ℚ] ℚ) (js : List J) :
    ∃ m : ℕ, m ≤ finrank ℚ P ∧ ∃ indices : Fin m → J,
      (∀ i, indices i ∈ js) ∧
      LinearIndependent ℚ (fun i => (eta (indices i)).comp P.subtype) ∧
      ∀ x ∈ P.baseChange ℝ,
        (∀ j ∈ js, realifyFunctional (eta j) x = 0) ↔
          ∀ i, realifyFunctional (eta (indices i)) x = 0 := by
  obtain ⟨m, hm, indices, hmem, hlin, hspan⟩ := exists_restricted_frequency_basis P eta js
  have hK : finiteFrequencyKernel P eta js =
      finiteFrequencyKernel P (fun i => eta (indices i)) (List.finRange m) := by
    apply finiteFrequencyKernel_eq_of_span_eq
    rw [restrictedFrequencySpan_finRange]
    exact hspan.symm
  refine ⟨m, hm, indices, hmem, hlin, ?_⟩
  intro x hx
  constructor
  · intro h
    have hk := (mem_real_finiteFrequencyKernel P eta js x).mpr ⟨hx, h⟩
    rw [hK] at hk
    have hsel := (mem_real_finiteFrequencyKernel P (fun i => eta (indices i)) (List.finRange m) x).mp hk
    exact fun i => hsel.2 i (by simp)
  · intro h
    have hk := (mem_real_finiteFrequencyKernel P (fun i => eta (indices i)) (List.finRange m) x).mpr
      ⟨hx, fun i _ => h i⟩
    rw [← hK] at hk
    exact ((mem_real_finiteFrequencyKernel P eta js x).mp hk).2

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open Module CircleFourier
open scoped TensorProduct BigOperators

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d}

theorem exists_bounded_positive_fourier_basis (T : D.Niltest (fun _ : Unit => 1))
    {p rho tau B : ℝ} (hp : 0 ≤ p) (hT : T.UnitIntervalValued) (hTc : T.ComplexityLE p)
    (hcap : T.normBound ≤ 1) (hrho : 0 < rho) (hrhop : rho⁻¹ ≤ Real.exp p)
    (htau : 0 ≤ tau) (hB : 0 ≤ B) {N : ℕ} [NeZero N]
    (weight : ZMod N → ℂ) (hweight : ∀ x, ‖weight x‖ ≤ B) :
    ∃ (J : Type) (inst : Fintype J), letI := inst
    ∃ (eta : J → L →ₗ[ℚ] ℚ) (U : J → D.Niltest (fun _ : Unit => 1))
      (S : D.Niltest (fun _ : Unit => 1)) (m : ℕ) (indices : Fin m → J),
      (Fintype.card J : ℝ) ≤ Real.exp (verticalDecompositionBudget p) ∧
      (∀ j i, rationalLogHeight (eta j (D.basis i)) ≤ verticalDecompositionBudget p) ∧
      (∀ j, (U j).ComplexityLE p ∧ (U j).orbit = T.orbit ∧ (U j).normBound ≤ 1) ∧
      (∀ j z, z ∈ D.filtration.realification.subgroup s → ∀ x,
        (U j).observable (z • x) =
          character ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) * (U j).observable x) ∧
      m ≤ d ∧
      (∀ i, tau < ‖𝔼 n, weight n * (U (indices i)).evalCyclic N (fun _ => n)‖) ∧
      LinearIndependent ℚ (fun i => (eta (indices i)).comp (D.filtration.layer s).subtype) ∧
      S.UnitIntervalValued ∧ S.ComplexityLE p ∧ S.orbit = T.orbit ∧
      (∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup s →
        (∀ i, realifyFunctional (eta (indices i)) z.coord = 0) →
        ∀ x, S.observable (z • x) = S.observable x) ∧
      ‖(𝔼 n, weight n * T.evalCyclic N (fun _ => n)) -
        (𝔼 n, weight n * S.evalCyclic N (fun _ => n))‖ ≤
          2 * B * rho + Real.exp (verticalDecompositionBudget p) * tau := by
  classical
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  obtain ⟨J, inst, eta, U, hcard, hheight, hU, hvertical, _, happrox, _⟩ :=
    T.exists_vertical_decomposition_preserving_bounds hp hTc hrho hrhop
  let := inst
  obtain ⟨S, hS, hSc, hSo, hinv, herr⟩ := T.exists_positive_frequency_projection_of_decomposition
    hT hTc eta U (fun j => (hU j).2.1) hvertical weight hB htau hweight
      (fun x => by simpa only [norm_sub_rev] using happrox x)
  let active : Finset J := Finset.univ.filter
    (fun j => tau < ‖𝔼 n, weight n * (U j).evalCyclic N (fun _ => n)‖)
  let js := active.toList
  obtain ⟨m, hm, indices, hindices, hlin, hkernel⟩ :=
    exists_restricted_frequency_basis_real_kernel (D.filtration.layer s) eta js
  have hmd : m ≤ d := hm.trans (by
    simpa only [finrank_eq_card_basis D.basis, Fintype.card_fin] using (D.filtration.layer s).finrank_le)
  refine ⟨J, inst, eta, U, S, m, indices, hcard, hheight, ?_, hvertical, hmd, ?_, hlin,
    hS, hSc, hSo, ?_, ?_⟩
  · intro j
    refine ⟨(hU j).1, (hU j).2.1, ?_⟩
    rw [(hU j).2.2.1]
    exact hcap
  · intro i
    simpa only [js, active, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]
      using hindices i
  · intro z hz hbasis x
    apply hinv z hz _ x
    have hfull := (hkernel z.coord hz).mpr hbasis
    intro j hj
    exact hfull j (by simpa only [js, active, Finset.mem_toList, Finset.mem_filter,
      Finset.mem_univ, true_and] using hj)
  · exact herr.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hcard htau))

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3

open Module
open scoped Classical TensorProduct

variable {V J : Type*} [AddCommGroup V] [Module ℚ V]

def frequencyCodeIndices {D : ℕ} (code : Fin D → Option J) : List J :=
  (List.ofFn code).filterMap id

theorem mem_frequencyCodeIndices {D : ℕ} (code : Fin D → Option J) (j : J) :
    j ∈ frequencyCodeIndices code ↔ ∃ i, code i = some j := by
  simp only [frequencyCodeIndices, List.mem_filterMap, List.mem_ofFn]
  constructor
  · rintro ⟨x, ⟨i, rfl⟩, hx⟩
    exact ⟨i, hx⟩
  · rintro ⟨i, hi⟩
    exact ⟨code i, ⟨i, rfl⟩, hi⟩

theorem finiteFrequencyKernel_codeIndices (P : Submodule ℚ V)
    (eta : J → V →ₗ[ℚ] ℚ) {D : ℕ} (code : Fin D → Option J) :
    finiteFrequencyKernel P eta (frequencyCodeIndices code) = frequencyCodeKernel P eta code := by
  ext x
  rw [mem_finiteFrequencyKernel, mem_frequencyCodeKernel]
  refine and_congr_right (fun _ => ?_)
  constructor
  · intro h i j hij
    exact h j ((mem_frequencyCodeIndices code j).mpr ⟨i, hij⟩)
  · intro h j hj
    obtain ⟨i, hi⟩ := (mem_frequencyCodeIndices code j).mp hj
    exact h i j hi

theorem restrictedFrequencySpan_eq_of_kernel_eq [FiniteDimensional ℚ V]
    {I : Type*} (P : Submodule ℚ V) (eta : J → V →ₗ[ℚ] ℚ) (js : List J)
    (xi : I → V →ₗ[ℚ] ℚ) (is : List I)
    (hker : finiteFrequencyKernel P eta js = finiteFrequencyKernel P xi is) :
    restrictedFrequencySpan P eta js = restrictedFrequencySpan P xi is := by
  have hco : (restrictedFrequencySpan P eta js).dualCoannihilator =
      (restrictedFrequencySpan P xi is).dualCoannihilator := by
    ext x
    rw [mem_restrictedFrequencySpan_coannihilator,
      mem_restrictedFrequencySpan_coannihilator, hker]
  calc
    _ = (restrictedFrequencySpan P eta js).dualCoannihilator.dualAnnihilator :=
      Subspace.dualCoannihilator_dualAnnihilator_eq.symm
    _ = (restrictedFrequencySpan P xi is).dualCoannihilator.dualAnnihilator := by rw [hco]
    _ = _ := Subspace.dualCoannihilator_dualAnnihilator_eq

theorem exists_common_significant_frequency_basis [FiniteDimensional ℚ V]
    {H : Type*} [Fintype H] [Fintype J]
    (law : FiniteProbabilityWeights H) (productive : Finset H)
    (hproductive : 0 < law.mass productive)
    (P : Submodule ℚ V) (eta : J → V →ₗ[ℚ] ℚ) (significant : H → Finset J)
    (D : ℕ) (hD : finrank ℚ P ≤ D) :
    ∃ (m : ℕ) (indices : Fin m → J) (retained : Finset H),
      m ≤ finrank ℚ P ∧ m ≤ D ∧
      LinearIndependent ℚ (fun i => (eta (indices i)).comp P.subtype) ∧
      retained ⊆ productive ∧
      law.mass productive / (Fintype.card J + 1 : ℝ) ^ D ≤ law.mass retained ∧
      0 < law.mass retained ∧
      ∀ h ∈ retained,
        (∀ i, indices i ∈ significant h) ∧
        restrictedFrequencySpan P eta (significant h).toList =
          Submodule.span ℚ (Set.range (fun i => (eta (indices i)).comp P.subtype)) ∧
        finiteFrequencyKernel P eta (significant h).toList =
          finiteFrequencyKernel P (fun i => eta (indices i)) (List.finRange m) ∧
        ∀ x ∈ P.baseChange ℝ,
          (∀ j ∈ significant h, realifyFunctional (eta j) x = 0) ↔
            ∀ i, realifyFunctional (eta (indices i)) x = 0 := by
  obtain ⟨code, retained, hsub, hmass, hfixed⟩ :=
    exists_common_frequency_kernel law productive P eta (fun h => (significant h).toList)
  obtain ⟨m, hm, indices, hindices, hlin, hspan⟩ :=
    exists_restricted_frequency_basis P eta (frequencyCodeIndices code)
  have hkernel : finiteFrequencyKernel P eta (frequencyCodeIndices code) =
      finiteFrequencyKernel P (fun i => eta (indices i)) (List.finRange m) := by
    apply finiteFrequencyKernel_eq_of_span_eq
    rw [restrictedFrequencySpan_finRange]
    exact hspan.symm
  have hmass' : law.mass productive / (Fintype.card J + 1 : ℝ) ^ D ≤
      law.mass retained := by
    apply le_trans _ hmass
    apply div_le_div_of_nonneg_left (law.mass_nonneg productive) (by positivity)
    exact pow_le_pow_right₀ (le_add_of_nonneg_left (Nat.cast_nonneg _)) hD
  refine ⟨m, indices, retained, hm, hm.trans hD, hlin, hsub, hmass',
    (div_pos hproductive (by positivity)).trans_le hmass', ?_⟩
  intro h hh
  have hk : finiteFrequencyKernel P eta (significant h).toList =
      finiteFrequencyKernel P (fun i => eta (indices i)) (List.finRange m) := by
    rw [(hfixed h hh).2, ← finiteFrequencyKernel_codeIndices]
    exact hkernel
  refine ⟨?_, ?_, hk, ?_⟩
  · intro i
    obtain ⟨k, hk⟩ := (mem_frequencyCodeIndices code (indices i)).mp (hindices i)
    exact Finset.mem_toList.mp ((hfixed h hh).1 k (indices i) hk)
  · have hs := restrictedFrequencySpan_eq_of_kernel_eq P eta (significant h).toList
      (fun i => eta (indices i)) (List.finRange m) hk
    simpa only [restrictedFrequencySpan_finRange] using hs
  · intro x hx
    have heq : x ∈ (finiteFrequencyKernel P eta (significant h).toList).baseChange ℝ ↔
        x ∈ (finiteFrequencyKernel P (fun i => eta (indices i)) (List.finRange m)).baseChange ℝ := by
      rw [hk]
    simpa only [mem_real_finiteFrequencyKernel, hx, true_and,
      Finset.mem_toList, List.mem_finRange, forall_true_left] using heq

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open Module CircleFourier
open scoped TensorProduct BigOperators

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d}

theorem exists_positive_fourier_projection_basis (T : D.Niltest (fun _ : Unit => 1))
    {p rho tau B : ℝ} (hp : 0 ≤ p) (hT : T.UnitIntervalValued) (hTc : T.ComplexityLE p)
    (hrho : 0 < rho) (hrhop : rho⁻¹ ≤ Real.exp p) (htau : 0 ≤ tau) (hB : 0 ≤ B)
    {N : ℕ} [NeZero N] (weight : ZMod N → ℂ) (hweight : ∀ x, ‖weight x‖ ≤ B) :
    ∃ (J : Type) (inst : Fintype J), letI := inst
    ∃ (eta : J → L →ₗ[ℚ] ℚ) (U : J → D.Niltest (fun _ : Unit => 1))
      (S : D.Niltest (fun _ : Unit => 1)) (m : ℕ) (indices : Fin m → J),
      (Fintype.card J : ℝ) ≤ Real.exp (verticalDecompositionBudget p) ∧
      (∀ j i, rationalLogHeight (eta j (D.basis i)) ≤ verticalDecompositionBudget p) ∧
      (∀ j, (U j).ComplexityLE p ∧ (U j).orbit = T.orbit) ∧
      (∀ j (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
        (U j).observable (z • x) =
          character ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) * (U j).observable x) ∧
      m ≤ d ∧
      (∀ i, tau < ‖𝔼 n, weight n * (U (indices i)).evalCyclic N (fun _ => n)‖) ∧
      LinearIndependent ℚ (fun i => (eta (indices i)).comp (D.filtration.layer s).subtype) ∧
      S.UnitIntervalValued ∧ S.ComplexityLE p ∧ S.orbit = T.orbit ∧
      (∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup s →
        (∀ i, realifyFunctional (eta (indices i)) z.coord = 0) →
        ∀ x, S.observable (z • x) = S.observable x) ∧
      ‖(𝔼 n, weight n * T.evalCyclic N (fun _ => n)) -
        (𝔼 n, weight n * S.evalCyclic N (fun _ => n))‖ ≤
          2 * B * rho + Real.exp (verticalDecompositionBudget p) * tau := by
  classical
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  obtain ⟨J, inst, eta, U, S, hcard, hheight, hU, hvertical, _, hS, hSc, hSo, hinv, herr⟩ :=
    T.exists_positive_fourier_projection hp hT hTc hrho hrhop htau hB weight hweight
  let := inst
  let active : Finset J := Finset.univ.filter
    (fun j => tau < ‖𝔼 n, weight n * (U j).evalCyclic N (fun _ => n)‖)
  let js := active.toList
  obtain ⟨m, hm, indices, hindices, hlin, hkernel⟩ :=
    exists_restricted_frequency_basis_real_kernel (D.filtration.layer s) eta js
  have hmd : m ≤ d := hm.trans (by
    simpa only [finrank_eq_card_basis D.basis, Fintype.card_fin] using (D.filtration.layer s).finrank_le)
  refine ⟨J, inst, eta, U, S, m, indices, hcard, hheight, hU, hvertical, hmd, ?_, hlin,
    hS, hSc, hSo, ?_, herr⟩
  · intro i
    simpa only [js, active, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]
      using hindices i
  · intro z hz hbasis x
    apply hinv z hz _ x
    have hfull := (hkernel z.coord hz).mpr hbasis
    intro j hj
    exact hfull j (by simpa only [js, active, Finset.mem_toList, Finset.mem_filter,
      Finset.mem_univ, true_and] using hj)

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.NilpotentLieFiltration

variable {L Y J : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing Y] [LieAlgebra ℚ Y] {s n : ℕ}
  (F : NilpotentLieFiltration L s) (π : L →ₗ⁅ℚ⁆ Y)
  (eta : J → L →ₗ[ℚ] ℚ) (code : Fin n → Option J)

theorem pivotAnnihilatorIdeal_codeIndices
    (hK : frequencyCodeKernel (F.layer s ⊓ LinearMap.ker π.toLinearMap) eta code ≤
      F.layer s) :
    F.pivotAnnihilatorIdeal π eta (frequencyCodeIndices code) =
      F.topSubspaceIdeal
        (frequencyCodeKernel (F.layer s ⊓ LinearMap.ker π.toLinearMap) eta code) hK := by
  ext x
  change x ∈ finiteFrequencyKernel (F.layer s ⊓ LinearMap.ker π.toLinearMap) eta
      (frequencyCodeIndices code) ↔
    x ∈ frequencyCodeKernel (F.layer s ⊓ LinearMap.ker π.toLinearMap) eta code
  rw [finiteFrequencyKernel_codeIndices]

theorem quotientLie_heq_of_ideal_eq {I I' : LieIdeal ℚ L} (h : I = I')
    {t : ℕ} (hI : F.layer (t + 1) ≤ I.toSubmodule)
    (hI' : F.layer (t + 1) ≤ I'.toSubmodule) :
    HEq (F.quotientLie I hI) (F.quotientLie I' hI') := by
  subst I'
  rfl

theorem pivotQuotientFiltration_codeIndices_heq
    (hK : frequencyCodeKernel (F.layer s ⊓ LinearMap.ker π.toLinearMap) eta code ≤
      F.layer s)
    (hI : F.layer (s + 1) ≤ (F.topSubspaceIdeal
      (frequencyCodeKernel (F.layer s ⊓ LinearMap.ker π.toLinearMap) eta code) hK).toSubmodule) :
    HEq (F.pivotQuotientFiltration π eta (frequencyCodeIndices code))
      (F.quotientLie (F.topSubspaceIdeal
        (frequencyCodeKernel (F.layer s ⊓ LinearMap.ker π.toLinearMap) eta code) hK) hI) :=
  F.quotientLie_heq_of_ideal_eq (F.pivotAnnihilatorIdeal_codeIndices π eta code hK) _ hI

end Erdos3.NilpotentLieFiltration

end

end OAI

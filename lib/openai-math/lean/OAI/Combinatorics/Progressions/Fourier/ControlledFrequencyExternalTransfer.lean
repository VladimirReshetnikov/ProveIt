import OAI.Combinatorics.Progressions.Linear.ExternalFamilyKernelProjectionQuantitative
import OAI.Combinatorics.Progressions.Linear.NativeExternalKernelQuotientTransfer

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

theorem exists_controlled_frequency_quotient
    {L J : Type*} [LieRing L] [LieAlgebra ℚ L] {s d r : ℕ}
    (D : RationalFilteredNilmanifold L s d) (hs : 1 ≤ s)
    (P : Submodule ℚ L) (hP : P ≤ D.filtration.layer s)
    (vP : Fin d → L) (hspan : Submodule.span ℚ (Set.range vP) = P)
    (eta : J → L →ₗ[ℚ] ℚ) (code : Fin r → Option J)
    {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) (hr : (r : ℝ) ≤ p)
    (hvP : ∀ i j, rationalLogHeight (D.basis.repr (vP i) j) ≤ p)
    (heta : ∀ i j, rationalLogHeight (eta i (D.basis j)) ≤ p) :
    let K := frequencyCodeKernel P eta code
    let hK : K ≤ D.filtration.layer s := (finiteFrequencyKernel_le P _ _).trans hP
    let I := D.filtration.topSubspaceIdeal K hK
    let hI : D.filtration.layer (s + 1) ≤ I.toSubmodule := by rw [D.filtration.terminal]; exact bot_le
    let q := p + ((2 * p + 6) ^ 2 + 2) ^ 63 + 1
    ∃ n : ℕ, n ≤ d ∧ ∃ Q : RationalFilteredNilmanifold (L ⧸ I) s n,
      Q.filtration = D.filtration.quotientLie I hI ∧
      Q.lattice = D.lattice.map (D.filtration.quotientStepHom I hI) ∧
      Q.GeometryComplexityLE ((q + 3) ^ 11) ∧
      ∀ i j, rationalLogHeight (Q.basis.repr (lieQuotientMap I (D.basis i)) j) ≤ (q + 3) ^ 5 := by
  intro K hK I hI q
  obtain ⟨n, hn, bk, hbk⟩ := exists_frequency_code_kernel_basis_logHeight D.basis P vP hspan
    eta code hp hD.1 hr hvP heta
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by
    have : 0 ≤ ((2 * p + 6) ^ 2 + 2) ^ 63 := by positivity
    dsimp [q]
    exact (le_add_of_nonneg_right this).trans (le_add_of_nonneg_right zero_le_one)
  have hbq : ((2 * p + 6) ^ 2 + 2) ^ 63 ≤ q := by dsimp [q]; linarith
  exact D.exists_controlled_top_subspace_quotient hs K hK bk bk.span_eq hq
    (hD.mono D hpq) (fun i j => (hbk i j).trans hbq)

theorem exists_controlled_frequency_quotient_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L J : Type*} [LieRing L] [LieAlgebra ℚ L] {s d r : ℕ}
      (D : RationalFilteredNilmanifold L s d) (hs : 1 ≤ s)
      (P : Submodule ℚ L) (hP : P ≤ D.filtration.layer s)
      (vP : Fin d → L), Submodule.span ℚ (Set.range vP) = P →
      ∀ (eta : J → L →ₗ[ℚ] ℚ) (code : Fin r → Option J) (p : ℝ),
      0 ≤ p → D.GeometryComplexityLE p → (r : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (D.basis.repr (vP i) j) ≤ p) →
      (∀ i j, rationalLogHeight (eta i (D.basis j)) ≤ p) →
      let K := frequencyCodeKernel P eta code
      let hK : K ≤ D.filtration.layer s := (finiteFrequencyKernel_le P _ _).trans hP
      let I := D.filtration.topSubspaceIdeal K hK
      let hI : D.filtration.layer (s + 1) ≤ I.toSubmodule := by
        rw [D.filtration.terminal]; exact bot_le
      ∃ n : ℕ, n ≤ d ∧ ∃ Q : RationalFilteredNilmanifold (L ⧸ I) s n,
        Q.filtration = D.filtration.quotientLie I hI ∧
        Q.lattice = D.lattice.map (D.filtration.quotientStepHom I hI) ∧
        Q.GeometryComplexityLE ((p + 2) ^ C) ∧
        ∀ i j, rationalLogHeight (Q.basis.repr (lieQuotientMap I (D.basis i)) j) ≤ (p + 2) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let q := X + ((2 * X + 6) ^ 2 + 2) ^ 63 + 1
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget ((q + 3) ^ 11 + (q + 3) ^ 5)
  refine ⟨C, hC, ?_⟩
  intro L J _ _ s d r D hs P hP vP hspan eta code p hp hD hr hvP heta K hK I hI
  obtain ⟨n, hn, Q, hQF, hQL, hQ, he⟩ :=
    D.exists_controlled_frequency_quotient hs P hP vP hspan eta code hp hD hr hvP heta
  have hb : (p + ((2 * p + 6) ^ 2 + 2) ^ 63 + 1 + 3) ^ 11 +
      (p + ((2 * p + 6) ^ 2 + 2) ^ 63 + 1 + 3) ^ 5 ≤ (p + 2) ^ C := by
    simpa [X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hb11 : (p + ((2 * p + 6) ^ 2 + 2) ^ 63 + 1 + 3) ^ 11 ≤ (p + 2) ^ C := by
    have : 0 ≤ (p + ((2 * p + 6) ^ 2 + 2) ^ 63 + 1 + 3) ^ 5 := by positivity
    exact (le_add_of_nonneg_right this).trans hb
  have hb5 : (p + ((2 * p + 6) ^ 2 + 2) ^ 63 + 1 + 3) ^ 5 ≤ (p + 2) ^ C := by
    have : 0 ≤ (p + ((2 * p + 6) ^ 2 + 2) ^ 63 + 1 + 3) ^ 11 := by positivity
    exact (le_add_of_nonneg_left this).trans hb
  exact ⟨n, hn, Q, hQF, hQL, hQ.mono Q hb11, fun i j => (he i j).trans hb5⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold
open Module VectorPolynomial NilpotentLieFiltration CircleFourier
open scoped TensorProduct NNReal BigOperators Classical

theorem exists_external_marked_contractive_frequency_quotient_prefix (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M σ X Ω A : Type*}
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [Fintype Ω] [Fintype A] {d e : ℕ} (D : RationalFilteredNilmanifold L s d),
      1 ≤ s → ∀ (b : Basis (Fin e) ℚ M) (φ : L →ₗ⁅ℚ⁆ M)
        {w : σ → ℕ} (tests : X → D.Niltest w) (p : ℝ),
      0 ≤ p → D.GeometryComplexityLE p → (e : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (b.repr (φ (D.basis j)) i) ≤ p) →
      (∀ x, (tests x).UnitIntervalValued) → (∀ x, (tests x).ComplexityLE p) →
      ∀ (outer : FiniteProbabilityWeights Ω) (productive : Finset Ω), 0 < outer.mass productive →
      ∀ (localLaw : Ω → FiniteProbabilityWeights A) (physical : Ω → A → X)
        (path : Ω → A → D.RealGroup) (weight : Ω → A → ℂ),
      (∀ a x, ‖weight a x‖ ≤ Real.exp p) →
      (∀ a ∈ productive, Real.exp (-p) ≤ ((localLaw a).complexMean
        (fun x => weight a x * (tests (physical a x)).observable (QuotientGroup.mk (path a x)))).re) →
      let P := D.filtration.layer s ⊓ LinearMap.ker φ.toLinearMap
      ∃ (J : Type) (inst : Fintype J), letI := inst
      ∃ (eta : J → L →ₗ[ℚ] ℚ) (U : J → X → D.Niltest w)
        (code : Fin (finrank ℚ P) → Option J) (retained : Finset Ω),
        (Fintype.card J : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
        (∀ j i, rationalLogHeight (eta j (D.basis i)) ≤ (p + 2) ^ C) ∧
        (∀ j x, (U j x).ComplexityLE ((p + 2) ^ C) ∧
          (U j x).orbit = (tests x).orbit ∧ (U j x).normBound = (tests x).normBound ∧
          (U j x).lipBound = (tests x).lipBound) ∧
        (∀ j a (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
          (U j a).observable (z • x) =
            character ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) * (U j a).observable x) ∧
        (∀ j x y ε, (∀ z, ‖(tests x).observable z - (tests y).observable z‖ ≤ ε) →
          ∀ z, ‖(U j x).observable z - (U j y).observable z‖ ≤ ε) ∧
        retained ⊆ productive ∧ 0 < outer.mass retained ∧
        outer.mass productive * Real.exp (-((p + 2) ^ C)) ≤ outer.mass retained ∧
        (∀ a ∈ retained, ∀ i j, code i = some j → Real.exp (-((p + 2) ^ C)) <
          ‖(localLaw a).complexMean (fun x => weight a x *
            (U j (physical a x)).observable (QuotientGroup.mk (path a x)))‖) ∧
        (let K := frequencyCodeKernel P eta code
         let hK : K ≤ D.filtration.layer s := (finiteFrequencyKernel_le P _ _).trans inf_le_left
         let I := D.filtration.topSubspaceIdeal K hK
         let hI : D.filtration.layer (s + 1) ≤ I.toSubmodule := by
           rw [D.filtration.terminal]; exact bot_le
         ∃ _hker : ∀ x ∈ I, φ x = 0,
         ∃ n : ℕ, n ≤ d ∧ ∃ Q : RationalFilteredNilmanifold (L ⧸ I) s n,
           Q.filtration = D.filtration.quotientLie I hI ∧
           Q.lattice = D.lattice.map (D.filtration.quotientStepHom I hI) ∧
           Q.GeometryComplexityLE ((p + 2) ^ C) ∧
           (∀ i j, rationalLogHeight (Q.basis.repr (lieQuotientMap I (D.basis j)) i) ≤ (p + 2) ^ C) ∧
           (letI := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ I))
            letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ I)) := IsModuleTopology.isTopologicalAddGroup ℝ _
            letI := realification_moduleTopology_t2 Q.basis
            ∃ descended : X → Q.Niltest w,
              (∀ x, (descended x).UnitIntervalValued) ∧
              (∀ x, (descended x).ComplexityLE ((p + 2) ^ C)) ∧
              (∀ x y η, (∀ z, ‖(tests x).observable z - (tests y).observable z‖ ≤ η) →
                ∀ q, ‖(descended x).observable q - (descended y).observable q‖ ≤ η) ∧
              (∀ x (g : D.RealGroup), (descended x).observable (QuotientGroup.mk
                (NilpotentLieBCHGroup.realificationMap
                  (hnil := D.filtration.lowerCentralSeries_eq_bot)
                  (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap I) g)) =
                ((tests x).kernelProjection K hK).observable (QuotientGroup.mk g)) ∧
              ∀ a ∈ retained, Real.exp (-((p + 2) ^ C)) ≤ ((localLaw a).complexMean
                (fun x => weight a x * (descended (physical a x)).observable (QuotientGroup.mk
                  (NilpotentLieBCHGroup.realificationMap
                    (hnil := D.filtration.lowerCentralSeries_eq_bot)
                    (hM := Q.filtration.lowerCentralSeries_eq_bot)
                    (lieQuotientMap I) (path a x))))).re)) := by
  obtain ⟨a, _, hprojection⟩ := exists_external_family_contractive_quantitative_kernel_projection_budget
  obtain ⟨bexp, _, hspanBudget⟩ := exists_nativeTopMarkKernel_spanning_budget
  obtain ⟨c, _, hquotient⟩ := exists_controlled_frequency_quotient_budget
  obtain ⟨dexp, _, hdescent⟩ := exists_external_kernelProjection_native_descent s
  let Y : Polynomial ℕ := Polynomial.X
  let P0 := Y + (Y + 2) ^ a + (Y + 2) ^ bexp + 1
  let P1 := P0 + (P0 + 2) ^ c + 1
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget (P1 + (P1 + 2) ^ dexp)
  refine ⟨C, hC, ?_⟩
  intro L M σ X Ω A _ _ _ _ _ _ _ _ _ _ d e D hs b φ w tests p hp hD he hφ
    hunit htests outer productive hprod localLaw physical path weight hweight hscore P
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  obtain ⟨vP, hvPspan, hvP⟩ := hspanBudget D b φ p hs hp hD he hφ
  obtain ⟨J, inst, eta, U, code, projected, retained, hJ, heta, hU, hvert, hcontract, hprojected,
    hidentity, hinv, hsub, hmass, hlocal⟩ := hprojection tests p hp hD hunit htests P inf_le_left
      outer productive localLaw physical (fun a x => QuotientGroup.mk (path a x)) weight hweight hscore
  let := inst
  let q0 := p + (p + 2) ^ a + (p + 2) ^ bexp + 1
  let q1 := q0 + (q0 + 2) ^ c + 1
  have hpowa : 0 ≤ (p + 2) ^ a := by positivity
  have hpowb : 0 ≤ (p + 2) ^ bexp := by positivity
  have hq0 : 0 ≤ q0 := by dsimp [q0]; positivity
  have hpq0 : p ≤ q0 := by dsimp [q0]; linarith
  have haq0 : (p + 2) ^ a ≤ q0 := by dsimp [q0]; linarith
  have hbq0 : (p + 2) ^ bexp ≤ q0 := by dsimp [q0]; linarith
  have hq1 : 0 ≤ q1 := by dsimp [q1]; positivity
  have hpowc : 0 ≤ (q0 + 2) ^ c := by positivity
  have h01 : q0 ≤ q1 := by dsimp [q1]; linarith
  have hcq1 : (q0 + 2) ^ c ≤ q1 := by dsimp [q1]; linarith
  have hbudget' : q1 + (q1 + 2) ^ dexp ≤ (p + 2) ^ C := by
    simpa [P0, P1, Y, q0, q1, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q1 ≤ (p + 2) ^ C :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ (q1 + 2) ^ dexp)).trans hbudget'
  have hdC : (q1 + 2) ^ dexp ≤ (p + 2) ^ C :=
    (le_add_of_nonneg_left hq1).trans hbudget'
  have haC : (p + 2) ^ a ≤ (p + 2) ^ C := haq0.trans (h01.trans hqC)
  have hneg : Real.exp (-((p + 2) ^ C)) ≤ Real.exp (-((p + 2) ^ a)) :=
    Real.exp_le_exp.mpr (neg_le_neg haC)
  have hretained : 0 < outer.mass retained :=
    (mul_pos hprod (Real.exp_pos _)).trans_le hmass
  refine ⟨J, inst, eta, U, code, retained,
    hJ.trans (Real.exp_le_exp.mpr haC), fun j i => (heta j i).trans haC,
    fun j x => ⟨(hU j x).1.mono haC, (hU j x).2⟩, hvert, hcontract,
    hsub, hretained, (mul_le_mul_of_nonneg_left hneg (outer.mass_nonneg productive)).trans hmass,
    fun a ha i j hij => hneg.trans_lt ((hlocal a ha).1 i j hij), ?_⟩
  intro K hK I hI
  have hker : ∀ x ∈ I, φ x = 0 := by
    intro x hx
    exact ((mem_frequencyCodeKernel P eta code x).mp hx).1.2
  have hdim : (finrank ℚ P : ℝ) ≤ p := by
    have hb := Submodule.finrank_le P
    rw [finrank_eq_card_basis D.basis, Fintype.card_fin] at hb
    exact (Nat.cast_le.mpr hb).trans hD.1
  obtain ⟨n, hn, Q, hQF, hQL, hQ, hmap⟩ :=
    hquotient D hs P inf_le_left vP hvPspan eta code q0 hq0 (hD.mono D hpq0)
      (hdim.trans hpq0) (fun i j => (hvP i j).trans hbq0) (fun i j => (heta i j).trans haq0)
  refine ⟨hker, n, hn, Q, hQF, hQL, hQ.mono Q (hcq1.trans hqC),
    fun i j => (hmap j i).trans (hcq1.trans hqC), ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ I))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ I)) := IsModuleTopology.isTopologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 Q.basis
  obtain ⟨descended, _, _, hpositive, hcomplex, _, hrec, _, hcontraction⟩ :=
    hdescent D I hI Q hQF hQL hK tests q1 hq1
      (fun x => (htests x).mono (hpq0.trans h01)) hunit
      (hQ.mono Q hcq1) (fun i j => (hmap j i).trans hcq1)
  refine ⟨descended, hpositive, fun x => (hcomplex x).mono hdC, hcontraction, hrec, ?_⟩
  intro a ha
  have hs := hneg.trans (hlocal a ha).2
  have hIK : I.toSubmodule = frequencyCodeKernel P eta code := rfl
  simpa only [hrec, hidentity, hIK] using hs

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold
open Module VectorPolynomial NilpotentLieFiltration CircleFourier
open scoped TensorProduct NNReal BigOperators Classical

theorem exists_external_marked_frequency_quotient_prefix (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M σ X Ω A : Type*}
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [Fintype Ω] [Fintype A] {d e : ℕ} (D : RationalFilteredNilmanifold L s d),
      1 ≤ s → ∀ (b : Basis (Fin e) ℚ M) (φ : L →ₗ⁅ℚ⁆ M)
        {w : σ → ℕ} (tests : X → D.Niltest w) (p : ℝ),
      0 ≤ p → D.GeometryComplexityLE p → (e : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (b.repr (φ (D.basis j)) i) ≤ p) →
      (∀ x, (tests x).UnitIntervalValued) → (∀ x, (tests x).ComplexityLE p) →
      ∀ (outer : FiniteProbabilityWeights Ω) (productive : Finset Ω), 0 < outer.mass productive →
      ∀ (localLaw : Ω → FiniteProbabilityWeights A) (physical : Ω → A → X)
        (path : Ω → A → D.RealGroup) (weight : Ω → A → ℂ),
      (∀ a x, ‖weight a x‖ ≤ Real.exp p) →
      (∀ a ∈ productive, Real.exp (-p) ≤ ((localLaw a).complexMean
        (fun x => weight a x * (tests (physical a x)).observable (QuotientGroup.mk (path a x)))).re) →
      let P := D.filtration.layer s ⊓ LinearMap.ker φ.toLinearMap
      ∃ (J : Type) (inst : Fintype J), letI := inst
      ∃ (eta : J → L →ₗ[ℚ] ℚ) (U : J → X → D.Niltest w)
        (code : Fin (finrank ℚ P) → Option J) (retained : Finset Ω),
        (Fintype.card J : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
        (∀ j i, rationalLogHeight (eta j (D.basis i)) ≤ (p + 2) ^ C) ∧
        (∀ j x, (U j x).ComplexityLE ((p + 2) ^ C) ∧
          (U j x).orbit = (tests x).orbit ∧ (U j x).normBound = (tests x).normBound ∧
          (U j x).lipBound = (tests x).lipBound) ∧
        (∀ j a (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
          (U j a).observable (z • x) =
            character ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) * (U j a).observable x) ∧
        retained ⊆ productive ∧ 0 < outer.mass retained ∧
        outer.mass productive * Real.exp (-((p + 2) ^ C)) ≤ outer.mass retained ∧
        (∀ a ∈ retained, ∀ i j, code i = some j → Real.exp (-((p + 2) ^ C)) <
          ‖(localLaw a).complexMean (fun x => weight a x *
            (U j (physical a x)).observable (QuotientGroup.mk (path a x)))‖) ∧
        (let K := frequencyCodeKernel P eta code
         let hK : K ≤ D.filtration.layer s := (finiteFrequencyKernel_le P _ _).trans inf_le_left
         let I := D.filtration.topSubspaceIdeal K hK
         let hI : D.filtration.layer (s + 1) ≤ I.toSubmodule := by
           rw [D.filtration.terminal]; exact bot_le
         ∃ _hker : ∀ x ∈ I, φ x = 0,
         ∃ n : ℕ, n ≤ d ∧ ∃ Q : RationalFilteredNilmanifold (L ⧸ I) s n,
           Q.filtration = D.filtration.quotientLie I hI ∧
           Q.lattice = D.lattice.map (D.filtration.quotientStepHom I hI) ∧
           Q.GeometryComplexityLE ((p + 2) ^ C) ∧
           (∀ i j, rationalLogHeight (Q.basis.repr (lieQuotientMap I (D.basis j)) i) ≤ (p + 2) ^ C) ∧
           (letI := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ I))
            letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ I)) := IsModuleTopology.isTopologicalAddGroup ℝ _
            letI := realification_moduleTopology_t2 Q.basis
            ∃ descended : X → Q.Niltest w,
              (∀ x, (descended x).UnitIntervalValued) ∧
              (∀ x, (descended x).ComplexityLE ((p + 2) ^ C)) ∧
              (∀ x y η, (∀ z, ‖(tests x).observable z - (tests y).observable z‖ ≤ η) →
                ∀ q, ‖(descended x).observable q - (descended y).observable q‖ ≤ η) ∧
              (∀ x (g : D.RealGroup), (descended x).observable (QuotientGroup.mk
                (NilpotentLieBCHGroup.realificationMap
                  (hnil := D.filtration.lowerCentralSeries_eq_bot)
                  (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap I) g)) =
                ((tests x).kernelProjection K hK).observable (QuotientGroup.mk g)) ∧
              ∀ a ∈ retained, Real.exp (-((p + 2) ^ C)) ≤ ((localLaw a).complexMean
                (fun x => weight a x * (descended (physical a x)).observable (QuotientGroup.mk
                  (NilpotentLieBCHGroup.realificationMap
                    (hnil := D.filtration.lowerCentralSeries_eq_bot)
                    (hM := Q.filtration.lowerCentralSeries_eq_bot)
                    (lieQuotientMap I) (path a x))))).re)) := by
  obtain ⟨a, _, hprojection⟩ := exists_external_family_quantitative_kernel_projection_budget
  obtain ⟨bexp, _, hspanBudget⟩ := exists_nativeTopMarkKernel_spanning_budget
  obtain ⟨c, _, hquotient⟩ := exists_controlled_frequency_quotient_budget
  obtain ⟨dexp, _, hdescent⟩ := exists_external_kernelProjection_native_descent s
  let Y : Polynomial ℕ := Polynomial.X
  let P0 := Y + (Y + 2) ^ a + (Y + 2) ^ bexp + 1
  let P1 := P0 + (P0 + 2) ^ c + 1
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget (P1 + (P1 + 2) ^ dexp)
  refine ⟨C, hC, ?_⟩
  intro L M σ X Ω A _ _ _ _ _ _ _ _ _ _ d e D hs b φ w tests p hp hD he hφ
    hunit htests outer productive hprod localLaw physical path weight hweight hscore P
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  obtain ⟨vP, hvPspan, hvP⟩ := hspanBudget D b φ p hs hp hD he hφ
  obtain ⟨J, inst, eta, U, code, projected, retained, hJ, heta, hU, hvert, hprojected,
    hidentity, hinv, hsub, hmass, hlocal⟩ := hprojection tests p hp hD hunit htests P inf_le_left
      outer productive localLaw physical (fun a x => QuotientGroup.mk (path a x)) weight hweight hscore
  let := inst
  let q0 := p + (p + 2) ^ a + (p + 2) ^ bexp + 1
  let q1 := q0 + (q0 + 2) ^ c + 1
  have hpowa : 0 ≤ (p + 2) ^ a := by positivity
  have hpowb : 0 ≤ (p + 2) ^ bexp := by positivity
  have hq0 : 0 ≤ q0 := by dsimp [q0]; positivity
  have hpq0 : p ≤ q0 := by dsimp [q0]; linarith
  have haq0 : (p + 2) ^ a ≤ q0 := by dsimp [q0]; linarith
  have hbq0 : (p + 2) ^ bexp ≤ q0 := by dsimp [q0]; linarith
  have hq1 : 0 ≤ q1 := by dsimp [q1]; positivity
  have hpowc : 0 ≤ (q0 + 2) ^ c := by positivity
  have h01 : q0 ≤ q1 := by dsimp [q1]; linarith
  have hcq1 : (q0 + 2) ^ c ≤ q1 := by dsimp [q1]; linarith
  have hbudget' : q1 + (q1 + 2) ^ dexp ≤ (p + 2) ^ C := by
    simpa [P0, P1, Y, q0, q1, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q1 ≤ (p + 2) ^ C :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ (q1 + 2) ^ dexp)).trans hbudget'
  have hdC : (q1 + 2) ^ dexp ≤ (p + 2) ^ C :=
    (le_add_of_nonneg_left hq1).trans hbudget'
  have haC : (p + 2) ^ a ≤ (p + 2) ^ C := haq0.trans (h01.trans hqC)
  have hneg : Real.exp (-((p + 2) ^ C)) ≤ Real.exp (-((p + 2) ^ a)) :=
    Real.exp_le_exp.mpr (neg_le_neg haC)
  have hretained : 0 < outer.mass retained :=
    (mul_pos hprod (Real.exp_pos _)).trans_le hmass
  refine ⟨J, inst, eta, U, code, retained,
    hJ.trans (Real.exp_le_exp.mpr haC), fun j i => (heta j i).trans haC,
    fun j x => ⟨(hU j x).1.mono haC, (hU j x).2⟩, hvert,
    hsub, hretained, (mul_le_mul_of_nonneg_left hneg (outer.mass_nonneg productive)).trans hmass,
    fun a ha i j hij => hneg.trans_lt ((hlocal a ha).1 i j hij), ?_⟩
  intro K hK I hI
  have hker : ∀ x ∈ I, φ x = 0 := by
    intro x hx
    exact ((mem_frequencyCodeKernel P eta code x).mp hx).1.2
  have hdim : (finrank ℚ P : ℝ) ≤ p := by
    have hb := Submodule.finrank_le P
    rw [finrank_eq_card_basis D.basis, Fintype.card_fin] at hb
    exact (Nat.cast_le.mpr hb).trans hD.1
  obtain ⟨n, hn, Q, hQF, hQL, hQ, hmap⟩ :=
    hquotient D hs P inf_le_left vP hvPspan eta code q0 hq0 (hD.mono D hpq0)
      (hdim.trans hpq0) (fun i j => (hvP i j).trans hbq0) (fun i j => (heta i j).trans haq0)
  refine ⟨hker, n, hn, Q, hQF, hQL, hQ.mono Q (hcq1.trans hqC),
    fun i j => (hmap j i).trans (hcq1.trans hqC), ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ I))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ I)) := IsModuleTopology.isTopologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 Q.basis
  obtain ⟨descended, _, _, hpositive, hcomplex, _, hrec, _, hcontraction⟩ :=
    hdescent D I hI Q hQF hQL hK tests q1 hq1
      (fun x => (htests x).mono (hpq0.trans h01)) hunit
      (hQ.mono Q hcq1) (fun i j => (hmap j i).trans hcq1)
  refine ⟨descended, hpositive, fun x => (hcomplex x).mono hdC, hcontraction, hrec, ?_⟩
  intro a ha
  have hs := hneg.trans (hlocal a ha).2
  have hIK : I.toSubmodule = frequencyCodeKernel P eta code := rfl
  simpa only [hrec, hidentity, hIK] using hs

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold
open Module VectorPolynomial NilpotentLieFiltration
open scoped TensorProduct NNReal

theorem exists_controlled_frequency_external_transfer (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M σ X J : Type*}
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d r u : ℕ} (D : RationalFilteredNilmanifold L s d), 1 ≤ s →
      ∀ (G : NilpotentLieFiltration M u) (φ : L →ₗ⁅ℚ⁆ M)
        (vP : Fin d → L),
      Submodule.span ℚ (Set.range vP) = D.filtration.layer s ⊓ LinearMap.ker φ.toLinearMap →
      ∀ (eta : J → L →ₗ[ℚ] ℚ) (code : Fin r → Option J) (p : ℝ),
      0 ≤ p → D.GeometryComplexityLE p → (r : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (D.basis.repr (vP i) j) ≤ p) →
      (∀ i j, rationalLogHeight (eta i (D.basis j)) ≤ p) →
      ∀ {w : σ → ℕ} (tests : X → D.Niltest w),
      (∀ x, (tests x).ComplexityLE p) → (∀ x, (tests x).UnitIntervalValued) →
      let P := D.filtration.layer s ⊓ LinearMap.ker φ.toLinearMap
      let K := frequencyCodeKernel P eta code
      let hK : K ≤ D.filtration.layer s := (finiteFrequencyKernel_le P _ _).trans inf_le_left
      let I := D.filtration.topSubspaceIdeal K hK
      let hI : D.filtration.layer (s + 1) ≤ I.toSubmodule := by
        rw [D.filtration.terminal]; exact bot_le
      ∃ hker : ∀ x ∈ I, φ x = 0,
      ∃ n : ℕ, n ≤ d ∧ ∃ Q : RationalFilteredNilmanifold (L ⧸ I) s n,
        Q.filtration = D.filtration.quotientLie I hI ∧
        Q.lattice = D.lattice.map (D.filtration.quotientStepHom I hI) ∧
        Q.GeometryComplexityLE ((p + 2) ^ C) ∧
        (∀ i j, rationalLogHeight (Q.basis.repr (lieQuotientMap I (D.basis j)) i) ≤ (p + 2) ^ C) ∧
        (letI := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ I))
         let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ I)) :=
           IsModuleTopology.isTopologicalAddGroup ℝ _
         let := realification_moduleTopology_t2 Q.basis
         ∃ descended : X → Q.Niltest w,
           (∀ x, (descended x).UnitIntervalValued) ∧
           (∀ x, (descended x).ComplexityLE ((p + 2) ^ C)) ∧
           (∀ x y η, (∀ z, ‖(tests x).observable z - (tests y).observable z‖ ≤ η) →
             ∀ q, ‖(descended x).observable q - (descended y).observable q‖ ≤ η) ∧
           ∀ {Ω A : Type*} [Fintype Ω] [Fintype A]
             (q : Q.filtration.realification.PolynomialOrbit w)
             (marked : G.realification.PolynomialOrbit w),
             map ((realificationLieHom (quotientInducedMark I φ hker)).toLinearMap.restrictScalars ℚ)
               q.log = marked.log →
             ∀ (outer : FiniteProbabilityWeights Ω) (H : Finset Ω), 0 < outer.mass H →
             ∀ (localLaw : Ω → FiniteProbabilityWeights A)
               (physical : Ω → A → X) (point : Ω → A → σ → ℤ) (weight : X → ℂ)
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
                   ((tests (physical a j)).withOrbit restored).eval (point a j))).re) := by
  obtain ⟨a, _, hquotient⟩ := exists_controlled_frequency_quotient_budget
  obtain ⟨b, _, htransfer⟩ := exists_external_kernel_quotient_transfer s
  let polyX : Polynomial ℕ := Polynomial.X
  let Pbudget := polyX + (polyX + 2) ^ a + 1
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget
    (Pbudget + (Pbudget + 2) ^ b)
  refine ⟨C, hC, ?_⟩
  intro L M σ X J _ _ _ _ _ _ _ _ d r u D hs G φ vP hspan eta code p
    hp hD hr hvP heta w tests htests hunit P K hK I hI
  have hker : ∀ x ∈ I, φ x = 0 := by
    intro x hx
    exact ((mem_frequencyCodeKernel P eta code x).mp hx).1.2
  let qbudget := p + (p + 2) ^ a + 1
  have hq0 : 0 ≤ qbudget := by dsimp [qbudget]; positivity
  have hpq : p ≤ qbudget := by
    have : 0 ≤ (p + 2) ^ a := by positivity
    dsimp [qbudget]
    linarith
  have haq : (p + 2) ^ a ≤ qbudget := by dsimp [qbudget]; linarith
  have hbudget' : qbudget + (qbudget + 2) ^ b ≤ (p + 2) ^ C := by
    simpa [Pbudget, polyX, qbudget, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : qbudget ≤ (p + 2) ^ C :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ (qbudget + 2) ^ b)).trans hbudget'
  have hbC : (qbudget + 2) ^ b ≤ (p + 2) ^ C :=
    (le_add_of_nonneg_left hq0).trans hbudget'
  obtain ⟨n, hn, Q, hQF, hQL, hQ, he⟩ :=
    hquotient D hs P inf_le_left vP hspan eta code p hp hD hr hvP heta
  refine ⟨hker, n, hn, Q, hQF, hQL, hQ.mono Q (haq.trans hqC),
    fun i j => (he j i).trans (haq.trans hqC), ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ I))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ I)) :=
    IsModuleTopology.isTopologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 Q.basis
  obtain ⟨descended, hpositive, hcomplex, hcontraction, hreturn⟩ :=
    htransfer D I hI Q hQF hQL hK tests qbudget hq0
      (fun x => (htests x).mono hpq) hunit (hQ.mono Q haq) (fun i j => (he j i).trans haq)
  refine ⟨descended, hpositive, fun x => (hcomplex x).mono hbC, hcontraction, ?_⟩
  intro Ω A _ _ q marked hmark outer H hH localLaw physical point weight B δ hB hδ hweight hscore
  exact hreturn G φ hker q marked hmark outer H hH localLaw physical point weight
    hB hδ hweight hscore

end Erdos3.RationalFilteredNilmanifold

end

end OAI

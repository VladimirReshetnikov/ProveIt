import OAI.Combinatorics.Progressions.Estimates.UniformFamilyMemberNet
import OAI.Combinatorics.Progressions.Linear.KernelProjectionPresentPivotIdeal

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

variable {L σ I : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L s d)

noncomputable def externalNetNiltest (f : D.Space → ℂ) (K : ℝ≥0)
    (hcap : ∀ x, ‖f x‖ ≤ 1) (hLip : letI := D.metricSpace; LipschitzWith K f)
    {w : σ → ℕ} (orbit : D.filtration.realification.PolynomialOrbit w) : D.Niltest w where
  orbit := orbit
  observable := f
  normBound := 1
  lipBound := K
  norm_le := hcap
  lipschitz := hLip

theorem externalNetNiltest_complexity
    (f : D.Space → ℂ) (K : ℝ≥0)
    (hcap : ∀ x, ‖f x‖ ≤ 1) (hLip : letI := D.metricSpace; LipschitzWith K f)
    {w : σ → ℕ} (orbit : D.filtration.realification.PolynomialOrbit w)
    {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p)
    (hK : (K : ℝ) ≤ Real.exp p) :
    (D.externalNetNiltest f K hcap hLip orbit).ComplexityLE (p + 3) := by
  refine ⟨hD.mono D (by linarith), ?_⟩
  change Real.log (2 + (1 : ℝ) + (K : ℝ)) ≤ p + 3
  apply (Real.log_le_iff_le_exp (by positivity)).2
  have he : 1 ≤ Real.exp p := Real.one_le_exp_iff.mpr hp
  have hthree : (4 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  calc
    2 + 1 + (K : ℝ) ≤ 4 * Real.exp p := by linarith
    _ ≤ Real.exp 3 * Real.exp p := mul_le_mul_of_nonneg_right hthree (Real.exp_nonneg p)
    _ = Real.exp (p + 3) := by rw [← Real.exp_add, add_comm]

theorem exists_external_net_ordinary_test_family
    (centers : I → D.Space → ℂ) (K : ℝ≥0)
    (hcap : ∀ i x, ‖centers i x‖ ≤ 1)
    (hLip : letI := D.metricSpace; ∀ i, LipschitzWith K (centers i))
    (hpositive : ∀ i x, (centers i x).im = 0 ∧ 0 ≤ (centers i x).re ∧ (centers i x).re ≤ 1)
    {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) (hK : (K : ℝ) ≤ Real.exp p)
    {w : σ → ℕ} :
    ∃ tests : I → D.filtration.realification.PolynomialOrbit w → D.Niltest w,
      ∀ i orbit, (tests i orbit).observable = centers i ∧
        (tests i orbit).orbit = orbit ∧ (tests i orbit).UnitIntervalValued ∧
        (tests i orbit).ComplexityLE (p + 3) ∧
        ∀ x, (tests i orbit).eval x = centers i (QuotientGroup.mk
          (D.filtration.realification.polynomialOrbitEval w x orbit)) := by
  refine ⟨fun i orbit => D.externalNetNiltest (centers i) K (hcap i) (hLip i) orbit, ?_⟩
  intro i orbit
  exact ⟨rfl, rfl, hpositive i,
    D.externalNetNiltest_complexity (centers i) K (hcap i) (hLip i) orbit hp hD hK,
    fun _ => rfl⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct BigOperators NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem exists_uniform_controlled_vertical_operators {p : ℝ} (hp : 0 ≤ p)
    (hD : D.GeometryComplexityLE p) (δ : ℝ) (hδ : 0 < δ) (hδp : δ⁻¹ ≤ Real.exp p) :
    letI := D.metricSpace
    ∃ (J : Type) (inst : Fintype J), letI := inst
    ∃ (η : J → L →ₗ[ℚ] ℚ) (V : J → (D.Space → ℂ) → D.Space → ℂ),
      (Fintype.card J : ℝ) ≤ Real.exp (verticalDecompositionBudget p) ∧
      (∀ j i, rationalLogHeight (η j (D.basis i)) ≤ verticalDecompositionBudget p) ∧
      (∀ j (f g : D.Space → ℂ) (K H : ℝ≥0), LipschitzWith K f → LipschitzWith H g →
        ∀ ε : ℝ, (∀ x, ‖f x - g x‖ ≤ ε) → ∀ x, ‖V j f x - V j g x‖ ≤ ε) ∧
      ∀ (f : D.Space → ℂ) (K B : ℝ≥0), LipschitzWith K f → (∀ x, ‖f x‖ ≤ B) →
        (K : ℝ) ≤ Real.exp p →
        (∀ j, LipschitzWith K (V j f) ∧ (∀ x, ‖V j f x‖ ≤ B)) ∧
        (∀ j (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
          V j f (z • x) = character ((realifyFunctional (η j) z.coord : ℝ) : CircleFourier.Circle) * V j f x) ∧
        (∀ (z : D.RealGroup) (c : ℂ), (∀ x, f (z • x) = c * f x) →
          ∀ j x, V j f (z • x) = c * V j f x) ∧
        ∀ x, ‖(∑ j, V j f x) - f x‖ ≤ δ := by
  classical
  let := D.metricSpace
  obtain ⟨b, w, N, hlayers, _, hbinv, hN, hNp, _, _, A, hcomm, horbit, hact⟩ :=
    D.exists_controlled_central_actions hp hD
  let S : Set (Fin (finrank ℚ L)) := {j | s ≤ w j}
  let q := centralActionBudget p
  have hq : 0 ≤ q := centralActionBudget_nonneg hp
  have hpq : p ≤ q := le_centralActionBudget hp
  have hd : (Fintype.card S : ℝ) ≤ p := by
    apply (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans
    simpa only [Fintype.card_fin, finrank_eq_card_basis D.basis] using hD.1
  let O : ℝ≥0 := ⟨Real.exp q, (Real.exp_pos q).le⟩
  obtain ⟨J, inst, ν, V, hcard, hν, hcontract, hdecomp⟩ :=
    exists_uniform_controlled_commuting_circle_operators A hcomm O horbit δ q hδ hq
      (hd.trans hpq) le_rfl (hδp.trans (Real.exp_le_exp.mpr hpq))
  let η : J → L →ₗ[ℚ] ℚ := fun j => basisFrequency b S N (ν j)
  let R : ℝ := (2 * q + 2) ^ 4 + q + (p + 3) ^ 5
  have hpow : 0 ≤ (p + 3) ^ 5 := by positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hqR : q ≤ R := by dsimp [R]; nlinarith [sq_nonneg ((2 * q + 2) ^ 2)]
  have hfreq : (2 * q + 2) ^ 4 ≤ R := by dsimp [R]; linarith
  have hbas : (p + 3) ^ 5 ≤ R := by dsimp [R]; nlinarith [sq_nonneg ((2 * q + 2) ^ 2)]
  have hNq : (p + 3) ^ 9 ≤ q := by dsimp [q, centralActionBudget]; linarith
  have hterm : 2 * q * (2 * q + 2) ^ 4 ≤ verticalDecompositionBudget p := by
    change _ ≤ _ + (R + 2) ^ 4
    exact le_add_of_nonneg_right (by positivity)
  have hheight : (R + 2) ^ 4 ≤ verticalDecompositionBudget p := by
    change _ ≤ 2 * q * (2 * q + 2) ^ 4 + _
    have h : 0 ≤ 2 * q * (2 * q + 2) ^ 4 := by positivity
    linarith
  have hcentral (i : S) (z : L) : ⁅b i, z⁆ = 0 := by
    apply D.filtration.top_layer_central
    rw [hlayers s]
    exact Submodule.subset_span ⟨i, i.property, rfl⟩
  have hucentral (i : S) (z : ℝ ⊗[ℚ] L) : ⁅(N : ℝ) • b.baseChange ℝ i, z⁆ = 0 :=
    scaled_real_basis_central b i (hcentral i) N z
  refine ⟨J, inst, η, V, hcard.trans (Real.exp_le_exp.mpr hterm), ?_, hcontract, ?_⟩
  · intro j i
    exact (basisFrequency_logHeight_le D.basis b S N hN (ν j) hR (hd.trans (hpq.trans hqR))
      (hNp.trans (Real.exp_le_exp.mpr (hNq.trans hqR)))
      (fun a => (hν j a).trans (Real.exp_le_exp.mpr hfreq))
      (fun a c => (hbinv a c).trans hbas) i).trans hheight
  · intro f K B hf hb hK
    obtain ⟨hv, hchar, hpres, herr⟩ :=
      hdecomp f K B hf hb (hK.trans (Real.exp_le_exp.mpr hpq))
    refine ⟨hv, ?_, ?_, herr⟩
    · intro j z hz x
      apply central_span_character (fun i : S => (N : ℝ) • b.baseChange ℝ i) hucentral
        (realifyFunctional (η j)) (V j f) ?_ ?_ x
      · intro i r y
        have h := hchar j i (r : CircleFourier.Circle) y
        rw [hact] at h
        change _ = character ((r * realifyFunctional (basisFrequency b S N (ν j))
          ((N : ℝ) • b.baseChange ℝ i) : ℝ) : CircleFourier.Circle) * _
        rw [realify_basisFrequency_direction b S N hN (ν j) i]
        simpa only [← AddCircle.coe_zsmul, zsmul_eq_mul, mul_comm] using h
      · exact D.filtration.realLayer_le_span_scaled_basis b s S (hlayers s) N hN hz
    · intro z c hc
      apply hpres (fun x => z • x) c ?_ hc
      intro i t x
      obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective t
      rw [hact, hact, ← mul_smul, ← mul_smul]
      rw [(realBCHLine_commute _ (hucentral i) r z).eq]

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

variable {L σ I X : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L s d)

theorem exists_external_physical_member_net [Nonempty X] {w : σ → ℕ}
    (T : X → D.Niltest w) (centers : I → D.Space → ℂ) {ε p : ℝ}
    (hnet : ∀ x, ∃ i, ∀ y, ‖(T x).observable y - centers i y‖ ≤ ε)
    (hunit : ∀ x, (T x).UnitIntervalValued)
    (hcomplexity : ∀ x, (T x).ComplexityLE p) :
    ∃ rep : I → X,
      (∀ i, (T (rep i)).UnitIntervalValued ∧ (T (rep i)).ComplexityLE p) ∧
      ∀ x, ∃ i, ∀ y, ‖(T x).observable y - (T (rep i)).observable y‖ ≤ 2 * ε := by
  obtain ⟨rep, hrep⟩ := exists_uniform_family_member_net
    (fun x => (T x).observable) centers hnet
  exact ⟨rep, fun i => ⟨hunit (rep i), hcomplexity (rep i)⟩, hrep⟩

theorem exists_external_physical_member_net_of_half [Nonempty X] {w : σ → ℕ}
    (T : X → D.Niltest w) (centers : I → D.Space → ℂ) {ε p : ℝ}
    (hnet : ∀ x, ∃ i, ∀ y, ‖(T x).observable y - centers i y‖ ≤ ε / 2)
    (hunit : ∀ x, (T x).UnitIntervalValued)
    (hcomplexity : ∀ x, (T x).ComplexityLE p) :
    ∃ rep : I → X,
      (∀ i, (T (rep i)).UnitIntervalValued ∧ (T (rep i)).ComplexityLE p) ∧
      ∀ x, ∃ i, ∀ y, ‖(T x).observable y - (T (rep i)).observable y‖ ≤ ε := by
  have h := D.exists_external_physical_member_net T centers hnet hunit hcomplexity
  have he : 2 * (ε / 2) = ε := by ring
  simpa only [he] using h

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open CircleFourier
open scoped TensorProduct BigOperators

variable {σ X L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d) {w : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

private theorem contractiveFamily_integer_error {J : Type*} [Fintype J]
    (T : X → D.Niltest w) (U : J → X → D.Niltest w)
    (hU : ∀ j a, (U j a).orbit = (T a).orbit) (δ : ℝ)
    (herr : ∀ a x, ‖(T a).observable x - ∑ j, (U j a).observable x‖ ≤ δ) :
    ∀ a (x : σ → ℤ), ‖(T a).eval x - ∑ j, (U j a).eval x‖ ≤ δ := by
  intro a x
  simpa only [Niltest.eval, hU] using
    herr a (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x (T a).orbit))

private theorem contractiveFamily_real_error {J : Type*} [Fintype J]
    (T : X → D.Niltest w) (U : J → X → D.Niltest w)
    (hU : ∀ j a, (U j a).orbit = (T a).orbit) (δ : ℝ)
    (herr : ∀ a x, ‖(T a).observable x - ∑ j, (U j a).observable x‖ ≤ δ) :
    ∀ a (x : σ → ℝ), ‖(T a).evalReal x - ∑ j, (U j a).evalReal x‖ ≤ δ := by
  intro a x
  simpa only [Niltest.evalReal, hU] using
    herr a (QuotientGroup.mk (D.filtration.realification.polynomialOrbitRealEval w x (T a).orbit))

theorem exists_externalFamily_contractive_vertical_expansion {p : ℝ} (hp : 0 ≤ p)
    (hD : D.GeometryComplexityLE p) (T : X → D.Niltest w)
    (hT : ∀ a, (T a).ComplexityLE p) (δ : ℝ) (hδ : 0 < δ)
    (hδp : δ⁻¹ ≤ Real.exp p) :
    ∃ (J : Type) (inst : Fintype J), letI := inst
    ∃ (eta : J → L →ₗ[ℚ] ℚ) (U : J → X → D.Niltest w),
      (Fintype.card J : ℝ) ≤ Real.exp (verticalDecompositionBudget p) ∧
      (∀ j i, rationalLogHeight (eta j (D.basis i)) ≤ verticalDecompositionBudget p) ∧
      (∀ j a, (U j a).ComplexityLE p ∧ (U j a).orbit = (T a).orbit ∧
        (U j a).normBound = (T a).normBound ∧ (U j a).lipBound = (T a).lipBound) ∧
      (∀ j a (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
        (U j a).observable (z • x) =
          character ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) *
            (U j a).observable x) ∧
      (∀ j a, (∃ x, (U j a).observable x ≠ 0) → ∀ z : D.RealGroup,
        z ∈ D.filtration.realification.subgroup s → z ∈ D.realLattice →
          ∃ n : ℤ, realifyFunctional (eta j) z.coord = n) ∧
      (∀ a (z : D.RealGroup) (c : ℂ),
        (∀ x, (T a).observable (z • x) = c * (T a).observable x) →
          ∀ j x, (U j a).observable (z • x) = c * (U j a).observable x) ∧
      (∀ j a b (ε : ℝ), (∀ x, ‖(T a).observable x - (T b).observable x‖ ≤ ε) →
        ∀ x, ‖(U j a).observable x - (U j b).observable x‖ ≤ ε) ∧
      (∀ a x, ‖(T a).observable x - ∑ j, (U j a).observable x‖ ≤ δ) ∧
      (∀ a (x : σ → ℤ), ‖(T a).eval x - ∑ j, (U j a).eval x‖ ≤ δ) ∧
      ∀ a (x : σ → ℝ), ‖(T a).evalReal x - ∑ j, (U j a).evalReal x‖ ≤ δ := by
  classical
  let := D.metricSpace
  obtain ⟨J, inst, eta, V, hcard, hheight, hcontract, hdecomp⟩ :=
    D.exists_uniform_controlled_vertical_operators hp hD δ hδ hδp
  have hK (a : X) : ((T a).lipBound : ℝ) ≤ Real.exp p := by
    have h := Niltest.observable_budget (hT a)
    have hB := (T a).normBound.coe_nonneg
    linarith
  have hprops := fun a =>
    hdecomp (T a).observable (T a).lipBound (T a).normBound
      (T a).lipschitz (T a).norm_le (hK a)
  let v : X → J → D.Space → ℂ := fun a j => V j (T a).observable
  have hv := fun a => (hprops a).1
  have hchar := fun a => (hprops a).2.1
  have hpres := fun a => (hprops a).2.2.1
  have herr := fun a => (hprops a).2.2.2
  let U : J → X → D.Niltest w := fun j a =>
    { orbit := (T a).orbit
      observable := v a j
      normBound := (T a).normBound
      lipBound := (T a).lipBound
      norm_le := (hv a j).2
      lipschitz := (hv a j).1 }
  have herror : ∀ a x, ‖(T a).observable x - ∑ j, (U j a).observable x‖ ≤ δ := by
    intro a x
    simpa only [norm_sub_rev] using herr a x
  refine ⟨J, inst, eta, U, hcard, hheight, fun _ a => ⟨hT a, rfl, rfl, rfl⟩,
    fun j a => hchar a j, ?_, hpres, ?_, herror,
    contractiveFamily_integer_error D T U (fun _ _ => rfl) δ herror,
    contractiveFamily_real_error D T U (fun _ _ => rfl) δ herror⟩
  · intro j a hne z hz hGamma
    exact vertical_frequency_integral_on_lattice D.filtration D.realLattice (eta j) (v a j)
      (hchar a j) hne z hz hGamma
  · intro j a b ε hab x
    exact hcontract j (T a).observable (T b).observable (T a).lipBound (T b).lipBound
      (T a).lipschitz (T b).lipschitz ε hab x

theorem externalFamily_vertical_member_net
    {J I : Type*} (T : X → D.Niltest w) (U : J → X → D.Niltest w)
    (center : I → X) (ε : ℝ)
    (hcontract : ∀ j a b (r : ℝ),
      (∀ x, ‖(T a).observable x - (T b).observable x‖ ≤ r) →
        ∀ x, ‖(U j a).observable x - (U j b).observable x‖ ≤ r)
    (hnet : ∀ a, ∃ i, ∀ x, ‖(T a).observable x - (T (center i)).observable x‖ ≤ ε) :
    ∀ j a, ∃ i, ∀ x, ‖(U j a).observable x - (U j (center i)).observable x‖ ≤ ε := by
  intro j a
  obtain ⟨i, hi⟩ := hnet a
  exact ⟨i, hcontract j a (center i) ε hi⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct Classical

theorem exists_external_physical_member_pivot_masks
    {L σ X I : Type*} [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [Fintype I] [Nonempty X] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d) {w : σ → ℕ}
    (T : X → D.Niltest w) (centers : I → D.Space → ℂ) {ε p : ℝ}
    (hnet : ∀ x, ∃ i, ∀ y, ‖(T x).observable y - centers i y‖ ≤ ε / 2)
    (hunit : ∀ x, (T x).UnitIntervalValued)
    (hcomplex : ∀ x, (T x).ComplexityLE p) :
    ∃ rep : I → X,
      (∀ i, (T (rep i)).UnitIntervalValued ∧ (T (rep i)).ComplexityLE p) ∧
      (∀ x, ∃ i, ∀ y, ‖(T x).observable y - (T (rep i)).observable y‖ ≤ ε) ∧
      ∀ {τ Ω J Freq : Type*} [Fintype Ω] [Fintype J] {v : τ → ℕ}
        (U : Freq → X → D.Niltest w),
      (∀ f a b (e : ℝ),
        (∀ y, ‖(T a).observable y - (T b).observable y‖ ≤ e) →
          ∀ y, ‖(U f a).observable y - (U f b).observable y‖ ≤ e) →
      ∀ {q : ℝ}, (∀ f x, (U f x).ComplexityLE q) →
      ∀ (r : ℕ) (code : Fin r → Option Freq)
        (outer : FiniteProbabilityWeights Ω) (H : Finset Ω), 0 < outer.mass H →
      ∀ (localLaw : Ω → FiniteProbabilityWeights J)
        (localOrbit : Ω → D.filtration.realification.PolynomialOrbit v)
        (physical : Ω → J → X) (point : Ω → J → τ → ℤ) (weight : X → ℂ)
        {B δ : ℝ}, 0 ≤ B → 0 < δ → B * ε ≤ δ / 2 →
      (∀ x, ‖weight x‖ ≤ B) →
      (∀ a ∈ H, ∀ i f, code i = some f → δ ≤
        ‖(localLaw a).complexMean (fun j => weight (physical a j) *
          ((U f (physical a j)).withOrbit (localOrbit a)).eval (point a j))‖) →
      ∃ hcomponentNet : ∀ f x, ∃ i, ∀ y,
          ‖(U f x).observable y - (U f (rep i)).observable y‖ ≤ ε,
        (∀ f i, (U f (rep i)).ComplexityLE q) ∧
        ∃ (chosen : KernelProjectionPresentPivot code → I)
          (masked : KernelProjectionPresentPivot code → X → ℂ) (H' : Finset Ω),
          (∀ k x, masked k x = if externalNetIndex
            (fun x => (U (kernelProjectionSelectedPivot code k) x).observable)
            (fun i => (U (kernelProjectionSelectedPivot code k) (rep i)).observable)
            (hcomponentNet (kernelProjectionSelectedPivot code k)) x = chosen k
            then weight x else 0) ∧
          (∀ k x, ‖masked k x‖ ≤ B) ∧ H' ⊆ H ∧ 0 < outer.mass H' ∧
          outer.mass H / (Fintype.card I : ℝ) ^ r ≤ outer.mass H' ∧
          (∀ a k, ((U (kernelProjectionSelectedPivot code k) (rep (chosen k))).withOrbit
            (localOrbit a)).ComplexityLE q) ∧
          ∀ a ∈ H', ∀ k, δ / (2 * Fintype.card I) ≤
            ‖(localLaw a).complexMean (fun j => masked k (physical a j) *
              ((U (kernelProjectionSelectedPivot code k) (rep (chosen k))).withOrbit
                (localOrbit a)).eval (point a j))‖ := by
  obtain ⟨rep, hrep, hmemberNet⟩ :=
    D.exists_external_physical_member_net_of_half T centers hnet hunit hcomplex
  refine ⟨rep, hrep, hmemberNet, ?_⟩
  intro τ Ω J Freq _ _ v U hcontract q hU r code outer H hH
    localLaw localOrbit physical point weight B δ hB hδ herror hweight hscore
  let : Nonempty I := by
    obtain ⟨i, _⟩ := hnet (Classical.choice (inferInstance : Nonempty X))
    exact ⟨i⟩
  have hcomponentNet := D.externalFamily_vertical_member_net T U rep ε hcontract hmemberNet
  refine ⟨hcomponentNet, fun f i => hU f (rep i), ?_⟩
  exact exists_external_kernel_pivot_masks D code U rep hU hcomponentNet
    outer H hH localLaw localOrbit physical point weight hB hδ herror hweight hscore

end Erdos3.RationalFilteredNilmanifold

end

end OAI

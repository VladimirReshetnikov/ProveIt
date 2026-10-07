import OAI.Combinatorics.Progressions.Nilpotent.LocalMajorDenseSliceNiltest
import OAI.Combinatorics.Progressions.Nilpotent.NiltestVerticalBounds

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct BigOperators NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem exists_uniform_controlled_vertical_decomposition {p : ℝ} (hp : 0 ≤ p)
    (hD : D.GeometryComplexityLE p) (δ : ℝ) (hδ : 0 < δ) (hδp : δ⁻¹ ≤ Real.exp p) :
    letI := D.metricSpace
    ∃ (J : Type) (inst : Fintype J), letI := inst
    ∃ η : J → L →ₗ[ℚ] ℚ,
      (Fintype.card J : ℝ) ≤ Real.exp (verticalDecompositionBudget p) ∧
      (∀ j i, rationalLogHeight (η j (D.basis i)) ≤ verticalDecompositionBudget p) ∧
      ∀ (f : D.Space → ℂ) (K B : ℝ≥0), LipschitzWith K f → (∀ x, ‖f x‖ ≤ B) →
        (K : ℝ) ≤ Real.exp p →
      ∃ v : J → D.Space → ℂ,
        (∀ j, LipschitzWith K (v j) ∧ (∀ x, ‖v j x‖ ≤ B)) ∧
        (∀ j (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
          v j (z • x) = character ((realifyFunctional (η j) z.coord : ℝ) : CircleFourier.Circle) * v j x) ∧
        (∀ (z : D.RealGroup) (c : ℂ), (∀ x, f (z • x) = c * f x) →
          ∀ j x, v j (z • x) = c * v j x) ∧
        ∀ x, ‖(∑ j, v j x) - f x‖ ≤ δ := by
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
  obtain ⟨J, inst, ν, hcard, hν, hdecomp⟩ :=
    exists_uniform_controlled_commuting_circle_decomposition A hcomm O horbit δ q hδ hq
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
  refine ⟨J, inst, η, hcard.trans (Real.exp_le_exp.mpr hterm), ?_, ?_⟩
  · intro j i
    exact (basisFrequency_logHeight_le D.basis b S N hN (ν j) hR (hd.trans (hpq.trans hqR))
      (hNp.trans (Real.exp_le_exp.mpr (hNq.trans hqR)))
      (fun a => (hν j a).trans (Real.exp_le_exp.mpr hfreq))
      (fun a c => (hbinv a c).trans hbas) i).trans hheight
  · intro f K B hf hb hK
    obtain ⟨v, hv, hchar, hpres, herr⟩ :=
      hdecomp f K B hf hb (hK.trans (Real.exp_le_exp.mpr hpq))
    refine ⟨v, hv, ?_, ?_, herr⟩
    · intro j z hz x
      apply central_span_character (fun i : S => (N : ℝ) • b.baseChange ℝ i) hucentral
        (realifyFunctional (η j)) (v j) ?_ ?_ x
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

open CircleFourier
open scoped TensorProduct BigOperators

variable {σ X L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d) {w : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

private theorem externalFamily_integer_error {J : Type*} [Fintype J]
    (T : X → D.Niltest w) (U : J → X → D.Niltest w)
    (hU : ∀ j a, (U j a).orbit = (T a).orbit) (δ : ℝ)
    (herr : ∀ a x, ‖(T a).observable x - ∑ j, (U j a).observable x‖ ≤ δ) :
    ∀ a (x : σ → ℤ), ‖(T a).eval x - ∑ j, (U j a).eval x‖ ≤ δ := by
  intro a x
  simpa only [Niltest.eval, hU] using
    herr a (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x (T a).orbit))

private theorem externalFamily_real_error {J : Type*} [Fintype J]
    (T : X → D.Niltest w) (U : J → X → D.Niltest w)
    (hU : ∀ j a, (U j a).orbit = (T a).orbit) (δ : ℝ)
    (herr : ∀ a x, ‖(T a).observable x - ∑ j, (U j a).observable x‖ ≤ δ) :
    ∀ a (x : σ → ℝ), ‖(T a).evalReal x - ∑ j, (U j a).evalReal x‖ ≤ δ := by
  intro a x
  simpa only [Niltest.evalReal, hU] using
    herr a (QuotientGroup.mk (D.filtration.realification.polynomialOrbitRealEval w x (T a).orbit))

theorem exists_externalFamily_vertical_expansion {p : ℝ} (hp : 0 ≤ p)
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
      (∀ a x, ‖(T a).observable x - ∑ j, (U j a).observable x‖ ≤ δ) ∧
      (∀ a (x : σ → ℤ), ‖(T a).eval x - ∑ j, (U j a).eval x‖ ≤ δ) ∧
      ∀ a (x : σ → ℝ), ‖(T a).evalReal x - ∑ j, (U j a).evalReal x‖ ≤ δ := by
  classical
  let := D.metricSpace
  obtain ⟨J, inst, eta, hcard, hheight, hdecomp⟩ :=
    D.exists_uniform_controlled_vertical_decomposition hp hD δ hδ hδp
  have hK (a : X) : ((T a).lipBound : ℝ) ≤ Real.exp p := by
    have h := Niltest.observable_budget (hT a)
    have hB := (T a).normBound.coe_nonneg
    linarith
  choose v hv hchar hpres herr using fun a =>
    hdecomp (T a).observable (T a).lipBound (T a).normBound
      (T a).lipschitz (T a).norm_le (hK a)
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
    fun j a => hchar a j, ?_, hpres, herror,
    externalFamily_integer_error D T U (fun _ _ => rfl) δ herror,
    externalFamily_real_error D T U (fun _ _ => rfl) δ herror⟩
  intro j a hne z hz hGamma
  exact vertical_frequency_integral_on_lattice D.filtration D.realLattice (eta j) (v a j)
    (hchar a j) hne z hz hGamma

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open CircleFourier
open scoped TensorProduct BigOperators NNReal

variable {σ X L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d) {w : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem exists_externalUnitFamily_vertical_expansion {p : ℝ} (hp : 0 ≤ p)
    (hD : D.GeometryComplexityLE p) (T : X → D.Niltest w)
    (hT : ∀ a, (T a).ComplexityLE p)
    (hunit : ∀ a x, ‖(T a).observable x‖ ≤ 1) (δ : ℝ) (hδ : 0 < δ)
    (hδp : δ⁻¹ ≤ Real.exp p) :
    ∃ (J : Type) (inst : Fintype J), letI := inst
    ∃ (eta : J → L →ₗ[ℚ] ℚ) (U : J → X → D.Niltest w),
      (Fintype.card J : ℝ) ≤ Real.exp (verticalDecompositionBudget p) ∧
      (∀ j i, rationalLogHeight (eta j (D.basis i)) ≤ verticalDecompositionBudget p) ∧
      (∀ j a, (U j a).ComplexityLE p ∧ (U j a).orbit = (T a).orbit ∧
        (U j a).normBound ≤ 1 ∧ (U j a).lipBound = (T a).lipBound) ∧
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
      (∀ a x, ‖(T a).observable x - ∑ j, (U j a).observable x‖ ≤ δ) ∧
      (∀ a (x : σ → ℤ), ‖(T a).eval x - ∑ j, (U j a).eval x‖ ≤ δ) ∧
      ∀ a (x : σ → ℝ), ‖(T a).evalReal x - ∑ j, (U j a).evalReal x‖ ≤ δ := by
  classical
  let T' : X → D.Niltest w := fun a =>
    { T a with
      normBound := min (T a).normBound 1
      norm_le := fun x => by
        simpa only [NNReal.coe_min, NNReal.coe_one] using
          le_min ((T a).norm_le x) (hunit a x) }
  have hT' (a : X) : (T' a).ComplexityLE p := by
    refine ⟨(hT a).1, ?_⟩
    apply le_trans _ (hT a).2
    apply Real.log_le_log (by positivity)
    change 2 + ((min (T a).normBound 1 : ℝ≥0) : ℝ) + ((T a).lipBound : ℝ) ≤
      2 + ((T a).normBound : ℝ) + ((T a).lipBound : ℝ)
    have hmin : ((min (T a).normBound 1 : ℝ≥0) : ℝ) ≤ (T a).normBound :=
      NNReal.coe_le_coe.mpr (min_le_left (T a).normBound 1)
    linarith only [hmin]
  obtain ⟨J, inst, eta, U, hcard, hheight, hcert, hvert, hint, hpres, herr, heval, hreal⟩ :=
    D.exists_externalFamily_vertical_expansion hp hD T' hT' δ hδ hδp
  refine ⟨J, inst, eta, U, hcard, hheight, ?_, hvert, hint, hpres, herr, heval, hreal⟩
  intro j a
  refine ⟨(hcert j a).1, (hcert j a).2.1, ?_, (hcert j a).2.2.2⟩
  rw [(hcert j a).2.2.1]
  exact min_le_right (T a).normBound 1

end Erdos3.RationalFilteredNilmanifold

end

end OAI

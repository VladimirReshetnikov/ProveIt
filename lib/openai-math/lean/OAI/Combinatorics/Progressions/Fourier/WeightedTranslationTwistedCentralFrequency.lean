import OAI.Combinatorics.Progressions.Estimates.NativeFixedVerticalPower
import OAI.Combinatorics.Progressions.Estimates.WeightedTranslationCentralTop
import OAI.Combinatorics.Progressions.Nilpotent.WeightedTranslationTwistedNiltest

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open CircleFourier
open scoped TensorProduct BigOperators

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem exists_vertical_decomposition_preserving_bounds_and_characters (T : D.Niltest w)
    {p rho : ℝ} (hp : 0 ≤ p) (hT : T.ComplexityLE p) (hrho : 0 < rho)
    (hrhop : rho⁻¹ ≤ Real.exp p) :
    ∃ (J : Type) (inst : Fintype J), letI := inst
    ∃ (eta : J → L →ₗ[ℚ] ℚ) (U : J → D.Niltest w),
      (Fintype.card J : ℝ) ≤ Real.exp (verticalDecompositionBudget p) ∧
      (∀ j i, rationalLogHeight (eta j (D.basis i)) ≤ verticalDecompositionBudget p) ∧
      (∀ j, (U j).ComplexityLE p ∧ (U j).orbit = T.orbit ∧
        (U j).normBound = T.normBound ∧ (U j).lipBound = T.lipBound) ∧
      (∀ j (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
        (U j).observable (z • x) =
          character ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) * (U j).observable x) ∧
      (∀ j, (∃ x, (U j).observable x ≠ 0) → ∀ z : D.RealGroup,
        z ∈ D.filtration.realification.subgroup s → z ∈ D.realLattice →
          ∃ n : ℤ, realifyFunctional (eta j) z.coord = n) ∧
      (∀ (z : D.RealGroup) (c : ℂ), (∀ x, T.observable (z • x) = c * T.observable x) →
        ∀ j x, (U j).observable (z • x) = c * (U j).observable x) ∧
      (∀ x, ‖(∑ j, (U j).observable x) - T.observable x‖ ≤ rho) ∧
      ∀ x : σ → ℤ, ‖(∑ j, (U j).eval x) - T.eval x‖ ≤ rho := by
  let := D.metricSpace
  have hK : (T.lipBound : ℝ) ≤ Real.exp p := by
    have h := observable_budget hT
    have hB := T.normBound.coe_nonneg
    linarith
  obtain ⟨J, inst, eta, v, hcard, hheight, hv, hchar, hpres, herr⟩ :=
    D.exists_controlled_vertical_decomposition hp hT.1 T.observable T.lipBound T.normBound
      T.lipschitz T.norm_le hK rho hrho hrhop
  let U : J → D.Niltest w := fun j =>
    { orbit := T.orbit
      observable := v j
      normBound := T.normBound
      lipBound := T.lipBound
      norm_le := (hv j).2
      lipschitz := (hv j).1 }
  refine ⟨J, inst, eta, U, hcard, hheight, fun _ => ⟨hT, rfl, rfl, rfl⟩, hchar, ?_, hpres, herr, ?_⟩
  · intro j hne z hz hGamma
    exact vertical_frequency_integral_on_lattice D.filtration D.realLattice (eta j) (v j)
      (hchar j) hne z hz hGamma
  · intro x
    exact herr (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x T.orbit))

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3

open CircleFourier
open scoped TensorProduct BigOperators

theorem exists_native_vertical_pair_preserving_characters_on_finset
    {X σ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d e : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
    (D : RationalFilteredNilmanifold L s d) (D' : RationalFilteredNilmanifold M s e)
    {w : σ → ℕ} (Q : D.Niltest w) (R : D'.Niltest w)
    {p q delta rho eta : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hdelta : 0 < delta)
    (hrho : 0 < rho) (heta : 0 < eta) (hrhop : rho⁻¹ ≤ Real.exp p) (hetaq : eta⁻¹ ≤ Real.exp q)
    (hQc : Q.ComplexityLE p) (hRc : R.ComplexityLE q)
    (hQcap : (Q.normBound : ℝ) ≤ 1) (hRcap : (R.normBound : ℝ) ≤ 1)
    (hsmall : rho + Real.exp (verticalDecompositionBudget p) * eta ≤ delta / 2)
    (B : Finset X) (hB : B.Nonempty) (sample : X → σ → ℤ) (U : X → ℂ)
    (hU : ∀ x ∈ B, ‖U x‖ ≤ 1)
    (hcorr : delta ≤ ‖𝔼 x ∈ B, U x * Q.eval (sample x) * R.eval (sample x)‖) :
    ∃ (freq : L →ₗ[ℚ] ℚ) (freq' : M →ₗ[ℚ] ℚ) (V : D.Niltest w) (W : D'.Niltest w),
      V.ComplexityLE p ∧ V.orbit = Q.orbit ∧ V.normBound = Q.normBound ∧
      W.ComplexityLE q ∧ W.orbit = R.orbit ∧ W.normBound = R.normBound ∧
      (∀ i, rationalLogHeight (freq (D.basis i)) ≤ verticalDecompositionBudget p) ∧
      (∀ i, rationalLogHeight (freq' (D'.basis i)) ≤ verticalDecompositionBudget q) ∧
      (∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
        V.observable (z • x) = character ((realifyFunctional freq z.coord : ℝ) : CircleFourier.Circle) *
          V.observable x) ∧
      (∀ z, z ∈ D'.filtration.realification.subgroup s → ∀ x,
        W.observable (z • x) = character ((realifyFunctional freq' z.coord : ℝ) : CircleFourier.Circle) *
          W.observable x) ∧
      (∀ (z : D.RealGroup) (c : ℂ),
        (∀ x, Q.observable (z • x) = c * Q.observable x) →
          ∀ x, V.observable (z • x) = c * V.observable x) ∧
      (∀ (z : D'.RealGroup) (c : ℂ),
        (∀ x, R.observable (z • x) = c * R.observable x) →
          ∀ x, W.observable (z • x) = c * W.observable x) ∧
      (∃ x, V.observable x ≠ 0) ∧ (∃ x, W.observable x ≠ 0) ∧
      (delta / 2) / (Real.exp (verticalDecompositionBudget p) * Real.exp (verticalDecompositionBudget q)) ≤
        ‖𝔼 x ∈ B, U x * V.eval (sample x) * W.eval (sample x)‖ := by
  obtain ⟨I, instI, freqV, V, hI, hheightV, hcertV, hvertV, _, hpresV, _, happroxV⟩ :=
    Q.exists_vertical_decomposition_preserving_bounds_and_characters hp hQc hrho hrhop
  let := instI
  obtain ⟨J, instJ, freqW, W, hJ, hheightW, hcertW, hvertW, _, hpresW, _, happroxW⟩ :=
    R.exists_vertical_decomposition_preserving_bounds_and_characters hq hRc heta hetaq
  let := instJ
  obtain ⟨i, j, hbias⟩ := exists_correlating_components_on_finset B hB U
    (fun x => Q.eval (sample x)) (fun x => R.eval (sample x))
    (fun i x => (V i).eval (sample x)) (fun j x => (W j).eval (sample x))
    hdelta (Real.exp_pos _) (Real.exp_pos _) hrho.le heta.le hI hJ hU
    (fun x _ => (R.norm_eval_le (sample x)).trans hRcap)
    (fun i x _ => ((V i).norm_eval_le (sample x)).trans (by rw [(hcertV i).2.2.1]; exact hQcap))
    (fun x _ => by simpa only [norm_sub_rev] using happroxV (sample x))
    (fun x _ => by simpa only [norm_sub_rev] using happroxW (sample x)) hsmall hcorr
  have hbiaspos : 0 < ‖𝔼 x ∈ B, U x * (V i).eval (sample x) * (W j).eval (sample x)‖ :=
    lt_of_lt_of_le (div_pos (div_pos hdelta (by norm_num))
      (mul_pos (Real.exp_pos _) (Real.exp_pos _))) hbias
  have hVne : ∃ x, (V i).observable x ≠ 0 := by
    by_contra! hzero
    have heval : ∀ x, (V i).eval (sample x) = 0 := fun x => hzero _
    simp [heval] at hbiaspos
  have hWne : ∃ x, (W j).observable x ≠ 0 := by
    by_contra! hzero
    have heval : ∀ x, (W j).eval (sample x) = 0 := fun x => hzero _
    simp [heval] at hbiaspos
  exact ⟨freqV i, freqW j, V i, W j, (hcertV i).1, (hcertV i).2.1, (hcertV i).2.2.1,
    (hcertW j).1, (hcertW j).2.1, (hcertW j).2.2.1, hheightV i, hheightW j, hvertV i, hvertW j,
    (fun z c hz => hpresV z c hz i), (fun z c hz => hpresW z c hz j), hVne, hWne, hbias⟩

end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped TensorProduct BigOperators

theorem exists_native_vertical_pair_preserving_characters_power :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X σ L M : Type*}
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s d e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      (D : RationalFilteredNilmanifold L s d) (D' : RationalFilteredNilmanifold M s e)
      {w : σ → ℕ} (Q : D.Niltest w) (R : D'.Niltest w) (p : ℝ), 0 ≤ p →
      Q.ComplexityLE p → R.ComplexityLE p →
      (Q.normBound : ℝ) ≤ 1 → (R.normBound : ℝ) ≤ 1 →
      ∀ (B : Finset X), B.Nonempty → ∀ (sample : X → σ → ℤ) (U : X → ℂ),
      (∀ x ∈ B, ‖U x‖ ≤ 1) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ B, U x * Q.eval (sample x) * R.eval (sample x)‖ →
      ∃ (freq : L →ₗ[ℚ] ℚ) (freq' : M →ₗ[ℚ] ℚ) (V : D.Niltest w) (W : D'.Niltest w),
        V.ComplexityLE ((p + C) ^ C) ∧ V.orbit = Q.orbit ∧ V.normBound = Q.normBound ∧
        W.ComplexityLE ((p + C) ^ C) ∧ W.orbit = R.orbit ∧ W.normBound = R.normBound ∧
        (∀ i, rationalLogHeight (freq (D.basis i)) ≤ (p + C) ^ C) ∧
        (∀ i, rationalLogHeight (freq' (D'.basis i)) ≤ (p + C) ^ C) ∧
        (∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
          V.observable (z • x) = character ((realifyFunctional freq z.coord : ℝ) : CircleFourier.Circle) *
            V.observable x) ∧
        (∀ z, z ∈ D'.filtration.realification.subgroup s → ∀ x,
          W.observable (z • x) = character ((realifyFunctional freq' z.coord : ℝ) : CircleFourier.Circle) *
            W.observable x) ∧
        (∀ (z : D.RealGroup) (c : ℂ),
          (∀ x, Q.observable (z • x) = c * Q.observable x) →
            ∀ x, V.observable (z • x) = c * V.observable x) ∧
        (∀ (z : D'.RealGroup) (c : ℂ),
          (∀ x, R.observable (z • x) = c * R.observable x) →
            ∀ x, W.observable (z • x) = c * W.observable x) ∧
        (∃ x, V.observable x ≠ 0) ∧ (∃ x, W.observable x ≠ 0) ∧
        Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 x ∈ B, U x * V.eval (sample x) * W.eval (sample x)‖ := by
  obtain ⟨C, hC, hprecision⟩ := exists_vertical_pair_precision
  refine ⟨C, hC, ?_⟩
  intro X σ L M _ _ _ _ s d e _ _ _ _ _ _ _ _ D D' w Q R p hp hQ hR hQcap hRcap
    B hB sample U hU hcorr
  obtain ⟨q, r, rho, eta, hpq, hpr, hqC, hrC, hVq, hVr, hrho, heta, hrhoq, hetar, hsmall, hloss⟩ :=
    hprecision p hp
  obtain ⟨freq, freq', V, W, hVc, hVo, hVn, hWc, hWo, hWn, hVheight, hWheight,
      hvertV, hvertW, hpresV, hpresW, hVne, hWne, hbias⟩ :=
    exists_native_vertical_pair_preserving_characters_on_finset D D' Q R
      (hp.trans hpq) (hp.trans hpr) (Real.exp_pos _) hrho heta hrhoq hetar
      (hQ.mono hpq) (hR.mono hpr) hQcap hRcap hsmall B hB sample U hU hcorr
  exact ⟨freq, freq', V, W, hVc.mono hqC, hVo, hVn, hWc.mono hrC, hWo, hWn,
    fun i => (hVheight i).trans hVq, fun i => (hWheight i).trans hVr,
    hvertV, hvertW, hpresV, hpresW, hVne, hWne, hloss.trans hbias⟩

end Erdos3

end

section

namespace Erdos3.PolynomialTranslationLie
open MvPolynomial CircleFourier
open scoped TensorProduct

variable {m : ℕ} (w : Fin m → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hd : 0 < d) (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)]

 theorem central_character_eq_fourierChar (t : ℝ) :
    character (t : CircleFourier.Circle) = (Real.fourierChar t : ℂ) := by
  rw [character_coe_exp, Real.fourierChar_apply]
  congr 1
  push_cast
  ring

theorem weightedTranslation_frequency_one_of_central
    {σ : Type*} [Fintype σ] (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hd : 0 < d) (hwd : ∀ i, w i ≤ d)
    (Γ : Subgroup (weightedFiltration w d hwd).realification.Group)
    (η : weightedSubalgebra w d →ₗ[ℚ] ℚ)
    (f : (weightedFiltration w d hwd).realification.Group ⧸ Γ → ℂ)
    (hvert : ∀ z ∈ (weightedFiltration w d hwd).realification.subgroup d, ∀ x,
      f (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * f x)
    (hne : ∃ x, f x ≠ 0)
    (hline : ∀ t x, f (centralRealLine w d hw hd hwd t • x) =
      (Real.fourierChar t : ℂ) * f x) :
    η (centralRationalElement w d hd 1) = 1 := by
  apply vertical_frequency_eq_one_of_real_line (weightedFiltration w d hwd) Γ
    η f hvert hne _ (centralRationalElement_mem_top w d hd hwd 1)
  intro t x
  have he : (⟨t ⊗ₜ[ℚ] centralRationalElement w d hd 1⟩ :
      (weightedFiltration w d hwd).realification.Group) = centralRealLine w d hw hd hwd t := by
    apply NilpotentLieBCHGroup.ext
    exact (centralRealLine_coord w d hw hd hwd t).symm
  rw [he, central_character_eq_fourierChar]
  exact hline t x

theorem weightedTranslation_selected_frequency_one
    (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ)
    (η : weightedSubalgebra w d →ₗ[ℚ] ℚ)
    (f : (weightedTranslationNilmanifold w d hw hwd).Space → ℂ)
    (hvert : ∀ z ∈ (weightedFiltration w d hwd).realification.subgroup d, ∀ x,
      f (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * f x)
    (hne : ∃ x, f x ≠ 0)
    (hpres : ∀ (z : (weightedFiltration w d hwd).realification.Group) (c : ℂ),
      (∀ x, weightedTranslationBufferedObservable w d hw hwd Ψ D₀ (z • x) =
        c * weightedTranslationBufferedObservable w d hw hwd Ψ D₀ x) →
      ∀ x, f (z • x) = c * f x) :
    η (centralRationalElement w d hd 1) = 1 := by
  apply vertical_frequency_eq_one_of_real_line
    (weightedFiltration w d hwd) (weightedTranslationNilmanifold w d hw hwd).realLattice
    η f hvert hne _ (centralRationalElement_mem_top w d hd hwd 1)
  intro t x
  have he : (⟨t ⊗ₜ[ℚ] centralRationalElement w d hd 1⟩ :
      (weightedFiltration w d hwd).realification.Group) = centralRealLine w d hw hd hwd t := by
    apply NilpotentLieBCHGroup.ext
    exact (centralRealLine_coord w d hw hd hwd t).symm
  rw [he, central_character_eq_fourierChar]
  apply hpres
  intro y
  rw [weightedTranslationBufferedObservable_central w d hw hd hwd]
  exact mul_comm _ _

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial CircleFourier

variable {m : ℕ} (w : Fin m → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hd : 0 < d) (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)]
    (M : ℕ) (hM : 0 < M)

theorem weightedTranslationTwistedObservable_central
    (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ) (t : ℝ)
    (x : (weightedTranslationResidueNilmanifold w d hw hwd M hM).Space) :
    weightedTranslationTwistedObservable w d hw hwd M hM Ψ D₀ T
      (centralRealLine w d hw hd hwd t • x) =
      weightedTranslationTwistedObservable w d hw hwd M hM Ψ D₀ T x *
        (Real.fourierChar t : ℂ) := by
  induction x using Quotient.inductionOn with
  | h g =>
    change weightedTranslationTwistedObservable w d hw hwd M hM Ψ D₀ T
      (QuotientGroup.mk (centralRealLine w d hw hd hwd t * g)) = _
    rw [(centralRealLine_commute w d hw hd hwd t g).eq]
    simp only [weightedTranslationTwistedObservable_mk, map_mul, centralRealLine_map]
    exact twistedBufferedTranslationPhase_central M Ψ D₀ T _ t

theorem weightedTranslation_twisted_selected_frequency_one
    (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (η : weightedSubalgebra w d →ₗ[ℚ] ℚ)
    (f : (weightedTranslationResidueNilmanifold w d hw hwd M hM).Space → ℂ)
    (hvert : ∀ z ∈ (weightedFiltration w d hwd).realification.subgroup d, ∀ x,
      f (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * f x)
    (hne : ∃ x, f x ≠ 0)
    (hpres : ∀ (z : (weightedFiltration w d hwd).realification.Group) (c : ℂ),
      (∀ x, weightedTranslationTwistedObservable w d hw hwd M hM Ψ D₀ T (z • x) =
        c * weightedTranslationTwistedObservable w d hw hwd M hM Ψ D₀ T x) →
      ∀ x, f (z • x) = c * f x) :
    η (centralRationalElement w d hd 1) = 1 := by
  apply weightedTranslation_frequency_one_of_central w d hw hd hwd
    (weightedTranslationResidueNilmanifold w d hw hwd M hM).realLattice η f hvert hne
  intro t x
  apply hpres
  intro y
  rw [weightedTranslationTwistedObservable_central w d hw hd hwd M hM]
  exact mul_comm _ _

end Erdos3.PolynomialTranslationLie

end

end OAI

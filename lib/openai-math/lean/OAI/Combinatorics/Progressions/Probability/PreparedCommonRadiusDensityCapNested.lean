import OAI.Combinatorics.Progressions.Estimates.PreparedFiniteForwardFixedCenterThreshold
import OAI.Combinatorics.Progressions.Sampling.ForecastPreparedScaleBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators NNReal

private theorem exists_commonRadius_densityCap_bound (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ p : ℝ, 0 ≤ p → (m : ℝ) ≤ p →
      ∀ a n : Fin m → ℕ, (∀ j, (a j : ℝ) ≤ p) → (∀ j, (n j : ℝ) ≤ p) →
      ∀ V : Fin m → ℝ≥0, (∀ j, (V j : ℝ) ≤ Real.exp p) →
      (probabilityProfileLipschitz : ℝ) ≤ Real.exp p →
      4 * ∏ j, earlyConstantDensityCap (a j) (n j)
        (allocatedCommonProductRadius m p p) (V j) ≤ Real.exp ((p + A) ^ A) := by
  let rad : Polynomial ℕ := allocatedCommonProductRadiusLog m Polynomial.X Polynomial.X
  let env : Polynomial ℕ := Polynomial.X + rad + 4
  let cap : Polynomial ℕ := 3 * env ^ 3 + 17 * env ^ 2 + 4
  obtain ⟨A, hA, hbound⟩ := exists_natPolynomial_eval_budget cap
  refine ⟨A, hA, ?_⟩
  intro p hp hm a n ha hn V hV hprofile
  let E := p + allocatedCommonProductRadiusLog m p p + 4
  obtain ⟨hrad, hR, _, hRinv, _⟩ := allocatedCommonProductRadius_bounds m hp hp
  have hpE : p ≤ E := by dsimp only [E]; linarith
  have hradE : allocatedCommonProductRadiusLog m p p ≤ E := by dsimp only [E]; linarith
  have hE : 0 ≤ E := hp.trans hpE
  have heval : env.eval₂ (Nat.castRingHom ℝ) p = E := by
    simp [env, rad, E, allocatedCommonProductRadiusLog, allocatedCommonRadiusLog,
      allocatedBufferedRadiusLog, allocatedBufferedRadiusInput, allocatedProductChartLog,
      allocatedIdealCoverPrimitiveLog, allocatedIdealCoverInputLog, allocatedSiteCoefficientLog,
      allocatedComparisonDimension, Polynomial.eval₂_pow]
  have hcap : earlyFiberCapLog E + 4 ≤ (p + A) ^ A := by
    simpa only [cap, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_ofNat, heval, earlyFiberCapLog] using hbound p hp
  have hprod := earlyFiberCap_exp_bound a n (fun _ => allocatedCommonProductRadius m p p)
    (fun j => (V j : ℝ)) hE (hm.trans hpE) (fun _ => hR)
    (fun j => (V j).coe_nonneg) (fun j => (ha j).trans hpE)
    (fun j => (hn j).trans hpE) (hprofile.trans (Real.exp_le_exp.mpr hpE))
    (fun _ => hRinv.le.trans (Real.exp_le_exp.mpr hradE))
    (fun j => (hV j).trans (Real.exp_le_exp.mpr hpE))
  calc
    4 * ∏ j, earlyConstantDensityCap (a j) (n j)
        (allocatedCommonProductRadius m p p) (V j)
      ≤ Real.exp 4 * Real.exp (earlyFiberCapLog E) :=
        mul_le_mul (by linarith [Real.add_one_le_exp (4 : ℝ)]) hprod
          (Finset.prod_nonneg (fun j _ => earlyConstantDensityCap_nonneg _ _ hR (V j).coe_nonneg))
          (Real.exp_nonneg _)
    _ = Real.exp (earlyFiberCapLog E + 4) := by rw [← Real.exp_add, add_comm]
    _ ≤ _ := Real.exp_le_exp.mpr hcap

theorem exists_commonRadius_densityCap_uniform_bound (maxLayers : ℕ) :
    ∃ A₀ : ℕ, 2 ≤ A₀ ∧ ∀ A : ℕ, A₀ ≤ A →
      ∀ m : ℕ, m ≤ maxLayers → ∀ p : ℝ, 0 ≤ p → (m : ℝ) ≤ p →
      ∀ a n : Fin m → ℕ, (∀ j, (a j : ℝ) ≤ p) → (∀ j, (n j : ℝ) ≤ p) →
      ∀ V : Fin m → ℝ≥0, (∀ j, (V j : ℝ) ≤ Real.exp p) →
      (probabilityProfileLipschitz : ℝ) ≤ Real.exp p →
      4 * ∏ j, earlyConstantDensityCap (a j) (n j)
        (allocatedCommonProductRadius m p p) (V j) ≤ Real.exp ((p + A) ^ A) := by
  classical
  choose ex hex hb using fun j : Fin (maxLayers + 1) => exists_commonRadius_densityCap_bound j.val
  let A₀ := 2 + ∑ j, ex j
  refine ⟨A₀, by dsimp only [A₀]; omega, ?_⟩
  intro A hA m hm p hp hmp a n ha hn V hV hprofile
  let j : Fin (maxLayers + 1) := ⟨m, by omega⟩
  have hsum : ex j ≤ ∑ i, ex i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hEA : ex j ≤ A := by dsimp only [A₀] at hA; omega
  have hAtwo : (2 : ℝ) ≤ A := by exact_mod_cast (hex j).trans hEA
  have hpow : (p + ex j) ^ ex j ≤ (p + A) ^ A :=
    (pow_le_pow_left₀ (by positivity) (add_le_add le_rfl (Nat.cast_le.mpr hEA)) _).trans
      (pow_le_pow_right₀ (by linarith) hEA)
  exact (hb j p hp hmp a n ha hn V hV hprofile).trans (Real.exp_le_exp.mpr hpow)

theorem exists_prepared_commonRadius_densityCap_forward_bound (maxLayers : ℕ) :
    ∃ A₀ : ℕ, 2 ≤ A₀ ∧ ∀ A : ℕ, A₀ ≤ A →
      ∀ {X J : Type} {m : ℕ} (prep : RankPreparationFamily X J m),
      m ≤ maxLayers → ∀ M Jalloc : ℕ,
      (∀ j, Fintype.card (prep j).Coord ≤ M) →
      ∀ p : ℝ, 0 ≤ p → (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ p →
      ∀ V : Fin m → ℝ≥0, (∀ j, (V j : ℝ) ≤ Real.exp p) →
      (probabilityProfileLipschitz : ℝ) ≤ Real.exp p →
      ∀ stageCountConstant : ℕ → ℕ, ∀ stage : ℕ,
      4 * ∏ j, earlyConstantDensityCap (Fintype.card (PreparedSamplerContinuous prep j))
        (preparedSamplerTransverse prep j) (allocatedCommonProductRadius m p p) (V j) ≤
          Real.exp (preparedFiniteForwardWork A stageCountConstant stage p) := by
  obtain ⟨A₀, hA₀, hcap⟩ := exists_commonRadius_densityCap_uniform_bound maxLayers
  refine ⟨A₀, hA₀, ?_⟩
  intro A hA X J m prep hm M Jalloc hM p hp hnum V hV hprofile constants stage
  obtain ⟨_, hI, hn⟩ := enlargedPreparedCommonSampler_dimensions prep Jalloc hM
  have hmdim : m ≤ enlargedPreparedCommonSamplerDimension m M Jalloc := by
    unfold enlargedPreparedCommonSamplerDimension
    omega
  have h := hcap A hA m hm p hp ((Nat.cast_le.mpr hmdim).trans hnum)
    (fun j => Fintype.card (PreparedSamplerContinuous prep j)) (preparedSamplerTransverse prep)
    (fun j => (Nat.cast_le.mpr (hI j)).trans hnum)
    (fun j => (Nat.cast_le.mpr (hn j)).trans hnum) V hV hprofile
  apply h.trans (Real.exp_le_exp.mpr ?_)
  rw [preparedFiniteForwardWork_eq]
  exact pow_le_pow_left₀ (by positivity)
    (add_le_add (le_preparedFiniteForwardParameter A constants stage hp) le_rfl) A

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators NNReal

theorem exists_prepared_commonRadius_densityCap_nested_bound (maxLayers : ℕ) :
    ∃ A₀ : ℕ, 2 ≤ A₀ ∧ ∀ A : ℕ, A₀ ≤ A →
      ∀ {X J : Type} {m : ℕ} (prep : RankPreparationFamily X J m),
      m ≤ maxLayers → ∀ M Jalloc : ℕ,
      (∀ j, Fintype.card (prep j).Coord ≤ M) →
      ∀ p : ℝ, 0 ≤ p → (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ p →
      ∀ V : Fin m → ℝ≥0, (∀ j, (V j : ℝ) ≤ Real.exp p) →
      (probabilityProfileLipschitz : ℝ) ≤ Real.exp p →
      ∀ constants : ℕ → ℕ, ∀ innerDepth outer inner : ℕ,
      4 * ∏ j, earlyConstantDensityCap (Fintype.card (PreparedSamplerContinuous prep j))
        (preparedSamplerTransverse prep j) (allocatedCommonProductRadius m p p) (V j) ≤
          Real.exp (preparedFiniteForwardWork A constants inner
            (candidateNestedForwardSeed A constants innerDepth outer p)) := by
  obtain ⟨A₀, hA₀, hcap⟩ := exists_prepared_commonRadius_densityCap_forward_bound maxLayers
  refine ⟨A₀, hA₀, ?_⟩
  intro A hA X J m prep hm M Jalloc hM p hp hnum V hV hprofile
    constants innerDepth outer inner
  have hAtwo : 2 ≤ A := hA₀.trans hA
  have h := hcap A hA prep hm M Jalloc hM p hp hnum V hV hprofile constants 0
  apply h.trans (Real.exp_le_exp.mpr ?_)
  rw [preparedFiniteForwardWork_eq, preparedFiniteForwardParameter_zero,
    preparedFiniteForwardWork_eq]
  apply pow_le_pow_left₀ (add_nonneg hp (Nat.cast_nonneg A))
  exact add_le_add
    ((le_candidateNestedForwardSeed A constants innerDepth outer hAtwo hp).trans
      (le_preparedFiniteForwardParameter A constants inner
        (candidateNestedForwardSeed_nonneg A constants innerDepth outer hp))) le_rfl

noncomputable def preparedCommonRadiusDensityCapNestedExponent (maxLayers : ℕ) : ℕ :=
  Classical.choose (exists_prepared_commonRadius_densityCap_nested_bound maxLayers)

theorem preparedCommonRadiusDensityCapNestedExponent_two_le (maxLayers : ℕ) :
    2 ≤ preparedCommonRadiusDensityCapNestedExponent maxLayers :=
  (Classical.choose_spec (exists_prepared_commonRadius_densityCap_nested_bound maxLayers)).1

theorem prepared_commonRadius_densityCap_nested_bound (maxLayers A : ℕ)
    (hA : preparedCommonRadiusDensityCapNestedExponent maxLayers ≤ A)
    {X J : Type} {m : ℕ} (prep : RankPreparationFamily X J m)
    (hm : m ≤ maxLayers) (M Jalloc : ℕ)
    (hM : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (p : ℝ) (hp : 0 ≤ p)
    (hnum : (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ p)
    (V : Fin m → ℝ≥0) (hV : ∀ j, (V j : ℝ) ≤ Real.exp p)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp p)
    (constants : ℕ → ℕ) (innerDepth outer inner : ℕ) :
    4 * ∏ j, earlyConstantDensityCap (Fintype.card (PreparedSamplerContinuous prep j))
      (preparedSamplerTransverse prep j) (allocatedCommonProductRadius m p p) (V j) ≤
        Real.exp (preparedFiniteForwardWork A constants inner
          (candidateNestedForwardSeed A constants innerDepth outer p)) :=
  (Classical.choose_spec (exists_prepared_commonRadius_densityCap_nested_bound maxLayers)).2
    A hA prep hm M Jalloc hM p hp hnum V hV hprofile constants innerDepth outer inner

end Erdos3.VectorPolynomial

end

end OAI

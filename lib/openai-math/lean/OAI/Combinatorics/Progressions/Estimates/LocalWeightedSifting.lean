-- Modified for ProveIt: added `import OAI.Compat.*` lines (backported names); see lib/openai-math/README.md.
import OAI.Combinatorics.Progressions.Probability.FinitePairProbability
import OAI.Combinatorics.Progressions.Probability.RectangleDensity
import OAI.Combinatorics.Progressions.Sampling.LocalWeightedSampling
import OAI.Compat.BigOperators

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_subset_sum_ge_weighted {ι : Type*} (S : Finset ι)
    (u f : ι → ℝ) (hu : ∀ a ∈ S, 0 ≤ u a ∧ u a ≤ 1) :
    ∃ A ⊆ S, (∑ a ∈ S, u a * f a) ≤ ∑ a ∈ A, f a := by
  classical
  refine ⟨S.filter (fun a => 0 ≤ f a), Finset.filter_subset _ _, ?_⟩
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro a ha
  by_cases hf : 0 ≤ f a
  · simpa only [hf, ite_true, one_mul] using mul_le_mul_of_nonneg_right (hu a ha).2 hf
  · simp only [hf, ite_false]
    exact mul_nonpos_of_nonneg_of_nonpos (hu a ha).1 (le_of_not_ge hf)

theorem exists_rectangle_sum_ge_weighted {ι κ : Type*} (S : Finset ι) (T : Finset κ)
    (u : ι → ℝ) (v : κ → ℝ) (w : ι → κ → ℝ)
    (hu : ∀ a ∈ S, 0 ≤ u a ∧ u a ≤ 1)
    (hv : ∀ b ∈ T, 0 ≤ v b ∧ v b ≤ 1) :
    ∃ A ⊆ S, ∃ B ⊆ T,
      (∑ a ∈ S, ∑ b ∈ T, u a * v b * w a b) ≤ ∑ a ∈ A, ∑ b ∈ B, w a b := by
  obtain ⟨A, hAS, hA⟩ := exists_subset_sum_ge_weighted S u
    (fun a => ∑ b ∈ T, v b * w a b) hu
  obtain ⟨B, hBT, hB⟩ := exists_subset_sum_ge_weighted T v
    (fun b => ∑ a ∈ A, w a b) hv
  refine ⟨A, hAS, B, hBT, ?_⟩
  calc
    _ = ∑ a ∈ S, u a * ∑ b ∈ T, v b * w a b := by
      simp only [Finset.mul_sum, mul_assoc]
    _ ≤ ∑ a ∈ A, ∑ b ∈ T, v b * w a b := hA
    _ = ∑ b ∈ T, v b * ∑ a ∈ A, w a b := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ ∑ b ∈ B, ∑ a ∈ A, w a b := hB
    _ = _ := Finset.sum_comm

end Erdos3

end

section

namespace Erdos3.WeightedSifting

open scoped BigOperators

variable {Ω ι κ : Type*}

noncomputable def sampleWeight (P : Ω → ι → ℝ) {q : ℕ} (t : Fin q → Ω) (a : ι) : ℝ :=
  ∏ i, P (t i) a

theorem sampleWeight_bounds (P : Ω → ι → ℝ) {q : ℕ} (t : Fin q → Ω) (a : ι)
    (hP : ∀ x, 0 ≤ P x a ∧ P x a ≤ 1) :
    0 ≤ sampleWeight P t a ∧ sampleWeight P t a ≤ 1 := by
  constructor
  · exact Finset.prod_nonneg (fun i _ => (hP (t i)).1)
  · exact Finset.prod_le_one₀ (fun i _ => (hP (t i)).1) (fun i _ => (hP (t i)).2)

variable [Fintype Ω]

theorem expect_sampleWeight_mul (P : Ω → ι → ℝ) (Q : Ω → κ → ℝ)
    (q : ℕ) (a : ι) (b : κ) :
    (𝔼 t : Fin q → Ω, sampleWeight P t a * sampleWeight Q t b) =
      (𝔼 x : Ω, P x a * Q x b) ^ q := by
  simpa only [sampleWeight, ← Finset.prod_mul_distrib, Fintype.piFinset_univ] using
    (Finset.expect_pow Finset.univ (fun x => P x a * Q x b) q).symm

theorem expect_sample_score (P : Ω → ι → ℝ) (Q : Ω → κ → ℝ)
    (q : ℕ) (S : Finset ι) (T : Finset κ) (w : ι → κ → ℝ) :
    (𝔼 t : Fin q → Ω, ∑ a ∈ S, ∑ b ∈ T,
      sampleWeight P t a * sampleWeight Q t b * w a b) =
      ∑ a ∈ S, ∑ b ∈ T, (𝔼 x : Ω, P x a * Q x b) ^ q * w a b := by
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [← Finset.expect_mul, expect_sampleWeight_mul]

theorem exists_rectangle_score_ge [Nonempty Ω]
    (P : Ω → ι → ℝ) (Q : Ω → κ → ℝ) (q : ℕ)
    (S : Finset ι) (T : Finset κ) (w : ι → κ → ℝ)
    (hP : ∀ x, ∀ a ∈ S, 0 ≤ P x a ∧ P x a ≤ 1)
    (hQ : ∀ x, ∀ b ∈ T, 0 ≤ Q x b ∧ Q x b ≤ 1) :
    ∃ A ⊆ S, ∃ B ⊆ T,
      (∑ a ∈ S, ∑ b ∈ T, (𝔼 x : Ω, P x a * Q x b) ^ q * w a b) ≤
        ∑ a ∈ A, ∑ b ∈ B, w a b := by
  obtain ⟨t, _, ht⟩ := Finset.exists_le_of_le_expect
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin q → Ω)).Nonempty)
    (le_of_eq (expect_sample_score P Q q S T w).symm)
  obtain ⟨A, hAS, B, hBT, hAB⟩ := exists_rectangle_sum_ge_weighted S T
    (sampleWeight P t) (sampleWeight Q t) w
    (fun a ha => sampleWeight_bounds P t a (fun x => hP x a ha))
    (fun b hb => sampleWeight_bounds Q t b (fun x => hQ x b hb))
  exact ⟨A, hAS, B, hBT, ht.trans hAB⟩

end Erdos3.WeightedSifting

end

section

namespace Erdos3.WeightedSifting

open scoped BigOperators

variable {Ω ι κ : Type*} [Fintype Ω] [Nonempty Ω]

theorem exists_dense_rectangle_of_score
    (P : Ω → ι → ℝ) (Q : Ω → κ → ℝ) (q : ℕ)
    (S : Finset ι) (T : Finset κ) (hS : S.Nonempty) (hT : T.Nonempty)
    (bad : ι → κ → Bool)
    (hP : ∀ x, ∀ a ∈ S, 0 ≤ P x a ∧ P x a ≤ 1)
    (hQ : ∀ x, ∀ b ∈ T, 0 ≤ Q x b ∧ Q x b ≤ 1)
    {delta epsilon : ℝ} (hdelta : 0 < delta) (hepsilon : 0 < epsilon)
    (hscore : delta * (S.card : ℝ) * T.card ≤
      ∑ a ∈ S, ∑ b ∈ T, (𝔼 x : Ω, P x a * Q x b) ^ q *
        (1 - (if bad a b then 1 else 0) / epsilon)) :
    ∃ A ⊆ S, ∃ B ⊆ T, A.Nonempty ∧ B.Nonempty ∧
      delta * (S.card : ℝ) ≤ A.card ∧ delta * (T.card : ℝ) ≤ B.card ∧
      (∑ a ∈ A, ∑ b ∈ B, if bad a b then (1 : ℝ) else 0) ≤
        epsilon * (A.card : ℝ) * B.card := by
  obtain ⟨A, hAS, B, hBT, hAB⟩ := exists_rectangle_score_ge P Q q S T
    (fun a b => 1 - (if bad a b then 1 else 0) / epsilon) hP hQ
  have hsum : (∑ a ∈ A, ∑ b ∈ B, (1 - (if bad a b then (1 : ℝ) else 0) / epsilon)) =
      (A.card : ℝ) * B.card -
        (∑ a ∈ A, ∑ b ∈ B, if bad a b then (1 : ℝ) else 0) / epsilon := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
      ← Finset.sum_div]
  have hscoreAB := hscore.trans hAB
  rw [hsum] at hscoreAB
  have hbad0 : 0 ≤ ∑ a ∈ A, ∑ b ∈ B, if bad a b then (1 : ℝ) else 0 := by positivity
  have hprod : delta * (S.card : ℝ) * T.card ≤ (A.card : ℝ) * B.card := by
    linarith [div_nonneg hbad0 hepsilon.le]
  obtain ⟨hA, hB, hAdensity, hBdensity⟩ := rectangle_density_bounds hAS hBT hS hT hdelta hprod
  refine ⟨A, hAS, B, hBT, hA, hB, hAdensity, hBdensity, ?_⟩
  have hdiv : (∑ a ∈ A, ∑ b ∈ B, if bad a b then (1 : ℝ) else 0) / epsilon ≤
      (A.card : ℝ) * B.card := by
    have : 0 ≤ delta * (S.card : ℝ) * T.card := by positivity
    linarith
  have h := (div_le_iff₀ hepsilon).mp hdiv
  nlinarith

theorem exists_dense_rectangle_of_moments
    (P : Ω → ι → ℝ) (Q : Ω → κ → ℝ) (q : ℕ)
    (S : Finset ι) (T : Finset κ) (hS : S.Nonempty) (hT : T.Nonempty)
    (bad : ι → κ → Bool)
    (hP : ∀ x, ∀ a ∈ S, 0 ≤ P x a ∧ P x a ≤ 1)
    (hQ : ∀ x, ∀ b ∈ T, 0 ≤ Q x b ∧ Q x b ≤ 1)
    {mu epsilon : ℝ} (hmu : 0 < mu) (hepsilon : 0 < epsilon)
    (htotal : mu * (S.card : ℝ) * T.card ≤
      ∑ a ∈ S, ∑ b ∈ T, (𝔼 x : Ω, P x a * Q x b) ^ q)
    (hbad : (∑ a ∈ S, ∑ b ∈ T,
      if bad a b then (𝔼 x : Ω, P x a * Q x b) ^ q else 0) ≤
        epsilon / 2 * mu * (S.card : ℝ) * T.card) :
    ∃ A ⊆ S, ∃ B ⊆ T, A.Nonempty ∧ B.Nonempty ∧
      mu / 2 * (S.card : ℝ) ≤ A.card ∧ mu / 2 * (T.card : ℝ) ≤ B.card ∧
      (∑ a ∈ A, ∑ b ∈ B, if bad a b then (1 : ℝ) else 0) ≤
        epsilon * (A.card : ℝ) * B.card := by
  apply exists_dense_rectangle_of_score P Q q S T hS hT bad hP hQ (by positivity) hepsilon
  have hpoint (a : ι) (b : κ) :
      (𝔼 x : Ω, P x a * Q x b) ^ q * (1 - (if bad a b then 1 else 0) / epsilon) =
        (𝔼 x : Ω, P x a * Q x b) ^ q -
          (if bad a b then (𝔼 x : Ω, P x a * Q x b) ^ q else 0) / epsilon := by
    split_ifs <;> ring
  simp_rw [hpoint, Finset.sum_sub_distrib, ← Finset.sum_div]
  have hbad' : (∑ a ∈ S, ∑ b ∈ T,
      if bad a b then (𝔼 x : Ω, P x a * Q x b) ^ q else 0) / epsilon ≤
        mu / 2 * (S.card : ℝ) * T.card := by
    apply (div_le_iff₀ hepsilon).mpr
    nlinarith [hbad]
  linarith

end Erdos3.WeightedSifting

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem exists_dense_sets_of_correlation_moment
    (L U S T K : Finset G) (hL : L.Nonempty) (hU : U.Nonempty)
    (hS : S.Nonempty) (hT : T.Nonempty) (f : G → ℝ)
    {M alpha threshold epsilon : ℝ} (hM : 0 < M) (halpha : 0 < alpha)
    (hthreshold : 0 ≤ threshold) (hepsilon : 0 < epsilon)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M)
    (hsupport : ∀ a ∈ S, ∀ b ∈ T, ∀ x, x ∉ U → f (x + a) * f (x + b) = 0)
    (q : ℕ)
    (hmoment : alpha ^ q ≤ 𝔼 a ∈ S, 𝔼 b ∈ T, correlation L f f (a - b) ^ q)
    (hbad : ∀ a ∈ S, ∀ b ∈ T, a - b ∉ K → correlation L f f (a - b) ≤ threshold)
    (hseparation : threshold ^ q ≤ epsilon / 2 * alpha ^ q) :
    ∃ A ⊆ S, ∃ B ⊆ T, A.Nonempty ∧ B.Nonempty ∧
      (((L.card : ℝ) / ((U.card : ℝ) * M ^ 2) * alpha) ^ q / 2) * S.card ≤ A.card ∧
      (((L.card : ℝ) / ((U.card : ℝ) * M ^ 2) * alpha) ^ q / 2) * T.card ≤ B.card ∧
      1 - epsilon ≤ 𝔼 a ∈ A, 𝔼 b ∈ B, if a - b ∈ K then (1 : ℝ) else 0 := by
  classical
  let : Nonempty U := ⟨⟨hU.choose, hU.choose_spec⟩⟩
  let P : U → G → ℝ := fun x a => f ((x : G) + a) / M
  let beta : ℝ := (L.card : ℝ) / ((U.card : ℝ) * M ^ 2)
  let bad : G → G → Bool := fun a b => decide (a - b ∉ K)
  have hLc : (0 : ℝ) < L.card := by exact_mod_cast hL.card_pos
  have hUc : (0 : ℝ) < U.card := by exact_mod_cast hU.card_pos
  have hSc : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hTc : (0 : ℝ) < T.card := by exact_mod_cast hT.card_pos
  have hbeta : 0 < beta := by dsimp [beta]; positivity
  have hP (x : U) (a : G) : 0 ≤ P x a ∧ P x a ≤ 1 := by
    exact ⟨div_nonneg (hf _).1 hM.le, (div_le_one hM).mpr (hf _).2⟩
  have hkernel (a : G) (ha : a ∈ S) (b : G) (hb : b ∈ T) :
      (𝔼 x : U, P x a * P x b) = beta * correlation L f f (a - b) :=
    expect_local_sample_pair L U hL hU f a b hM (hsupport a ha b hb)
  have hsumcorr : alpha ^ q * (S.card : ℝ) * T.card ≤
      ∑ a ∈ S, ∑ b ∈ T, correlation L f f (a - b) ^ q := by
    simp_rw [Finset.expect_eq_sum_div_card] at hmoment
    rw [← Finset.sum_div, div_div] at hmoment
    have h := (le_div_iff₀ (mul_pos hTc hSc)).mp hmoment
    nlinarith
  have hraw : (∑ a ∈ S, ∑ b ∈ T, (𝔼 x : U, P x a * P x b) ^ q) =
      beta ^ q * ∑ a ∈ S, ∑ b ∈ T, correlation L f f (a - b) ^ q := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    rw [hkernel a ha b hb, mul_pow]
  have htotal : (beta * alpha) ^ q * (S.card : ℝ) * T.card ≤
      ∑ a ∈ S, ∑ b ∈ T, (𝔼 x : U, P x a * P x b) ^ q := by
    rw [hraw]
    calc
      _ = beta ^ q * (alpha ^ q * (S.card : ℝ) * T.card) := by rw [mul_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsumcorr (pow_nonneg hbeta.le q)
  have hbadmoment : (∑ a ∈ S, ∑ b ∈ T,
      if bad a b then (𝔼 x : U, P x a * P x b) ^ q else 0) ≤
        epsilon / 2 * (beta * alpha) ^ q * (S.card : ℝ) * T.card := by
    calc
      _ ≤ ∑ _a ∈ S, ∑ _b ∈ T, (beta * threshold) ^ q := by
        apply Finset.sum_le_sum
        intro a ha
        apply Finset.sum_le_sum
        intro b hb
        by_cases h : bad a b
        · simp only [h, ite_true]
          have hnot : a - b ∉ K := by simpa [bad] using h
          rw [hkernel a ha b hb]
          exact pow_le_pow_left₀
            (mul_nonneg hbeta.le (correlation_nonneg L f f (fun x => (hf x).1) (fun x => (hf x).1) _))
            (mul_le_mul_of_nonneg_left (hbad a ha b hb hnot) hbeta.le) q
        · simp only [h]
          exact pow_nonneg (mul_nonneg hbeta.le hthreshold) q
      _ = beta ^ q * threshold ^ q * (S.card : ℝ) * T.card := by
        simp only [Finset.sum_const, nsmul_eq_mul, mul_pow]
        ring
      _ ≤ beta ^ q * (epsilon / 2 * alpha ^ q) * (S.card : ℝ) * T.card :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hseparation (pow_nonneg hbeta.le q)) hSc.le) hTc.le
      _ = _ := by rw [mul_pow]; ring
  obtain ⟨A, hAS, B, hBT, hA, hB, hAdensity, hBdensity, hbadAB⟩ :=
    WeightedSifting.exists_dense_rectangle_of_moments P P q S T hS hT bad
      (fun x a _ => hP x a) (fun x b _ => hP x b)
      (pow_pos (mul_pos hbeta halpha) q) hepsilon htotal hbadmoment
  refine ⟨A, hAS, B, hBT, hA, hB, hAdensity, hBdensity, ?_⟩
  have hprob := good_pair_expect_ge A B hA hB bad hbadAB
  simpa [bad] using hprob

end Erdos3.LocalConvolution

end

end OAI

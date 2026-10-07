-- Modified for ProveIt: added `import OAI.Compat.*` lines (backported names); see lib/openai-math/README.md.
-- Modified for ProveIt: in shiftTestingSeminorm_le_of_nonneg (empty index case), the closing `simp ...; rfl` became an explicit sSup-of-empty computation (the simp set differs in Mathlib v4.32.0).
import OAI.Combinatorics.Progressions.Estimates.CyclicShortShiftSet
import OAI.Combinatorics.Progressions.Estimates.UnitExpansionCorrelation
import OAI.Combinatorics.Progressions.Geometry.BoxDetectionExponents
import OAI.Compat.BigOperators

namespace OAI

section

namespace Erdos3

theorem exists_large_fixed_choices {G K P : Type*} [Fintype K] [Fintype P]
    (H : Finset G) (hH : H.Nonempty) (rel : G → K → P → Prop)
    (hchoice : ∀ h ∈ H, ∀ k, ∃ p, rel h k p) {R : ℝ}
    (hcount : (Fintype.card P : ℝ) ≤ Real.exp R) :
    ∃ (q : K → P) (S : Finset G), S ⊆ H ∧ S.Nonempty ∧
      Real.exp (-R * Fintype.card K) * H.card ≤ (S.card : ℝ) ∧
      ∀ h ∈ S, ∀ k, rel h k (q k) := by
  classical
  choose choices hchoices using hchoice
  obtain ⟨h0, hh0⟩ := hH
  have hH : H.Nonempty := ⟨h0, hh0⟩
  let code : G → (K → P) := fun h => if hh : h ∈ H then choices h hh else choices h0 hh0
  have hcode (h : G) (hh : h ∈ H) (k : K) : rel h k (code h k) := by
    simpa [code, hh] using hchoices h hh k
  have hcodeCount : (((Set.univ : Set (K → P)).ncard : ℕ) : ℝ) ≤
      Real.exp (R * Fintype.card K) := by
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun, Nat.cast_pow]
    calc
      _ ≤ (Real.exp R) ^ Fintype.card K := pow_le_pow_left₀ (Nat.cast_nonneg _) hcount _
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  obtain ⟨q, _, S, hsub, hSn, hconst, hsize⟩ := exists_exponential_constant_fiber
    H hH code Set.univ Set.finite_univ (fun _ _ => Set.mem_univ _) hcodeCount
  refine ⟨q, S, hsub, hSn, ?_, ?_⟩
  · simpa only [neg_mul] using hsize
  · intro h hh k
    rw [← hconst h hh]
    exact hcode h (hsub hh) k

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

noncomputable def functionCorrelationLinearMap (w : Ω → ℂ) : (Ω → ℂ) →ₗ[ℂ] ℂ where
  toFun v := 𝔼 x, v x * w x
  map_add' v u := by simp [Pi.add_apply, add_mul, Finset.expect_add_distrib]
  map_smul' a v := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply,
      Finset.mul_expect]

noncomputable def functionCorrelationSeminorm (w : Ω → ℂ) : Seminorm ℂ (Ω → ℂ) :=
  (normSeminorm ℂ ℂ).comp (functionCorrelationLinearMap w)

theorem functionCorrelationSeminorm_apply (w v : Ω → ℂ) :
    functionCorrelationSeminorm w v = ‖𝔼 x, v x * w x‖ := rfl

theorem functionCorrelationSeminorm_le (w v : Ω → ℂ) {M : ℝ}
    (hw : ∀ x, ‖w x‖ ≤ M) :
    functionCorrelationSeminorm w v ≤ M * (𝔼 x, ‖v x‖) := by
  rw [functionCorrelationSeminorm_apply, Finset.mul_expect]
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  apply Finset.expect_le_expect
  intro x _
  rw [norm_mul, mul_comm M]
  exact mul_le_mul_of_nonneg_left (hw x) (norm_nonneg _)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def weightedModelError {G I : Type*} [Fintype I]
    (c : I → ℂ) (ea : G → ℝ) (eb : I → G → ℝ) (h : G) : ℝ :=
  ea h + ∑ i, ‖c i‖ * eb i h

theorem weightedModelError_nonneg {G I : Type*} [Fintype I]
    (c : I → ℂ) (ea : G → ℝ) (eb : I → G → ℝ)
    (ha : ∀ h, 0 ≤ ea h) (hb : ∀ i h, 0 ≤ eb i h) (h : G) :
    0 ≤ weightedModelError c ea eb h := by
  exact add_nonneg (ha h) (Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (hb i h)))

theorem weightedModelError_mean_le {G I : Type*} [Fintype G] [Fintype I]
    (c : I → ℂ) (ea : G → ℝ) (eb : I → G → ℝ) {A : ℝ} {B : I → ℝ}
    (ha : (𝔼 h, ea h) ≤ A) (hb : ∀ i, (𝔼 h, eb i h) ≤ B i) :
    (𝔼 h, weightedModelError c ea eb h) ≤ A + ∑ i, ‖c i‖ * B i := by
  simp only [weightedModelError, Finset.expect_add_distrib, Finset.expect_sum_comm,
    ← Finset.mul_expect]
  exact add_le_add ha (Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hb i) (norm_nonneg _)))

theorem exists_large_good_error_set {G : Type*} [Fintype G] [Nonempty G]
    (H : Finset G) (err : G → ℝ) {sigma delta : ℝ} (hsigma : 0 < sigma) (hdelta : 0 < delta)
    (herr : ∀ h, 0 ≤ err h) (hH : sigma * Fintype.card G ≤ (H.card : ℝ))
    (hmean : (𝔼 h, err h) ≤ sigma * delta / 4) :
    ∃ S : Finset G, S ⊆ H ∧ S.Nonempty ∧
      sigma / 2 * Fintype.card G ≤ (S.card : ℝ) ∧ ∀ h ∈ S, err h ≤ delta / 2 := by
  classical
  let bad := H.filter (fun h => delta / 2 < err h)
  have hbadH : bad ⊆ H := Finset.filter_subset _ _
  have hcard : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hsum : (∑ h, err h) ≤ sigma * delta / 4 * Fintype.card G := by
    exact (div_le_iff₀ hcard).mp (by simpa only [Fintype.expect_eq_sum_div_card] using hmean)
  have hbad : (bad.card : ℝ) * (delta / 2) ≤ sigma * delta / 4 * Fintype.card G := by
    calc
      _ = ∑ _h ∈ bad, delta / 2 := by simp
      _ ≤ ∑ h ∈ bad, err h := Finset.sum_le_sum (fun h hh => (Finset.mem_filter.mp hh).2.le)
      _ ≤ ∑ h, err h := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun h _ _ => herr h)
      _ ≤ _ := hsum
  have hbadCard : (bad.card : ℝ) ≤ sigma / 2 * Fintype.card G := by
    apply (mul_le_mul_iff_left₀ (show 0 < delta / 2 by positivity)).mp
    exact hbad.trans_eq (by ring)
  have hgood : sigma / 2 * Fintype.card G ≤ ((H \ bad).card : ℝ) := by
    rw [Finset.cast_card_sdiff hbadH]
    linarith
  have hgoodPos : (0 : ℝ) < (H \ bad).card :=
    (mul_pos (by positivity) hcard).trans_le hgood
  refine ⟨H \ bad, Finset.sdiff_subset, Finset.card_pos.mp (by exact_mod_cast hgoodPos), hgood, ?_⟩
  intro h hh
  by_contra hlarge
  exact (Finset.mem_sdiff.mp hh).2 (Finset.mem_filter.mpr
    ⟨(Finset.mem_sdiff.mp hh).1, lt_of_not_ge hlarge⟩)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_large_fixed_dependent_choices {G K : Type*} {P : K → Type*}
    [Fintype K] [∀ k, Fintype (P k)]
    (H : Finset G) (hH : H.Nonempty) (rel : ∀ (_ : G) (k : K), P k → Prop)
    (hchoice : ∀ h ∈ H, ∀ k, ∃ p, rel h k p) {R : ℝ}
    (hcount : ∀ k, (Fintype.card (P k) : ℝ) ≤ Real.exp R) :
    ∃ (q : ∀ k, P k) (S : Finset G), S ⊆ H ∧ S.Nonempty ∧
      Real.exp (-R * Fintype.card K) * H.card ≤ (S.card : ℝ) ∧
      ∀ h ∈ S, ∀ k, rel h k (q k) := by
  classical
  choose choices hchoices using hchoice
  obtain ⟨h0, hh0⟩ := hH
  have hH : H.Nonempty := ⟨h0, hh0⟩
  let code : G → (∀ k, P k) := fun h => if hh : h ∈ H then choices h hh else choices h0 hh0
  have hcode (h : G) (hh : h ∈ H) (k : K) : rel h k (code h k) := by
    simpa [code, hh] using hchoices h hh k
  have hcodeCount : (((Set.univ : Set (∀ k, P k)).ncard : ℕ) : ℝ) ≤
      Real.exp (R * Fintype.card K) := by
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_pi, Nat.cast_prod]
    calc
      _ ≤ ∏ _k : K, Real.exp R :=
        Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun k _ => hcount k)
      _ = (Real.exp R) ^ Fintype.card K := by simp
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  obtain ⟨q, _, S, hsub, hSn, hconst, hsize⟩ := exists_exponential_constant_fiber
    H hH code Set.univ Set.finite_univ (fun _ _ => Set.mem_univ _) hcodeCount
  refine ⟨q, S, hsub, hSn, ?_, ?_⟩
  · simpa only [neg_mul] using hsize
  · intro h hh k
    rw [← hconst h hh]
    exact hcode h (hsub hh) k

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G ι : Type*} [AddCommGroup G] [Fintype G]

noncomputable def shiftTestSeminormAt (B : G → ℂ) (T : ι → G → ℂ) (h : G) :
    Seminorm ℂ (G → ℂ) :=
  ⨆ i, functionCorrelationSeminorm (fun x => B (x + h) * T i x)

noncomputable def shiftTestingSeminorm (B : G → ℂ) (T : ι → G → ℂ) :
    Seminorm ℂ (G → ℂ) :=
  Seminorm.of (fun v => 𝔼 h, shiftTestSeminormAt B T h v)
    (fun u v => by
      rw [← Finset.expect_add_distrib]
      exact Finset.expect_le_expect (fun h _ => map_add_le_add _ _ _))
    (fun a v => by simp only [map_smul_eq_mul, Finset.mul_expect])

theorem shiftTestSeminormAt_bddAbove (B : G → ℂ) (T : ι → G → ℂ) {M : ℝ}
    (hB : ∀ x, ‖B x‖ ≤ M) (hT : ∀ i x, ‖T i x‖ ≤ 1) (h : G) :
    BddAbove (Set.range fun i => functionCorrelationSeminorm (fun x => B (x + h) * T i x)) := by
  apply Seminorm.bddAbove_range_iff.mpr
  intro v
  refine ⟨M * (𝔼 x, ‖v x‖), ?_⟩
  rintro _ ⟨i, rfl⟩
  apply functionCorrelationSeminorm_le
  intro x
  rw [norm_mul]
  exact ((mul_le_mul_of_nonneg_left (hT i x) (norm_nonneg _)).trans_eq
    (mul_one _)).trans (hB _)

theorem shiftTestSeminormAt_apply (B : G → ℂ) (T : ι → G → ℂ) {M : ℝ}
    (hB : ∀ x, ‖B x‖ ≤ M) (hT : ∀ i x, ‖T i x‖ ≤ 1) (h : G) (v : G → ℂ) :
    shiftTestSeminormAt B T h v = ⨆ i, ‖𝔼 x, v x * (B (x + h) * T i x)‖ := by
  simp only [shiftTestSeminormAt,
    Seminorm.iSup_apply (shiftTestSeminormAt_bddAbove B T hB hT h),
    functionCorrelationSeminorm_apply]

theorem shiftTestingSeminorm_apply (B : G → ℂ) (T : ι → G → ℂ) {M : ℝ}
    (hB : ∀ x, ‖B x‖ ≤ M) (hT : ∀ i x, ‖T i x‖ ≤ 1) (v : G → ℂ) :
    shiftTestingSeminorm B T v =
      𝔼 h, ⨆ i, ‖𝔼 x, v x * (B (x + h) * T i x)‖ := by
  change (𝔼 h, shiftTestSeminormAt B T h v) = _
  simp_rw [shiftTestSeminormAt_apply B T hB hT]

theorem shiftTestingSeminorm_le [Nonempty ι]
    (B : G → ℂ) (T : ι → G → ℂ) {M : ℝ}
    (hB : ∀ x, ‖B x‖ ≤ M) (hT : ∀ i x, ‖T i x‖ ≤ 1) (v : G → ℂ) :
    shiftTestingSeminorm B T v ≤ M * (𝔼 x, ‖v x‖) := by
  rw [shiftTestingSeminorm_apply B T hB hT]
  apply Finset.expect_le Finset.univ_nonempty
  intro h _
  apply ciSup_le
  intro i
  apply functionCorrelationSeminorm_le
  intro x
  rw [norm_mul]
  exact ((mul_le_mul_of_nonneg_left (hT i x) (norm_nonneg _)).trans_eq
    (mul_one _)).trans (hB _)

theorem exists_nearly_maximizing_shift_tests [Nonempty ι]
    (B : G → ℂ) (T : ι → G → ℂ) {M : ℝ}
    (hB : ∀ x, ‖B x‖ ≤ M) (hT : ∀ i x, ‖T i x‖ ≤ 1)
    (v : G → ℂ) {eta : ℝ} (heta : 0 < eta) :
    ∃ t : G → ι, shiftTestingSeminorm B T v - eta <
      𝔼 h, ‖𝔼 x, v x * (B (x + h) * T (t h) x)‖ := by
  have hchoice (h : G) : ∃ i, shiftTestSeminormAt B T h v - eta <
      ‖𝔼 x, v x * (B (x + h) * T i x)‖ := by
    rw [shiftTestSeminormAt_apply B T hB hT]
    exact exists_lt_of_lt_ciSup (sub_lt_self _ heta)
  choose t ht using hchoice
  refine ⟨t, ?_⟩
  change (𝔼 h, shiftTestSeminormAt B T h v) - eta < _
  rw [← Fintype.expect_const (ι := G) eta, ← Finset.expect_sub_distrib]
  exact Finset.expect_lt_expect (fun h _ => (ht h).le)
    ⟨0, Finset.mem_univ _, ht 0⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem shiftTestingSeminorm_le_of_nonneg {G ι : Type*} [AddCommGroup G] [Fintype G]
    (B : G → ℂ) (T : ι → G → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hB : ∀ x, ‖B x‖ ≤ M) (hT : ∀ i x, ‖T i x‖ ≤ 1) (v : G → ℂ) :
    shiftTestingSeminorm B T v ≤ M * (𝔼 x, ‖v x‖) := by
  cases isEmpty_or_nonempty ι with
  | inl h =>
    let := h
    have hz : shiftTestingSeminorm B T v = 0 := by
      have h0 : ∀ hh, shiftTestSeminormAt B T hh = 0 := fun hh => by
        rw [shiftTestSeminormAt, iSup, Set.range_eq_empty, Seminorm.sSup_empty,
          Seminorm.bot_eq_zero]
      change 𝔼 hh, shiftTestSeminormAt B T hh v = 0
      simp [h0]
    rw [hz]
    exact mul_nonneg hM (Finset.expect_nonneg (fun x _ => norm_nonneg (v x)))
  | inr h =>
    let := h
    exact shiftTestingSeminorm_le B T hB hT v

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G ι : Type*} [AddCommGroup G]

def translatedTestFamily (T : ι → G → ℂ) (p : G × ι) (x : G) : ℂ := T p.2 (x + p.1)

theorem translatedTestFamily_norm_le_one (T : ι → G → ℂ)
    (hT : ∀ i x, ‖T i x‖ ≤ 1) (p : G × ι) (x : G) :
    ‖translatedTestFamily T p x‖ ≤ 1 := hT _ _

variable [Fintype G]

theorem correlation_le_shiftTestSeminormAt (B v : G → ℂ) (T : ι → G → ℂ)
    {M : ℝ} (hB : ∀ x, ‖B x‖ ≤ M) (hT : ∀ i x, ‖T i x‖ ≤ 1) (h : G) (i : ι) :
    ‖𝔼 x, v x * (B (x + h) * T i x)‖ ≤ shiftTestSeminormAt B T h v := by
  rw [shiftTestSeminormAt_apply B T hB hT]
  exact le_ciSup (Seminorm.bddAbove_range_iff.mp
    (shiftTestSeminormAt_bddAbove B T hB hT h) v) i

theorem first_model_error_le_shiftTest (B v : G → ℂ) (T : ι → G → ℂ)
    {M : ℝ} (hB : ∀ x, ‖B x‖ ≤ M) (hT : ∀ i x, ‖T i x‖ ≤ 1) (h : G) (i : ι) :
    ‖𝔼 x, T i x * v x * B (x + h)‖ ≤ shiftTestSeminormAt B T h v := by
  have heq : (𝔼 x, T i x * v x * B (x + h)) = 𝔼 x, v x * (B (x + h) * T i x) := by
    apply Finset.expect_congr rfl
    intro x _
    ring
  rw [heq]
  exact correlation_le_shiftTestSeminormAt B v T hB hT h i

theorem second_model_error_le_shiftTest (Q v : G → ℂ) (T : ι → G → ℂ)
    {M : ℝ} (hQ : ∀ x, ‖Q x‖ ≤ M) (hT : ∀ i x, ‖T i x‖ ≤ 1) (h : G) (i : ι) :
    ‖𝔼 x, T i x * Q x * v (x + h)‖ ≤
      shiftTestSeminormAt Q (translatedTestFamily T) (-h) v := by
  have heq : (𝔼 x, T i x * Q x * v (x + h)) =
      𝔼 y, v y * (Q (y + -h) * translatedTestFamily T (-h, i) y) := by
    apply Fintype.expect_equiv (Equiv.addRight h)
    intro x
    simp only [Equiv.coe_addRight, translatedTestFamily, add_neg_cancel_right]
    ring
  rw [heq]
  exact correlation_le_shiftTestSeminormAt Q v (translatedTestFamily T) hQ
    (translatedTestFamily_norm_le_one T hT) (-h) (-h, i)

theorem mean_negated_shiftTest (B v : G → ℂ) (T : ι → G → ℂ) :
    (𝔼 h, shiftTestSeminormAt B T (-h) v) = shiftTestingSeminorm B T v := by
  change (𝔼 h, shiftTestSeminormAt B T (-h) v) = 𝔼 h, shiftTestSeminormAt B T h v
  apply Fintype.expect_equiv (Equiv.neg G)
  intro h
  rfl

theorem weighted_shiftTest_model_error_mean {I : Type*} [Fintype I]
    (b ea : G → ℂ) (Q eb : I → G → ℂ) (c : I → ℂ) (T : ι → G → ℂ) :
    (𝔼 h, weightedModelError c (fun h => shiftTestSeminormAt b T h ea)
      (fun i h => shiftTestSeminormAt (Q i) (translatedTestFamily T) (-h) (eb i)) h) =
      shiftTestingSeminorm b T ea + ∑ i, ‖c i‖ * shiftTestingSeminorm (Q i) (translatedTestFamily T) (eb i) := by
  simp only [weightedModelError, Finset.expect_add_distrib, Finset.expect_sum_comm,
    ← Finset.mul_expect, mean_negated_shiftTest]
  rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_model_partner {G I : Type*} {J : I → Type*}
    [AddCommGroup G] [Fintype G] [Fintype I] [∀ i, Fintype (J i)]
    (a b ea U : G → ℂ) (Q : I → G → ℂ) (R : ∀ i, J i → G → ℂ)
    (eb : I → G → ℂ) (c : I → ℂ) (d : ∀ i, J i → ℂ)
    (ha : ∀ n, a n = (∑ i, c i * Q i n) + ea n)
    (hb : ∀ i n, b n = (∑ j, d i j * R i j n) + eb i n)
    (h : G) {A C D delta : ℝ} {B : I → ℝ}
    (hdelta : 0 < delta) (hC : 0 < C) (hD : 0 < D)
    (hc : (∑ i, ‖c i‖) ≤ C) (hd : ∀ i, (∑ j, ‖d i j‖) ≤ D)
    (hfirst : ‖𝔼 n, U n * ea n * b (n + h)‖ ≤ A)
    (hsecond : ∀ i, ‖𝔼 n, U n * Q i n * eb i (n + h)‖ ≤ B i)
    (herror : A + ∑ i, ‖c i‖ * B i ≤ delta / 2)
    (hcorr : delta ≤ ‖𝔼 n, U n * a n * b (n + h)‖) :
    ∃ i j, (delta / 2) / (C * D) ≤ ‖𝔼 n, U n * Q i n * R i j (n + h)‖ := by
  apply exists_large_weighted_pair c d
    (fun i j => 𝔼 n, U n * Q i n * R i j (n + h)) (by positivity) hC hD hc hd
  have herr := (two_site_model_error_bound a b ea U Q R eb c d ha hb h hfirst hsecond).trans herror
  have htri := norm_add_le
    ((𝔼 n, U n * a n * b (n + h)) -
      (∑ i, ∑ j, (c i * d i j) * (𝔼 n, U n * Q i n * R i j (n + h))))
    (∑ i, ∑ j, (c i * d i j) * (𝔼 n, U n * Q i n * R i j (n + h)))
  rw [sub_add_cancel] at htri
  linarith

theorem exists_fixed_model_partners {G I K : Type*} {J : I → Type*}
    [AddCommGroup G] [Fintype G] [Fintype I] [∀ i, Fintype (J i)] [Fintype K]
    (H : Finset G) (a b ea : G → ℂ) (U : G → K → G → ℂ)
    (Q : I → G → ℂ) (R : ∀ i, J i → G → ℂ)
    (eb : I → G → ℂ) (c : I → ℂ) (d : ∀ i, J i → ℂ)
    (ha : ∀ n, a n = (∑ i, c i * Q i n) + ea n)
    (hb : ∀ i n, b n = (∑ j, d i j * R i j n) + eb i n)
    (A : G → ℝ) (B : I → G → ℝ) {C D delta sigma budget : ℝ}
    (hdelta : 0 < delta) (hsigma : 0 < sigma) (hC : 0 < C) (hD : 0 < D)
    (hc : (∑ i, ‖c i‖) ≤ C) (hd : ∀ i, (∑ j, ‖d i j‖) ≤ D)
    (hA : ∀ h, 0 ≤ A h) (hB : ∀ i h, 0 ≤ B i h)
    (hfirst : ∀ h ∈ H, ∀ k, ‖𝔼 n, U h k n * ea n * b (n + h)‖ ≤ A h)
    (hsecond : ∀ h ∈ H, ∀ k i, ‖𝔼 n, U h k n * Q i n * eb i (n + h)‖ ≤ B i h)
    (hmean : (𝔼 h, A h) + ∑ i, ‖c i‖ * (𝔼 h, B i h) ≤ sigma * delta / 4)
    (hH : sigma * Fintype.card G ≤ (H.card : ℝ))
    (hcorr : ∀ h ∈ H, ∀ k, delta ≤ ‖𝔼 n, U h k n * a n * b (n + h)‖)
    (hcount : (Fintype.card (Sigma J) : ℝ) ≤ Real.exp budget) :
    ∃ (q : K → Sigma J) (S : Finset G), S ⊆ H ∧ S.Nonempty ∧
      Real.exp (-budget * Fintype.card K) * (sigma / 2 * Fintype.card G) ≤ (S.card : ℝ) ∧
      ∀ h ∈ S, ∀ k,
        (delta / 2) / (C * D) ≤ ‖𝔼 n, U h k n * Q (q k).1 n * R (q k).1 (q k).2 (n + h)‖ := by
  have herrMean : (𝔼 h, weightedModelError c A B h) ≤ sigma * delta / 4 :=
    (weightedModelError_mean_le c A B le_rfl (fun _ => le_rfl)).trans hmean
  obtain ⟨H', hsub, hH'n, hH'size, hgood⟩ := exists_large_good_error_set H
    (weightedModelError c A B) hsigma hdelta (weightedModelError_nonneg c A B hA hB) hH herrMean
  let rel : G → K → Sigma J → Prop := fun h k p =>
    (delta / 2) / (C * D) ≤ ‖𝔼 n, U h k n * Q p.1 n * R p.1 p.2 (n + h)‖
  have hchoice : ∀ h ∈ H', ∀ k, ∃ p, rel h k p := by
    intro h hh k
    obtain ⟨i, j, hij⟩ := exists_model_partner a b ea (U h k) Q R eb c d ha hb h
      hdelta hC hD hc hd (hfirst h (hsub hh) k) (hsecond h (hsub hh) k)
      (hgood h hh) (hcorr h (hsub hh) k)
    exact ⟨⟨i, j⟩, hij⟩
  obtain ⟨q, S, hSH', hSn, hsize, hfixed⟩ :=
    exists_large_fixed_choices H' hH'n rel hchoice hcount
  refine ⟨q, S, fun h hh => hsub (hSH' hh), hSn, ?_, hfixed⟩
  exact (mul_le_mul_of_nonneg_left hH'size (Real.exp_pos _).le).trans hsize

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_fixed_partners_of_shift_models {G I K ι : Type*} {J : I → Type*}
    [AddCommGroup G] [Fintype G] [Fintype I] [∀ i, Fintype (J i)] [Fintype K]
    (H : Finset G) (a b ea : G → ℂ) (T : ι → G → ℂ) (u : G → K → ι)
    (Q : I → G → ℂ) (R : ∀ i, J i → G → ℂ)
    (eb : I → G → ℂ) (c : I → ℂ) (d : ∀ i, J i → ℂ)
    (ha : ∀ n, a n = (∑ i, c i * Q i n) + ea n)
    (hb : ∀ i n, b n = (∑ j, d i j * R i j n) + eb i n)
    {C D delta sigma budget M : ℝ}
    (hdelta : 0 < delta) (hsigma : 0 < sigma) (hC : 0 < C) (hD : 0 < D)
    (hc : (∑ i, ‖c i‖) ≤ C) (hd : ∀ i, (∑ j, ‖d i j‖) ≤ D)
    (hT : ∀ t n, ‖T t n‖ ≤ 1) (hbcap : ∀ n, ‖b n‖ ≤ M)
    (hQ : ∀ i n, ‖Q i n‖ ≤ 1)
    (herror : shiftTestingSeminorm b T ea +
      ∑ i, ‖c i‖ * shiftTestingSeminorm (Q i) (translatedTestFamily T) (eb i) ≤ sigma * delta / 4)
    (hH : sigma * Fintype.card G ≤ (H.card : ℝ))
    (hcorr : ∀ h ∈ H, ∀ k, delta ≤ ‖𝔼 n, T (u h k) n * a n * b (n + h)‖)
    (hcount : (Fintype.card (Sigma J) : ℝ) ≤ Real.exp budget) :
    ∃ (q : K → Sigma J) (S : Finset G), S ⊆ H ∧ S.Nonempty ∧
      Real.exp (-budget * Fintype.card K) * (sigma / 2 * Fintype.card G) ≤ (S.card : ℝ) ∧
      ∀ h ∈ S, ∀ k,
        (delta / 2) / (C * D) ≤
          ‖𝔼 n, T (u h k) n * Q (q k).1 n * R (q k).1 (q k).2 (n + h)‖ := by
  apply exists_fixed_model_partners H a b ea (fun h k => T (u h k)) Q R eb c d ha hb
    (fun h => shiftTestSeminormAt b T h ea)
    (fun i h => shiftTestSeminormAt (Q i) (translatedTestFamily T) (-h) (eb i))
    hdelta hsigma hC hD hc hd
  · intro h
    exact apply_nonneg _ _
  · intro i h
    exact apply_nonneg _ _
  · intro h _ k
    exact first_model_error_le_shiftTest b ea T hbcap hT h (u h k)
  · intro h _ k i
    exact second_model_error_le_shiftTest (Q i) (eb i) T (hQ i) hT h (u h k)
  · change shiftTestingSeminorm b T ea +
      ∑ i, ‖c i‖ * (𝔼 h, shiftTestSeminormAt (Q i) (translatedTestFamily T) (-h) (eb i)) ≤ _
    simpa only [mean_negated_shiftTest] using herror
  · exact hH
  · exact hcorr
  · exact hcount

theorem two_stage_model_precision_bound {G I ι : Type*}
    [AddCommGroup G] [Fintype G] [Fintype I]
    (b ea : G → ℂ) (Q eb : I → G → ℂ) (c : I → ℂ) (T : ι → G → ℂ)
    {C delta sigma : ℝ} (hC : 0 < C) (hdelta : 0 ≤ delta) (hsigma : 0 ≤ sigma)
    (hc : (∑ i, ‖c i‖) ≤ C)
    (ha : shiftTestingSeminorm b T ea ≤ sigma * delta / 8)
    (hb : ∀ i, shiftTestingSeminorm (Q i) (translatedTestFamily T) (eb i) ≤
      sigma * delta / (8 * C)) :
    shiftTestingSeminorm b T ea +
      ∑ i, ‖c i‖ * shiftTestingSeminorm (Q i) (translatedTestFamily T) (eb i) ≤ sigma * delta / 4 := by
  have hsecond : (∑ i, ‖c i‖ * shiftTestingSeminorm (Q i) (translatedTestFamily T) (eb i)) ≤
      sigma * delta / 8 := by
    calc
      _ ≤ ∑ i, ‖c i‖ * (sigma * delta / (8 * C)) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hb i) (norm_nonneg _))
      _ = (∑ i, ‖c i‖) * (sigma * delta / (8 * C)) := (Finset.sum_mul _ _ _).symm
      _ ≤ C * (sigma * delta / (8 * C)) := mul_le_mul_of_nonneg_right hc (by positivity)
      _ = _ := by field_simp
  linarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exp_sub_two_le_quarter_exp (x : ℝ) : Real.exp (x - 2) ≤ Real.exp x / 4 := by
  have hfirst := exp_sub_one_le_half_exp (x - 1)
  have hsecond := exp_sub_one_le_half_exp x
  rw [show x - 1 - 1 = x - 2 by ring] at hfirst
  linarith

theorem exists_fixed_partners_power {G I K ι : Type*} {J : I → Type*}
    [AddCommGroup G] [Fintype G] [Fintype I] [∀ i, Fintype (J i)] [Fintype K]
    (H : Finset G) (a b ea : G → ℂ) (T : ι → G → ℂ) (u : G → K → ι)
    (Q : I → G → ℂ) (R : ∀ i, J i → G → ℂ)
    (eb : I → G → ℂ) (c : I → ℂ) (d : ∀ i, J i → ℂ)
    (ha : ∀ n, a n = (∑ i, c i * Q i n) + ea n)
    (hb : ∀ i n, b n = (∑ j, d i j * R i j n) + eb i n)
    {p q M : ℝ} (hp : 0 ≤ p) (hqp : q ≤ p) (hK : (Fintype.card K : ℝ) ≤ p)
    (hc : (∑ i, ‖c i‖) ≤ Real.exp p) (hd : ∀ i, (∑ j, ‖d i j‖) ≤ Real.exp p)
    (hT : ∀ t n, ‖T t n‖ ≤ 1) (hbcap : ∀ n, ‖b n‖ ≤ M)
    (hQ : ∀ i n, ‖Q i n‖ ≤ 1)
    (herror : shiftTestingSeminorm b T ea +
      ∑ i, ‖c i‖ * shiftTestingSeminorm (Q i) (translatedTestFamily T) (eb i) ≤ Real.exp (-(2 * q + 2)))
    (hH : Real.exp (-q) * Fintype.card G ≤ (H.card : ℝ))
    (hcorr : ∀ h ∈ H, ∀ k, Real.exp (-q) ≤ ‖𝔼 n, T (u h k) n * a n * b (n + h)‖)
    (hcount : (Fintype.card (Sigma J) : ℝ) ≤ Real.exp p) :
    ∃ (q : K → Sigma J) (S : Finset G), S ⊆ H ∧ S.Nonempty ∧
      Real.exp (-((p + 2) ^ 2)) * Fintype.card G ≤ (S.card : ℝ) ∧
      ∀ h ∈ S, ∀ k, Real.exp (-((p + 2) ^ 2)) ≤
        ‖𝔼 n, T (u h k) n * Q (q k).1 n * R (q k).1 (q k).2 (n + h)‖ := by
  have hquarter : Real.exp (-(2 * q + 2)) ≤ Real.exp (-q) * Real.exp (-q) / 4 := by
    rw [← Real.exp_add]
    convert exp_sub_two_le_quarter_exp (-q + -q) using 1
    congr 1
    ring
  obtain ⟨choice, S, hsub, hSn, hsize, hbias⟩ := exists_fixed_partners_of_shift_models
    H a b ea T u Q R eb c d ha hb (Real.exp_pos _) (Real.exp_pos _)
    (Real.exp_pos _) (Real.exp_pos _) hc hd hT hbcap hQ (herror.trans hquarter) hH hcorr hcount
  have hsize' : Real.exp (-((p + 2) ^ 2)) ≤
      Real.exp (-p * Fintype.card K) * (Real.exp (-q) / 2) := by
    calc
      _ ≤ Real.exp ((-p * Fintype.card K + -q) - 1) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left hK hp, sq_nonneg p]
      _ ≤ Real.exp (-p * Fintype.card K + -q) / 2 := exp_sub_one_le_half_exp _
      _ = _ := by rw [Real.exp_add]; ring
  have hbias' : Real.exp (-((p + 2) ^ 2)) ≤
      (Real.exp (-q) / 2) / (Real.exp p * Real.exp p) := by
    apply (le_div_iff₀ (mul_pos (Real.exp_pos _) (Real.exp_pos _))).mpr
    calc
      _ = Real.exp (-((p + 2) ^ 2) + (p + p)) := by rw [← Real.exp_add, ← Real.exp_add]
      _ ≤ Real.exp (-q - 1) := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg p])
      _ ≤ Real.exp (-q) / 2 := exp_sub_one_le_half_exp _
  refine ⟨choice, S, hsub, hSn, ?_, fun h hh k => hbias'.trans (hbias h hh k)⟩
  exact (mul_le_mul_of_nonneg_right hsize' (Nat.cast_nonneg _)).trans
    (by simpa only [mul_assoc] using hsize)

end Erdos3

end

end OAI

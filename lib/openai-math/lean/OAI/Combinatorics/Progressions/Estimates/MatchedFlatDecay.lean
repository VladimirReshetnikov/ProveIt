import OAI.Combinatorics.Progressions.Estimates.FiniteCellRefinement
import OAI.Combinatorics.Progressions.Probability.SiftingDensityBudget

namespace OAI

section

namespace Erdos3

noncomputable def flatComparisonDelta (epsilon : ℝ) : ℝ := epsilon / (4 * (2 + epsilon))

theorem flatComparisonDelta_spec {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    0 < flatComparisonDelta epsilon ∧ flatComparisonDelta epsilon ≤ 1 / 4 ∧
      1 + 2 * flatComparisonDelta epsilon ≤
        (1 + epsilon) * (1 - 2 * flatComparisonDelta epsilon) := by
  have hden : 0 < 4 * (2 + epsilon) := by positivity
  have hprod : flatComparisonDelta epsilon * (4 * (2 + epsilon)) = epsilon :=
    div_mul_cancel₀ _ hden.ne'
  refine ⟨div_pos hepsilon hden, ?_, ?_⟩
  · unfold flatComparisonDelta
    apply (div_le_iff₀ hden).mpr
    linarith
  · nlinarith

theorem exp_mul_half_pow_le {a b : ℝ} (q : ℕ)
    (hq : a + b ≤ (q : ℝ) * Real.log 2) :
    Real.exp a * (1 / 2 : ℝ) ^ q ≤ Real.exp (-b) := by
  have hhalf : (1 / 2 : ℝ) = Real.exp (-Real.log 2) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [hhalf, ← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem flat_exception_error_le {A B D p W M : ℝ}
    (hp : 1 ≤ p) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hWcap : W ≤ Real.exp (A * p)) (hMcap : M ≤ Real.exp (B * p))
    (q : ℕ) (hq : (A + B + D + Real.log 3) * p ≤ (q : ℝ) * Real.log 2) :
    W * (M + 2) * (1 / 2 : ℝ) ^ q ≤ Real.exp (-(D * p)) := by
  have hp0 : 0 ≤ p := by linarith
  have hone : 1 ≤ Real.exp (B * p) := Real.one_le_exp_iff.mpr (mul_nonneg hB hp0)
  have hMtwo : M + 2 ≤ 3 * Real.exp (B * p) := by linarith
  have hproduct : W * (M + 2) ≤ 3 * Real.exp ((A + B) * p) := by
    calc
      _ ≤ Real.exp (A * p) * (3 * Real.exp (B * p)) :=
        mul_le_mul hWcap hMtwo (by positivity) (Real.exp_nonneg _)
      _ = _ := by rw [add_mul, Real.exp_add]; ring
  have hlog3 : 0 ≤ Real.log 3 := (Real.log_pos (by norm_num : (1 : ℝ) < 3)).le
  have hthreshold : Real.log 3 + (A + B) * p + D * p ≤ (q : ℝ) * Real.log 2 := by
    have hlog := mul_le_mul_of_nonneg_left hp hlog3
    nlinarith
  calc
    _ ≤ (3 * Real.exp ((A + B) * p)) * (1 / 2 : ℝ) ^ q :=
      mul_le_mul_of_nonneg_right hproduct (by positivity)
    _ = Real.exp (Real.log 3 + (A + B) * p) * (1 / 2 : ℝ) ^ q := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    _ ≤ _ := exp_mul_half_pow_le q hthreshold

theorem exists_flat_moment_slope {A B D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ p : ℝ, 1 ≤ p → ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ C * p ∧
      (A + B + D + Real.log 3) * p ≤ ((2 * m : ℕ) : ℝ) * Real.log 2 := by
  let R : ℝ := (A + B + D + Real.log 3) / (2 * Real.log 2)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hR : 0 ≤ R := div_nonneg (by positivity) (by positivity)
  have hRprod : R * (2 * Real.log 2) = A + B + D + Real.log 3 :=
    div_mul_cancel₀ _ (by positivity)
  refine ⟨R + 2, by linarith, ?_⟩
  intro p hp
  let m : ℕ := ⌈(R + 1) * p⌉₊
  have hp0 : 0 ≤ p := by linarith
  have hlow : (R + 1) * p ≤ (m : ℝ) := Nat.le_ceil _
  have hhigh : (m : ℝ) < (R + 1) * p + 1 := Nat.ceil_lt_add_one (by positivity)
  have hmreal : 0 < (m : ℝ) := by nlinarith [mul_nonneg hR hp0]
  have hm : 0 < m := by exact_mod_cast hmreal
  refine ⟨m, hm, by nlinarith, ?_⟩
  have hmul := mul_le_mul_of_nonneg_right hlow (show 0 ≤ 2 * Real.log 2 by positivity)
  have heq : (R + 1) * p * (2 * Real.log 2) =
      (A + B + D + Real.log 3) * p + p * (2 * Real.log 2) := by
    calc
      _ = R * (2 * Real.log 2) * p + p * (2 * Real.log 2) := by ring
      _ = _ := by rw [hRprod]
  rw [heq] at hmul
  push_cast
  nlinarith [mul_nonneg hp0 hlog2.le]

end Erdos3

end

section

namespace Erdos3

theorem exp_extra_decay_le_half {D p : ℝ} (hp : 1 ≤ p) :
    Real.exp (-((D + 1) * p)) ≤ Real.exp (-(D * p)) / 2 := by
  have htwo : (2 : ℝ) ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
  calc
    _ = Real.exp (-(D * p)) / Real.exp p := by
      rw [← Real.exp_sub]
      congr 1
      ring
    _ ≤ _ := div_le_div_of_nonneg_left (Real.exp_nonneg _) (by norm_num) htwo

theorem flat_total_error_le_exp {A B D p W M delta eta : ℝ}
    (hp : 1 ≤ p) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hWcap : W ≤ Real.exp (A * p)) (hMcap : M ≤ Real.exp (B * p))
    (hdelta : 0 ≤ delta) (hdelta2 : delta ≤ 1 / 2)
    (heta : eta ≤ Real.exp (-(D * p)) / 4)
    (q : ℕ) (hq : (A + B + (D + 1) + Real.log 3) * p ≤ (q : ℝ) * Real.log 2) :
    (1 + 2 * delta) * eta + W * (M + 2) * (1 / 2 : ℝ) ^ q ≤ Real.exp (-(D * p)) := by
  have hexception := (flat_exception_error_le hp hB hM hWcap hMcap q hq).trans
    (exp_extra_decay_le_half (D := D) hp)
  have hmean := mul_le_mul_of_nonneg_left heta (show 0 ≤ 1 + 2 * delta by positivity)
  have hsmall := mul_le_mul_of_nonneg_right hdelta2 (Real.exp_nonneg (-(D * p)))
  nlinarith

end Erdos3

end

section

namespace Erdos3.LocalConvolution

theorem unbalanced_error_control {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    0 < c / 64 ∧ c / 64 ≤ 1 ∧
      1 + c / 8 ≤ (1 + c / 4) * (1 - c / 64 - c / 64) ∧
      1 + c / 16 ≤ (1 + c / 4) * (1 - c / 64 - c / 64) - c / 64 - c / 64 := by
  have hquad : 0 ≤ c * (1 - c) := mul_nonneg hc.le (sub_nonneg.mpr hc1)
  constructor
  · positivity
  constructor
  · linarith
  constructor <;> nlinarith

theorem exists_unbalanced_moment_threshold {c : ℝ} (hc : 0 < c) :
    ∃ m₀ : ℕ, 0 < m₀ ∧ ∀ m ≥ m₀, ∀ m' ≥ m,
      (1 + c / 4) ^ (2 * m') ≤ (c / 64) / 2 * (1 + c / 2) ^ (2 * m') := by
  obtain ⟨q₀, hq₀⟩ := exists_moment_separation
    (show 0 < 1 + c / 2 by linarith) (show 0 ≤ 1 + c / 4 by linarith)
    (show 1 + c / 4 < 1 + c / 2 by linarith) (show 0 < c / 64 by positivity)
  refine ⟨q₀ + 1, by omega, ?_⟩
  intro m hm m' hm'
  exact hq₀ (2 * m') (by omega)

end Erdos3.LocalConvolution

end

section

namespace Erdos3

theorem exists_joint_moment_orders {A B D c : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hD : 0 ≤ D) (hc : 0 < c) (R : ℕ) (hR : 0 < R) :
    ∃ C H : ℝ, 1 ≤ C ∧ 0 ≤ H ∧ ∀ p : ℝ, 1 ≤ p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ C * p ∧
        (A + B + D + Real.log 3) * p ≤ ((2 * m : ℕ) : ℝ) * Real.log 2 ∧
        ∀ m' : ℕ, m ≤ m' → m' ≤ R * m →
          ((2 * m' : ℕ) : ℝ) ≤ H * p ∧
          (1 + c / 4) ^ (2 * m') ≤ (c / 64) / 2 * (1 + c / 2) ^ (2 * m') := by
  obtain ⟨C₀, hC₀, hflat⟩ := exists_flat_moment_slope hA hB hD
  obtain ⟨m₀, _, hsep⟩ := LocalConvolution.exists_unbalanced_moment_threshold hc
  let C := C₀ + (m₀ : ℝ)
  let H := 2 * (R : ℝ) * C
  have hC : 1 ≤ C := by
    dsimp [C]
    have hm₀ : (0 : ℝ) ≤ m₀ := Nat.cast_nonneg m₀
    linarith
  have hH : 0 ≤ H := by dsimp [H]; positivity
  refine ⟨C, H, hC, hH, ?_⟩
  intro p hp
  obtain ⟨m₁, hm₁, hm₁C, horder⟩ := hflat p hp
  let m := m₁ + m₀
  have hm : 0 < m := by dsimp [m]; omega
  have hmC : (m : ℝ) ≤ C * p := by
    have hmul := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg m₀ : (0 : ℝ) ≤ m₀)
    dsimp [m, C]
    push_cast
    nlinarith
  refine ⟨m, hm, hmC, ?_, ?_⟩
  · apply horder.trans
    apply mul_le_mul_of_nonneg_right _ (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
    exact_mod_cast (show 2 * m₁ ≤ 2 * m by dsimp [m]; omega)
  · intro m' hmm' hm'R
    refine ⟨?_, hsep m (by dsimp [m]; omega) m' hmm'⟩
    have hm'Rreal : (m' : ℝ) ≤ (R : ℝ) * m := by exact_mod_cast hm'R
    have hmul := mul_le_mul_of_nonneg_left hmC (Nat.cast_nonneg R : (0 : ℝ) ≤ R)
    dsimp [H]
    push_cast
    nlinarith

end Erdos3

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem matched_flat_integral_decay
    (L S : Finset G) (A B f g : G → ℝ) {u v : ℝ} (hu : 0 < u) (hv : 0 < v)
    (hu1 : u ≤ 1) (hv1 : v ≤ 1) {q : ℕ} (hq : 0 < q)
    {epsilon delta W M eta a b D p : ℝ}
    (hW : 0 ≤ W) (hM : 0 ≤ M) (hepsilon : 0 ≤ epsilon)
    (hdelta : 0 < delta) (hdelta2 : delta ≤ 1 / 2)
    (hcoeff : 1 + 2 * delta ≤ (1 + epsilon) * (1 - 2 * delta))
    (hp : 1 ≤ p) (hb : 0 ≤ b) (hWcap : W ≤ Real.exp (a * p)) (hMcap : M ≤ Real.exp (b * p))
    (heta : eta ≤ Real.exp (-(D * p)) / 4)
    (horder : (a + b + (D + 1) + Real.log 3) * p ≤ (q : ℝ) * Real.log 2)
    (hA : ∀ x, 0 ≤ A x ∧ A x ≤ W) (hB : ∀ x, 0 ≤ B x ∧ B x ≤ W)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) (hgcap : ∀ x, g x / v ≤ M)
    (hfsupport : ∀ x, x ∉ L → f x = 0) (hfmean : (𝔼 x ∈ L, f x) = u)
    (hflat : LocalConvolution.sumLp S
      (fun x => LocalConvolution.convolution L (fun y => f y / u) (fun y => g y / v) x - 1) q ≤ delta)
    (hmean : (𝔼 s ∈ S, 𝔼 t ∈ S, (A (s + t) - B (s + t))) ≤ eta) :
    matchedIntegral L S (fun x => A x - (1 + epsilon) * B x) f g ≤
      Real.exp (-(D * p)) * (u * v) ^ (1 / 4 : ℝ) := by
  have hbase := matched_flat_integral_le_normalized L S A B f g hu hv hq hW hM hepsilon
    hdelta hdelta2 hcoeff hA hB hf hg hgcap hfsupport hfmean hflat hmean
  have herr := flat_total_error_le_exp hp hb hM hWcap hMcap hdelta.le hdelta2 heta q horder
  have hroot : u * v ≤ (u * v) ^ (1 / 4 : ℝ) :=
    Real.self_le_rpow_of_le_one (mul_nonneg hu.le hv.le)
      ((mul_le_mul hu1 hv1 hv.le (by norm_num)).trans_eq (one_mul 1)) (by norm_num)
  calc
    _ ≤ (u * v) * Real.exp (-(D * p)) :=
      hbase.trans (mul_le_mul_of_nonneg_left herr (mul_nonneg hu.le hv.le))
    _ ≤ (u * v) ^ (1 / 4 : ℝ) * Real.exp (-(D * p)) :=
      mul_le_mul_of_nonneg_right hroot (Real.exp_nonneg _)
    _ = _ := mul_comm _ _

end Erdos3.CellRefinement

end

end OAI

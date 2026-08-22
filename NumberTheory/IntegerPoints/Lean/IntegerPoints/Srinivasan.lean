import IntegerPoints.ExponentialSums
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.IntermediateValue

/-!
# Srinivasan's optimisation lemma (Zhai–Cao, Lemma 8)

We prove `zhaiCao_lemma8`.  Write `F(q) = ∑ A_i q^{a_i}` (increasing) and
`G(q) = ∑ B_j q^{-b_j}` (decreasing).  If `G(Q₁) ≤ F(Q₁)` take `q = Q₁`; if
`F(Q₂) ≤ G(Q₂)` take `q = Q₂`; otherwise the intermediate value theorem gives
`q ∈ [Q₁, Q₂]` with `F(q) = G(q) =: S`.  In the last case some
`A_i q^{a_i} ≥ S/m` and some `B_j q^{-b_j} ≥ S/n`, whence
`(A_i^{b_j} B_j^{a_i})^{1/(a_i+b_j)} ≥ S / max(m, n)`, and
`2 max(m, n) ≤ 2^{m+n}`.
-/

open Finset Real Set

namespace LeanProofs.IntegerPoints

/-- `2 max(m, n) ≤ 2^{m+n}` for `m, n ≥ 1`. -/
theorem two_mul_max_le_two_pow {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    2 * max m n ≤ 2 ^ (m + n) := by
  have h1 : max m n < 2 ^ max m n := Nat.lt_two_pow_self
  have h2 : 2 ^ max m n ≤ 2 ^ (m + n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : 2 * 2 ^ (m + n - 1) = 2 ^ (m + n) := by
    rw [← pow_succ']
    congr 1
    omega
  omega

/-- **Zhai–Cao, Lemma 8** (Srinivasan). -/
theorem zhaiCao_lemma8_holds : zhaiCao_lemma8 := by
  intro m n A a B b Q₁ Q₂ hA ha hB hb hQ1 hQ12
  -- the three sums of the right-hand side
  set R₁ : ℝ := ∑ i, ∑ j, (A i ^ b j * B j ^ a i) ^ (1 / (a i + b j)) with hR₁
  set R₂ : ℝ := ∑ i, A i * Q₁ ^ a i with hR₂
  set R₃ : ℝ := ∑ j, B j * Q₂ ^ (-b j) with hR₃
  have hR₁0 : 0 ≤ R₁ := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    Real.rpow_nonneg (mul_nonneg (Real.rpow_nonneg (hA i).le _) (Real.rpow_nonneg (hB j).le _)) _
  have hR₂0 : 0 ≤ R₂ := Finset.sum_nonneg fun i _ =>
    mul_nonneg (hA i).le (Real.rpow_nonneg hQ1.le _)
  have hR₃0 : 0 ≤ R₃ := Finset.sum_nonneg fun j _ =>
    mul_nonneg (hB j).le (Real.rpow_nonneg (by linarith) _)
  have hR0 : 0 ≤ R₁ + R₂ + R₃ := by linarith
  set F : ℝ → ℝ := fun q => ∑ i, A i * q ^ a i with hF
  set G : ℝ → ℝ := fun q => ∑ j, B j * q ^ (-b j) with hG
  have hFnn : ∀ q, 0 < q → 0 ≤ F q := fun q hq =>
    Finset.sum_nonneg fun i _ => mul_nonneg (hA i).le (Real.rpow_nonneg hq.le _)
  have hGnn : ∀ q, 0 < q → 0 ≤ G q := fun q hq =>
    Finset.sum_nonneg fun j _ => mul_nonneg (hB j).le (Real.rpow_nonneg hq.le _)
  -- `2 X ≤ 2^{m+n} R` for a nonnegative part `X` of `R`, unless everything vanishes
  have two_le : ∀ X : ℝ, 0 ≤ X → X ≤ R₁ + R₂ + R₃ → (m + n = 0 → X = 0) →
      2 * X ≤ 2 ^ (m + n) * (R₁ + R₂ + R₃) := by
    intro X hX hXR h0
    rcases Nat.eq_zero_or_pos (m + n) with h | h
    · rw [h0 h, mul_zero]
      exact mul_nonneg (by positivity) hR0
    · have h2 : (2 : ℝ) ≤ 2 ^ (m + n) := by
        calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (m + n) := pow_le_pow_right₀ (by norm_num) h
      calc 2 * X ≤ 2 ^ (m + n) * X := mul_le_mul_of_nonneg_right h2 hX
        _ ≤ 2 ^ (m + n) * (R₁ + R₂ + R₃) := mul_le_mul_of_nonneg_left hXR (by positivity)
  by_cases h1 : G Q₁ ≤ F Q₁
  · refine ⟨Q₁, le_rfl, hQ12, ?_⟩
    have hX : F Q₁ = R₂ := rfl
    calc F Q₁ + G Q₁ ≤ 2 * F Q₁ := by linarith
      _ ≤ 2 ^ (m + n) * (R₁ + R₂ + R₃) := by
        refine two_le _ (hFnn _ hQ1) (by rw [hX]; linarith) fun h0 => ?_
        have hm : m = 0 := by omega
        subst hm
        simp [hF]
  by_cases h2 : F Q₂ ≤ G Q₂
  · refine ⟨Q₂, hQ12, le_rfl, ?_⟩
    have hX : G Q₂ = R₃ := rfl
    calc F Q₂ + G Q₂ ≤ 2 * G Q₂ := by linarith
      _ ≤ 2 ^ (m + n) * (R₁ + R₂ + R₃) := by
        refine two_le _ (hGnn _ (by linarith)) (by rw [hX]; linarith) fun h0 => ?_
        have hn : n = 0 := by omega
        subst hn
        simp [hG]
  push Not at h1 h2
  -- intermediate value theorem for `F - G`
  have hcont : ContinuousOn (fun q => F q - G q) (Icc Q₁ Q₂) := by
    have hne : ∀ x ∈ Icc Q₁ Q₂, x ≠ 0 := fun x hx => ne_of_gt (lt_of_lt_of_le hQ1 hx.1)
    refine ContinuousOn.sub ?_ ?_
    · refine continuousOn_finsetSum _ fun i _ => continuousOn_const.mul ?_
      exact continuousOn_id.rpow_const fun x hx => Or.inl (hne x hx)
    · refine continuousOn_finsetSum _ fun j _ => continuousOn_const.mul ?_
      exact continuousOn_id.rpow_const fun x hx => Or.inl (hne x hx)
  obtain ⟨q, hq, hFG⟩ : ∃ q ∈ Icc Q₁ Q₂, F q - G q = 0 :=
    intermediate_value_Icc hQ12 hcont
      ⟨by show F Q₁ - G Q₁ ≤ 0; linarith, by show 0 ≤ F Q₂ - G Q₂; linarith⟩
  have hq0 : 0 < q := lt_of_lt_of_le hQ1 hq.1
  refine ⟨q, hq.1, hq.2, ?_⟩
  set S := F q with hS
  have hGS : G q = S := by linarith
  have hS0 : 0 ≤ S := hFnn q hq0
  change S + G q ≤ _
  rw [hGS]
  -- degenerate cases
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have : S = 0 := by simp [hS, hF]
    rw [this]
    simp only [add_zero]
    exact mul_nonneg (by positivity) hR0
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have : S = 0 := by rw [← hGS]; simp [hG]
    rw [this]
    simp only [add_zero]
    exact mul_nonneg (by positivity) hR0
  -- a large `i` and a large `j`
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨i₀, -, hi₀⟩ : ∃ i ∈ (univ : Finset (Fin m)), S / m ≤ A i * q ^ a i := by
    refine Finset.exists_le_of_sum_le (Finset.univ_nonempty_iff.2 ⟨⟨0, hm⟩⟩) ?_
    rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_div_cancel₀ _ hm'.ne']
  obtain ⟨j₀, -, hj₀⟩ : ∃ j ∈ (univ : Finset (Fin n)), S / n ≤ B j * q ^ (-b j) := by
    refine Finset.exists_le_of_sum_le (Finset.univ_nonempty_iff.2 ⟨⟨0, hn⟩⟩) ?_
    rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_div_cancel₀ _ hn'.ne']
    exact hGS.symm.le
  -- `T = S / max(m, n)`
  set K : ℝ := ((max m n : ℕ) : ℝ) with hK
  have hK0 : 0 < K := by
    rw [hK]
    exact_mod_cast lt_max_of_lt_left hm
  have hKm : (m : ℝ) ≤ K := by rw [hK]; exact_mod_cast le_max_left m n
  have hKn : (n : ℝ) ≤ K := by rw [hK]; exact_mod_cast le_max_right m n
  set T := S / K with hT
  have hT0 : 0 ≤ T := div_nonneg hS0 hK0.le
  have hTi : T ≤ A i₀ * q ^ a i₀ :=
    le_trans (div_le_div_of_nonneg_left hS0 hm' hKm) hi₀
  have hTj : T ≤ B j₀ * q ^ (-b j₀) :=
    le_trans (div_le_div_of_nonneg_left hS0 hn' hKn) hj₀
  -- the cross term dominates `T`
  have hcross : T ≤ (A i₀ ^ b j₀ * B j₀ ^ a i₀) ^ (1 / (a i₀ + b j₀)) := by
    have hab : 0 < a i₀ + b j₀ := by linarith [ha i₀, hb j₀]
    have hpow : T ^ (a i₀ + b j₀) ≤ A i₀ ^ b j₀ * B j₀ ^ a i₀ := by
      calc T ^ (a i₀ + b j₀) = T ^ b j₀ * T ^ a i₀ := by
            rw [add_comm, Real.rpow_add' hT0 (by linarith [ha i₀, hb j₀])]
        _ ≤ (A i₀ * q ^ a i₀) ^ b j₀ * (B j₀ * q ^ (-b j₀)) ^ a i₀ :=
            mul_le_mul (Real.rpow_le_rpow hT0 hTi (hb j₀).le)
              (Real.rpow_le_rpow hT0 hTj (ha i₀).le) (Real.rpow_nonneg hT0 _)
              (Real.rpow_nonneg (mul_nonneg (hA i₀).le (Real.rpow_nonneg hq0.le _)) _)
        _ = A i₀ ^ b j₀ * B j₀ ^ a i₀ * (q ^ (a i₀ * b j₀) * q ^ (-(b j₀) * a i₀)) := by
            rw [Real.mul_rpow (hA i₀).le (Real.rpow_nonneg hq0.le _),
              Real.mul_rpow (hB j₀).le (Real.rpow_nonneg hq0.le _),
              ← Real.rpow_mul hq0.le, ← Real.rpow_mul hq0.le]
            ring
        _ = A i₀ ^ b j₀ * B j₀ ^ a i₀ := by
            rw [← Real.rpow_add hq0]
            have : a i₀ * b j₀ + -b j₀ * a i₀ = 0 := by ring
            rw [this, Real.rpow_zero, mul_one]
    calc T = (T ^ (a i₀ + b j₀)) ^ (1 / (a i₀ + b j₀)) := by
          rw [one_div, Real.rpow_rpow_inv hT0 hab.ne']
      _ ≤ (A i₀ ^ b j₀ * B j₀ ^ a i₀) ^ (1 / (a i₀ + b j₀)) :=
          Real.rpow_le_rpow (Real.rpow_nonneg hT0 _) hpow (by positivity)
  have hTR : T ≤ R₁ := by
    have hinner : ∀ i : Fin m, 0 ≤ ∑ j, (A i ^ b j * B j ^ a i) ^ (1 / (a i + b j)) :=
      fun i => Finset.sum_nonneg fun j _ => Real.rpow_nonneg
        (mul_nonneg (Real.rpow_nonneg (hA i).le _) (Real.rpow_nonneg (hB j).le _)) _
    have h1 : (A i₀ ^ b j₀ * B j₀ ^ a i₀) ^ (1 / (a i₀ + b j₀)) ≤
        ∑ j, (A i₀ ^ b j * B j ^ a i₀) ^ (1 / (a i₀ + b j)) :=
      Finset.single_le_sum (f := fun j => (A i₀ ^ b j * B j ^ a i₀) ^ (1 / (a i₀ + b j)))
        (fun j _ => Real.rpow_nonneg
          (mul_nonneg (Real.rpow_nonneg (hA i₀).le _) (Real.rpow_nonneg (hB j).le _)) _)
        (Finset.mem_univ j₀)
    have h2 : ∑ j, (A i₀ ^ b j * B j ^ a i₀) ^ (1 / (a i₀ + b j)) ≤ R₁ :=
      Finset.single_le_sum (f := fun i => ∑ j, (A i ^ b j * B j ^ a i) ^ (1 / (a i + b j)))
        (fun i _ => hinner i) (Finset.mem_univ i₀)
    exact hcross.trans (h1.trans h2)
  -- assemble
  have h2K : 2 * K ≤ 2 ^ (m + n) := by
    rw [hK]
    exact_mod_cast two_mul_max_le_two_pow hm hn
  have hSKT : S = K * T := by
    rw [hT, mul_div_cancel₀ _ hK0.ne']
  calc S + S = (2 * K) * T := by rw [hSKT]; ring
    _ ≤ 2 ^ (m + n) * T := mul_le_mul_of_nonneg_right h2K hT0
    _ ≤ 2 ^ (m + n) * (R₁ + R₂ + R₃) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)

end LeanProofs.IntegerPoints

import IntegerPoints.VanDerCorput
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Zhai–Cao, Lemma 3 (Krätzel)

`∑_{n ∼ N} min(D, 1/‖f(n)‖) ≪ (P + 1)(D + Δ⁻¹) log(2 + Δ⁻¹)` when `|f| ≪ P`
and `|f'| ≫ Δ` on `[N, 2N]`.

Proof.  By the mean value theorem the values `f(n)`, `n ∼ N`, are
`δ = c₂Δ`-separated.  Group the `n` according to `k = round(f(n))`; there are
at most `2c₁P + 5` groups.  Inside a group, with `u = f(n) - k ∈ [-1/2, 1/2)`,
the shell `⌊|u|/δ⌋ = j` contains at most two `n` (one with `u ≥ 0`, one with
`u < 0`), and on shell `j ≥ 1` the summand is at most `1/(jδ)`; so a group
contributes at most `2D + (2/δ) H_J ≤ 2D + (2/δ)(1 + log(2 + 1/δ))`.
-/

open Real Finset

namespace LeanProofs.IntegerPoints

namespace Lemma3

/-- The summand is at most `D`. -/
theorem minInv_le_left (D t : ℝ) : minInv D t ≤ D := by
  unfold minInv
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

/-- The summand is at most `1/t` for `t > 0`. -/
theorem minInv_le_inv {D t : ℝ} (ht : 0 < t) : minInv D t ≤ 1 / t := by
  unfold minInv
  rw [if_neg ht.ne']
  exact min_le_right _ _

/-- The shell bound for a family of `δ`-separated values in `[-1/2, 1/2)`. -/
theorem shell_bound (s : Finset ℕ) (u : ℕ → ℝ) (D δ : ℝ) (hD : 0 < D) (hδ : 0 < δ)
    (hu : ∀ n ∈ s, |u n| ≤ 1 / 2)
    (hsep : ∀ n ∈ s, ∀ n' ∈ s, n ≠ n' → δ ≤ |u n - u n'|) :
    ∑ n ∈ s, minInv D |u n| ≤ 2 * D + 2 / δ * (1 + Real.log (2 + 1 / δ)) := by
  classical
  set J := ⌊1 / (2 * δ)⌋₊ with hJ
  set sh : ℕ → ℕ := fun n => ⌊|u n| / δ⌋₊ with hsh
  set h : ℕ → ℝ := fun j => if j = 0 then D else 1 / (j * δ) with hh
  have hmaps : ∀ n ∈ s, sh n ∈ Finset.range (J + 1) := by
    intro n hn
    rw [Finset.mem_range, Nat.lt_succ_iff, hsh, hJ]
    apply Nat.floor_le_floor
    rw [div_le_div_iff₀ hδ (by positivity)]
    have := hu n hn
    nlinarith
  -- the summand is bounded by `h` of the shell
  have hbound : ∀ n ∈ s, minInv D |u n| ≤ h (sh n) := by
    intro n hn
    rw [hh]
    simp only
    split_ifs with h0
    · exact minInv_le_left _ _
    · have hj : 0 < sh n := Nat.pos_of_ne_zero h0
      have hj' : (sh n : ℝ) ≤ |u n| / δ := Nat.floor_le (by positivity)
      have hjδ : (sh n : ℝ) * δ ≤ |u n| := by rwa [le_div_iff₀ hδ] at hj'
      have hjδ0 : 0 < (sh n : ℝ) * δ := by positivity
      calc minInv D |u n| ≤ 1 / |u n| := minInv_le_inv (by linarith)
        _ ≤ 1 / ((sh n : ℝ) * δ) := one_div_le_one_div_of_le hjδ0 hjδ
  -- each shell has at most two elements
  have hfiber : ∀ j, ((s.filter (fun n => sh n = j)).card : ℝ) ≤ 2 := by
    intro j
    have hsplit : s.filter (fun n => sh n = j) =
        (s.filter (fun n => sh n = j)).filter (fun n => 0 ≤ u n) ∪
          (s.filter (fun n => sh n = j)).filter (fun n => ¬ 0 ≤ u n) :=
      (Finset.filter_union_filter_neg_eq _ _).symm
    have key : ∀ (n n' : ℕ), n ∈ s → n' ∈ s → sh n = j → sh n' = j →
        (0 ≤ u n ↔ 0 ≤ u n') → n = n' := by
      intro n n' hn hn' hjn hjn' hsign
      by_contra hne
      have hs := hsep n hn n' hn' hne
      -- both `|u n|, |u n'| ∈ [jδ, (j+1)δ)`
      have h1 := Nat.floor_le (by positivity : 0 ≤ |u n| / δ)
      have h2 := Nat.lt_floor_add_one (|u n| / δ)
      have h1' := Nat.floor_le (by positivity : 0 ≤ |u n'| / δ)
      have h2' := Nat.lt_floor_add_one (|u n'| / δ)
      rw [hsh] at hjn hjn'
      simp only at hjn hjn'
      rw [hjn] at h1 h2
      rw [hjn'] at h1' h2'
      rw [le_div_iff₀ hδ] at h1 h1'
      rw [div_lt_iff₀ hδ] at h2 h2'
      have habs : |u n - u n'| < δ := by
        rcases le_or_gt 0 (u n) with hp | hp
        · have hp' : 0 ≤ u n' := hsign.1 hp
          rw [abs_of_nonneg hp] at h1 h2
          rw [abs_of_nonneg hp'] at h1' h2'
          rw [abs_lt]
          constructor <;> linarith
        · have hp' : ¬ 0 ≤ u n' := fun h => hp.not_ge (hsign.2 h)
          push Not at hp'
          rw [abs_of_neg hp] at h1 h2
          rw [abs_of_neg hp'] at h1' h2'
          rw [abs_lt]
          constructor <;> linarith
      linarith
    have hc1 : ((s.filter (fun n => sh n = j)).filter (fun n => 0 ≤ u n)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Finset.mem_filter] at ha hb
      exact key a b ha.1.1 hb.1.1 ha.1.2 hb.1.2 ⟨fun _ => hb.2, fun _ => ha.2⟩
    have hc2 : ((s.filter (fun n => sh n = j)).filter (fun n => ¬ 0 ≤ u n)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Finset.mem_filter] at ha hb
      exact key a b ha.1.1 hb.1.1 ha.1.2 hb.1.2 ⟨fun h => (ha.2 h).elim, fun h => (hb.2 h).elim⟩
    rw [hsplit]
    have := Finset.card_union_le ((s.filter (fun n => sh n = j)).filter (fun n => 0 ≤ u n))
      ((s.filter (fun n => sh n = j)).filter (fun n => ¬ 0 ≤ u n))
    have : ((s.filter (fun n => sh n = j)).filter (fun n => 0 ≤ u n) ∪
        (s.filter (fun n => sh n = j)).filter (fun n => ¬ 0 ≤ u n)).card ≤ 2 := by omega
    exact_mod_cast this
  have hh0 : ∀ j, 0 ≤ h j := by
    intro j
    rw [hh]
    simp only
    split_ifs
    · exact hD.le
    · positivity
  -- sum over shells
  calc ∑ n ∈ s, minInv D |u n| ≤ ∑ n ∈ s, h (sh n) := Finset.sum_le_sum hbound
    _ = ∑ j ∈ Finset.range (J + 1), ∑ n ∈ s.filter (fun n => sh n = j), h (sh n) :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ = ∑ j ∈ Finset.range (J + 1), ((s.filter (fun n => sh n = j)).card : ℝ) * h j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_congr rfl (fun n hn => by
          rw [(Finset.mem_filter.1 hn).2] : ∀ n ∈ s.filter (fun n => sh n = j), h (sh n) = h j)]
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ j ∈ Finset.range (J + 1), 2 * h j :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hfiber j) (hh0 j)
    _ = 2 * D + 2 / δ * (harmonic J : ℝ) := by
        rw [Finset.sum_range_succ', harmonic, Rat.cast_sum]
        simp only [hh, if_pos rfl, Nat.succ_ne_zero, if_false, Finset.mul_sum]
        rw [add_comm]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        push_cast
        field_simp
    _ ≤ 2 * D + 2 / δ * (1 + Real.log (2 + 1 / δ)) := by
        have hharm := harmonic_le_one_add_log J
        have hJle : (J : ℝ) ≤ 2 + 1 / δ := by
          have : (J : ℝ) ≤ 1 / (2 * δ) := Nat.floor_le (by positivity)
          have : 1 / (2 * δ) ≤ 1 / δ := by
            rw [div_le_div_iff₀ (by positivity) hδ]
            linarith
          linarith
        have hlog : Real.log J ≤ Real.log (2 + 1 / δ) := by
          rcases Nat.eq_zero_or_pos J with h0 | h0
          · rw [h0, Nat.cast_zero, Real.log_zero]
            exact (Real.log_pos (by linarith [show (0 : ℝ) < 1 / δ by positivity])).le
          · exact Real.log_le_log (by exact_mod_cast h0) hJle
        have : (harmonic J : ℝ) ≤ 1 + Real.log (2 + 1 / δ) := le_trans hharm (by linarith)
        have h2δ : 0 ≤ 2 / δ := by positivity
        nlinarith

end Lemma3

open Lemma3 in
/-- **Zhai–Cao, Lemma 3** (`zhaiCao_lemma3`). -/
theorem zhaiCao_lemma3_holds : zhaiCao_lemma3 := by
  intro c₁ c₂ hc₁ hc₂
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set K₁ : ℝ := 1 + Real.log (1 + 1 / c₂) / Real.log 2 with hK₁
  set K₂ : ℝ := 2 / Real.log 2 + 2 / c₂ * (1 / Real.log 2 + K₁) with hK₂
  have hK₁0 : 0 ≤ K₁ := by
    have : 0 ≤ Real.log (1 + 1 / c₂) :=
      Real.log_nonneg (by linarith [show (0 : ℝ) < 1 / c₂ by positivity])
    rw [hK₁]
    positivity
  have hK₂0 : 0 ≤ K₂ := by rw [hK₂]; positivity
  refine ⟨(2 * c₁ + 5) * K₂, fun N P Δ D f hN hP hΔ hD hf h1 h2 => ?_⟩
  classical
  set δ := c₂ * Δ with hδ
  have hδ0 : 0 < δ := by positivity
  have hmemIcc : ∀ n ∈ dyadic N, (n : ℝ) ∈ Set.Icc N (2 * N) := by
    intro n hn
    simp only [dyadic, intRange, Finset.mem_Ioc] at hn
    exact ⟨(Nat.floor_lt (by linarith)).1 hn.1 |>.le,
      (Nat.le_floor_iff (by linarith)).1 hn.2⟩
  -- separation of the values `f(n)`
  have hsep : ∀ n ∈ dyadic N, ∀ n' ∈ dyadic N, n ≠ n' → δ ≤ |f n - f n'| := by
    have hcont : Continuous f := hf.continuous
    have hdiff : Differentiable ℝ f := hf.differentiable one_ne_zero
    have key : ∀ n ∈ dyadic N, ∀ n' ∈ dyadic N, n < n' → δ ≤ |f n' - f n| := by
      intro n hn n' hn' hlt
      have hlt' : (n : ℝ) < n' := by exact_mod_cast hlt
      obtain ⟨ξ, hξ, hξ'⟩ := exists_deriv_eq_slope f hlt' hcont.continuousOn hdiff.differentiableOn
      have hξI : ξ ∈ Set.Icc N (2 * N) :=
        ⟨le_trans (hmemIcc n hn).1 hξ.1.le, le_trans hξ.2.le (hmemIcc n' hn').2⟩
      have hd := h2 ξ hξI
      have hpos : (0 : ℝ) < n' - n := by linarith
      rw [hξ', abs_div, abs_of_pos hpos, le_div_iff₀ hpos] at hd
      have h1n : (1 : ℝ) ≤ n' - n := by
        have : n + 1 ≤ n' := hlt
        have : ((n : ℝ) + 1) ≤ n' := by exact_mod_cast this
        linarith
      calc δ = δ * 1 := by ring
        _ ≤ δ * ((n' : ℝ) - n) := mul_le_mul_of_nonneg_left h1n hδ0.le
        _ ≤ |f n' - f n| := hd
    intro n hn n' hn' hne
    rcases lt_or_gt_of_ne hne with h | h
    · rw [abs_sub_comm]
      exact key n hn n' hn' h
    · exact key n' hn' n hn h
  -- grouping by `round (f n)`
  set m : ℤ := ⌈c₁ * P⌉ with hm
  set t : Finset ℤ := Finset.Icc (-(m + 1)) (m + 1) with ht
  have hmaps : ∀ n ∈ dyadic N, round (f n) ∈ t := by
    intro n hn
    have hb := h1 n (hmemIcc n hn)
    have hr := VdC.round_bounds (f n)
    have hcm : c₁ * P ≤ m := Int.le_ceil _
    rw [ht, Finset.mem_Icc]
    rw [abs_le] at hb
    constructor
    · have : (-(m + 1) : ℝ) ≤ round (f n) := by push_cast; linarith
      exact_mod_cast this
    · have : (round (f n) : ℝ) ≤ m + 1 := by push_cast; linarith
      exact_mod_cast this
  have hgroup : ∀ k ∈ t, ∑ n ∈ (dyadic N).filter (fun n : ℕ => round (f n) = k),
      minInv D (nearestIntDist (f n)) ≤ 2 * D + 2 / δ * (1 + Real.log (2 + 1 / δ)) := by
    intro k _
    have : ∀ n ∈ (dyadic N).filter (fun n : ℕ => round (f n) = k),
        nearestIntDist (f n) = |f n - k| := by
      intro n hn
      rw [Finset.mem_filter] at hn
      unfold nearestIntDist
      rw [hn.2]
    rw [Finset.sum_congr rfl fun n hn => by rw [this n hn]]
    refine shell_bound _ (fun n => f n - k) D δ hD hδ0 ?_ ?_
    · intro n hn
      rw [Finset.mem_filter] at hn
      have := abs_sub_round (f n)
      rwa [hn.2] at this
    · intro n hn n' hn' hne
      rw [Finset.mem_filter] at hn hn'
      have := hsep n hn.1 n' hn'.1 hne
      show δ ≤ |f n - k - (f n' - k)|
      rwa [show f n - k - (f n' - k) = f n - f n' by ring]
  -- the number of groups
  have hcard : (t.card : ℝ) ≤ 2 * c₁ * P + 5 := by
    rw [ht, Int.card_Icc]
    have hm0 : (0 : ℤ) ≤ m := by
      rw [hm]
      exact Int.ceil_nonneg (by positivity)
    have : (m + 1 + 1 - -(m + 1)).toNat = (2 * m + 3).toNat := by congr 1; ring
    have h3 : (((2 * m + 3).toNat : ℕ) : ℝ) = ((2 * m + 3 : ℤ) : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
    rw [this, h3]
    have hcm : (m : ℝ) < c₁ * P + 1 := by rw [hm]; exact Int.ceil_lt_add_one _
    push_cast
    linarith
  -- the logarithmic bookkeeping
  set L := Real.log (2 + Δ⁻¹) with hL
  have hL0 : Real.log 2 ≤ L := by
    rw [hL]
    exact Real.log_le_log (by norm_num) (by linarith [show (0 : ℝ) ≤ Δ⁻¹ by positivity])
  have hL1 : 1 ≤ L / Real.log 2 := by rw [le_div_iff₀ hlog2]; linarith
  have hlogδ : Real.log (2 + 1 / δ) ≤ K₁ * L := by
    have h1 : 2 + 1 / δ ≤ (1 + 1 / c₂) * (2 + Δ⁻¹) := by
      rw [show 1 / δ = 1 / c₂ * Δ⁻¹ by rw [hδ]; field_simp]
      have hx : 0 ≤ Δ⁻¹ := by positivity
      have hy : 0 ≤ 1 / c₂ := by positivity
      nlinarith [mul_nonneg hx hy]
    have h2 : Real.log (2 + 1 / δ) ≤ Real.log (1 + 1 / c₂) + L := by
      rw [hL, ← Real.log_mul (by positivity) (by positivity)]
      exact Real.log_le_log (by positivity) h1
    have h3 : Real.log (1 + 1 / c₂) ≤ Real.log (1 + 1 / c₂) / Real.log 2 * L := by
      have hnn : 0 ≤ Real.log (1 + 1 / c₂) :=
        Real.log_nonneg (by linarith [show (0 : ℝ) < 1 / c₂ by positivity])
      calc Real.log (1 + 1 / c₂) = Real.log (1 + 1 / c₂) * 1 := by ring
        _ ≤ Real.log (1 + 1 / c₂) * (L / Real.log 2) := mul_le_mul_of_nonneg_left hL1 hnn
        _ = Real.log (1 + 1 / c₂) / Real.log 2 * L := by ring
    rw [hK₁]
    linarith
  have hF : 2 * D + 2 / δ * (1 + Real.log (2 + 1 / δ)) ≤ K₂ * ((D + Δ⁻¹) * L) := by
    have hδinv : 1 / δ = 1 / c₂ * Δ⁻¹ := by rw [hδ]; field_simp
    have hD' : 2 * D ≤ 2 / Real.log 2 * (D * L) := by
      calc 2 * D = 2 * D * 1 := by ring
        _ ≤ 2 * D * (L / Real.log 2) := mul_le_mul_of_nonneg_left hL1 (by positivity)
        _ = 2 / Real.log 2 * (D * L) := by field_simp
    have h1' : (1 : ℝ) ≤ 1 / Real.log 2 * L := by
      rw [div_mul_eq_mul_div, one_mul]
      exact hL1
    have hΔ' : 2 / δ * (1 + Real.log (2 + 1 / δ)) ≤ 2 / c₂ * (1 / Real.log 2 + K₁) * (Δ⁻¹ * L) := by
      have h2δ : 2 / δ = 2 / c₂ * Δ⁻¹ := by rw [hδ]; field_simp
      rw [h2δ]
      have hnn : 0 ≤ 2 / c₂ * Δ⁻¹ := by positivity
      calc 2 / c₂ * Δ⁻¹ * (1 + Real.log (2 + 1 / δ))
          ≤ 2 / c₂ * Δ⁻¹ * (1 / Real.log 2 * L + K₁ * L) :=
            mul_le_mul_of_nonneg_left (by linarith) hnn
        _ = 2 / c₂ * (1 / Real.log 2 + K₁) * (Δ⁻¹ * L) := by ring
    have hLpos : 0 < L := by linarith
    have e1 : 0 ≤ 2 / Real.log 2 * (Δ⁻¹ * L) := by positivity
    have e2 : 0 ≤ 2 / c₂ * (1 / Real.log 2 + K₁) * (D * L) := by positivity
    rw [hK₂]
    nlinarith [hD', hΔ', e1, e2]
  -- assemble
  have hLpos : 0 < L := by linarith
  have hlogδ0 : 0 ≤ Real.log (2 + 1 / δ) :=
    Real.log_nonneg (by linarith [show (0 : ℝ) < 1 / δ by positivity])
  have hRHS0 : 0 ≤ K₂ * ((D + Δ⁻¹) * L) :=
    mul_nonneg hK₂0 (mul_nonneg (by positivity) hLpos.le)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  calc ∑ k ∈ t, ∑ n ∈ (dyadic N).filter (fun n : ℕ => round (f n) = k),
        minInv D (nearestIntDist (f n))
      ≤ ∑ k ∈ t, (2 * D + 2 / δ * (1 + Real.log (2 + 1 / δ))) := Finset.sum_le_sum hgroup
    _ = (t.card : ℝ) * (2 * D + 2 / δ * (1 + Real.log (2 + 1 / δ))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * c₁ * P + 5) * (K₂ * ((D + Δ⁻¹) * L)) :=
        mul_le_mul hcard hF
          (add_nonneg (by positivity) (mul_nonneg (by positivity) (by linarith)))
          (by positivity)
    _ ≤ ((2 * c₁ + 5) * (P + 1)) * (K₂ * ((D + Δ⁻¹) * L)) := by
        apply mul_le_mul_of_nonneg_right _ hRHS0
        nlinarith
    _ = (2 * c₁ + 5) * K₂ * ((P + 1) * (D + Δ⁻¹) * L) := by ring

end LeanProofs.IntegerPoints

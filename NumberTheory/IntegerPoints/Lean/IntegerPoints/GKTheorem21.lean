import IntegerPoints.GKStatements
import IntegerPoints.VanDerCorput

/-!
# Graham–Kolesnik, Theorem 2.1 as invoked in §3.3

The first two defining inequalities of `InGKClass N 2 s y ε a b f` put
`f'` uniformly away from the integers and make it antitone.  The
Kuz'min–Landau inequality then gives the required reciprocal-scale bound.
-/

open Real Finset

namespace LeanProofs.IntegerPoints

/-- **Graham–Kolesnik, Theorem 2.1**, in the form invoked in §3.3. -/
theorem gk_theorem21_invoked_holds : gk_theorem21_invoked := by
  intro s ε hs hε hεhalf
  set C : ℝ := 8 * (2 : ℝ) ^ s with hC
  refine ⟨C, ?_⟩
  intro N y a b f hN hy hf hzsmall
  obtain ⟨hNa, hab, hb2N, hf2, hcls⟩ := hf

  set z : ℝ := y * N ^ (-s) with hz
  have hz0 : 0 < z := by positivity
  have hzsmall' : z < 1 / 2 := by simpa [hz] using hzsmall
  have hzinv : z⁻¹ = y⁻¹ * N ^ s := by
    rw [hz, mul_inv, Real.rpow_neg hN.le, inv_inv]

  have hf2' : ContDiff ℝ 2 f := by simpa using hf2
  have hf' : ContDiff ℝ 1 (deriv f) :=
    (contDiff_succ_iff_deriv.mp
      (show ContDiff ℝ (1 + 1) f from hf2')).2.2
  have hd1 : ∀ t ∈ Set.Icc a b,
      |deriv f t - y * t ^ (-s)| < ε * (y * t ^ (-s)) := by
    intro t ht
    have h := hcls 0 (by norm_num) t ht
    simp only [Finset.range_zero, Finset.prod_empty, Nat.cast_zero,
      sub_zero, pow_zero, zero_add, iteratedDeriv_one] at h
    calc
      |deriv f t - y * t ^ (-s)| =
          |deriv f t - 1 * 1 * y * t ^ (-s)| := by ring_nf
      _ < ε * 1 * y * t ^ (-s) := h
      _ = ε * (y * t ^ (-s)) := by ring
  have hd2 : ∀ t ∈ Set.Icc a b,
      |deriv (deriv f) t + s * y * t ^ (-s - 1)| ≤
        ε * (s * y * t ^ (-s - 1)) := by
    intro t ht
    have h := hcls 1 (by norm_num) t ht
    simp only [Finset.range_one, Finset.prod_singleton, Nat.cast_zero,
      add_zero, pow_one, Nat.cast_one, iteratedDeriv_succ,
      iteratedDeriv_zero] at h
    calc
      |deriv (deriv f) t + s * y * t ^ (-s - 1)| =
          |deriv (deriv f) t - -1 * s * y * t ^ (-s - 1)| := by ring_nf
      _ ≤ ε * s * y * t ^ (-s - 1) := h.le
      _ = ε * (s * y * t ^ (-s - 1)) := by ring

  set A := ⌊a⌋₊ with hA
  set B := ⌊b⌋₊ with hB
  have hrange : intRange a b = Finset.Ioc A B := rfl
  have ha0 : 0 ≤ a := by linarith
  have haA : a < A + 1 := Nat.lt_floor_add_one a
  have hBb : (B : ℝ) ≤ b := Nat.floor_le (by linarith)
  have hsub : Set.Icc (A + 1 : ℝ) B ⊆ Set.Icc a b :=
    Set.Icc_subset_Icc haA.le hBb

  set lam : ℝ := 1 / 2 * (2 : ℝ) ^ (-s) * z with hlam
  have h2s1 : (2 : ℝ) ^ (-s) ≤ 1 := by
    rw [Real.rpow_neg (by norm_num)]
    exact inv_le_one_of_one_le₀
      (Real.one_le_rpow (by norm_num) hs.le)
  have hlam0 : 0 < lam := by positivity
  have h2sz : (2 : ℝ) ^ (-s) * z ≤ 1 / 2 := by
    calc
      (2 : ℝ) ^ (-s) * z ≤ 1 * (1 / 2) :=
        mul_le_mul h2s1 hzsmall'.le hz0.le zero_le_one
      _ = 1 / 2 := by ring
  have hlamquarter : lam ≤ 1 / 4 := by
    rw [hlam, mul_assoc]
    linarith
  have hlamhalf : lam ≤ 1 / 2 := by linarith

  have hderiv : ∀ t ∈ Set.Icc a b,
      lam ≤ deriv f t ∧ deriv f t ≤ 1 - lam := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hN (hNa.trans ht.1)
    have htN : N ≤ t := hNa.trans ht.1
    have ht2N : t ≤ 2 * N := ht.2.trans hb2N
    have hpowlower : (2 * N) ^ (-s) ≤ t ^ (-s) :=
      Real.rpow_le_rpow_of_nonpos ht0 ht2N (by linarith)
    have hpowupper : t ^ (-s) ≤ N ^ (-s) :=
      Real.rpow_le_rpow_of_nonpos hN htN (by linarith)
    have hsplit : (2 * N) ^ (-s) =
        (2 : ℝ) ^ (-s) * N ^ (-s) :=
      Real.mul_rpow (by norm_num) hN.le
    have hb := abs_lt.1 (hd1 t ht)
    have hytlower : (2 : ℝ) ^ (-s) * z ≤ y * t ^ (-s) := by
      rw [hz, ← mul_assoc, mul_comm ((2 : ℝ) ^ (-s)) y,
        mul_assoc, ← hsplit]
      exact mul_le_mul_of_nonneg_left hpowlower hy.le
    have hytupper : y * t ^ (-s) ≤ z := by
      rw [hz]
      exact mul_le_mul_of_nonneg_left hpowupper hy.le
    have hyt0 : 0 < y * t ^ (-s) := by positivity
    have hεyt : ε * (y * t ^ (-s)) <
        1 / 2 * (y * t ^ (-s)) :=
      mul_lt_mul_of_pos_right hεhalf hyt0
    have hlower : 1 / 2 * (y * t ^ (-s)) < deriv f t := by
      linarith [hb.1, hεyt]
    have hlamderiv : lam ≤ deriv f t := by
      calc
        lam = 1 / 2 * ((2 : ℝ) ^ (-s) * z) := by
          rw [hlam]
          ring
        _ ≤ 1 / 2 * (y * t ^ (-s)) :=
          mul_le_mul_of_nonneg_left hytlower (by norm_num)
        _ ≤ deriv f t := hlower.le
    have hεytupper : ε * (y * t ^ (-s)) ≤ ε * z :=
      mul_le_mul_of_nonneg_left hytupper hε.le
    have hεz : ε * z < 1 / 2 * z :=
      mul_lt_mul_of_pos_right hεhalf hz0
    have hupper : deriv f t < 3 / 2 * z := by
      linarith [hb.2, hytupper, hεytupper, hεz]
    have hupperquarter : deriv f t < 3 / 4 := by
      linarith [hupper, hzsmall']
    exact ⟨hlamderiv, by linarith [hupperquarter, hlamquarter]⟩

  have hεone : ε < 1 := by linarith
  have hanti : AntitoneOn (deriv f) (Set.Icc (A + 1 : ℝ) B) := by
    refine antitoneOn_of_deriv_nonpos
      (convex_Icc _ _)
      hf'.continuous.continuousOn
      (hf'.differentiable one_ne_zero).differentiableOn
      fun x hx => ?_
    rw [interior_Icc] at hx
    have hxI := hsub ⟨hx.1.le, hx.2.le⟩
    have hb := abs_le.1 (hd2 x hxI)
    have hx0 : 0 < x :=
      lt_of_lt_of_le hN (hNa.trans hxI.1)
    have hmain : 0 < s * y * x ^ (-s - 1) := by positivity
    have hεmain : ε * (s * y * x ^ (-s - 1)) <
        s * y * x ^ (-s - 1) :=
      by simpa only [one_mul] using mul_lt_mul_of_pos_right hεone hmain
    linarith [hb.2, hεmain]

  have hKL :=
    KL.kuzmin_landau f A B lam hlam0 hlamhalf
      (hf2'.of_le (by norm_num))
      (Or.inr hanti)
      fun t ht => by
        have ht' := hderiv t (hsub ht)
        exact VdC.nearestIntDist_ge 0
          (by push_cast; linarith)
          (by push_cast; linarith)

  have hbound : 4 / lam = C * z⁻¹ := by
    have h2pos : 0 < (2 : ℝ) ^ s := by positivity
    rw [hlam, hC,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    field_simp
    ring

  calc
    ‖∑ n ∈ intRange a b, e (f n)‖ =
        ‖∑ n ∈ Finset.Ioc A B, e (f n)‖ := by rw [hrange]
    _ ≤ 4 / lam := hKL
    _ = C * z⁻¹ := hbound
    _ = C * (y⁻¹ * N ^ s) := by rw [hzinv]

end LeanProofs.IntegerPoints

/-
# The BCH logarithm lies in every closed Lie subalgebra containing `X` and `Y`

This file proves the analytic form of the statement that the BCH series is a
Lie series: in a real or complex unital Banach algebra there is `δ > 0` such
that for every closed subspace `𝔤` that is closed under the commutator bracket
(`IsClosedLieSubalgebra`), and all `X, Y ∈ 𝔤` with `‖X‖ + ‖Y‖ < δ`, the
logarithm `log(e^X e^Y)` (the Mercator logarithm, equal to the BCH series
`∑ₙ Zₙ(X, Y)`) lies in `𝔤` (`exists_delta_mlog_mem`). For a matrix Lie algebra
`𝔤 ⊆ gl_d` this is the local BCH multiplication law of the accompanying
article (`docs/combined`, Proposition 8.1): `e^X e^Y = e^{Z}` with `Z ∈ 𝔤`.

## Method

By the logarithmic differential equation (Theorem 6.1, `BCH.ODE`) the curve
`Z(t) = log(e^X e^{tY})` satisfies `Z'(t) = F(Z(t))`, `F(W) = β(ad_W) Y`, with
`Z(0) = X`. The vector field `F` maps `𝔤` into itself (`β(ad_W) Y` is a limit
of iterated brackets of `W` and `Y`) and is Lipschitz on the ball `‖W‖ ≤ 3/8`.
The distance `d(t) = dist(Z(t), 𝔤)` therefore satisfies the differential
inequality `D⁺ d(t) ≤ K d(t)` (compare `Z(t+h)` with `w + h F(w)` for `w ∈ 𝔤`
close to `Z(t)`), so Gronwall's inequality and `d(0) = 0` give `d ≡ 0`.
-/
import BCH.ODE
import Mathlib.Analysis.ODE.Gronwall

open NormedSpace Filter Topology Metric

namespace BCH

section Lipschitz

variable {𝕂 𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

omit [CompleteSpace 𝔸] in
lemma ad_sub (X Y : 𝔸) : ad 𝕂 (X - Y) = ad 𝕂 X - ad 𝕂 Y := by
  ext Z
  simp only [sub_apply, ad_apply']
  noncomm_ring

omit [CompleteSpace 𝔸] in
lemma norm_ad_sub_le (X Y : 𝔸) : ‖ad 𝕂 X - ad 𝕂 Y‖ ≤ 2 * ‖X - Y‖ := by
  rw [← ad_sub]; exact norm_ad_le _

omit [CompleteSpace 𝔸] in
/-- `‖T^{n+1} - S^{n+1}‖ ≤ (n+1) q^n ‖T - S‖` for `‖T‖, ‖S‖ ≤ q`, in the operator algebra. -/
lemma norm_pow_succ_sub_pow_succ_le {T S : 𝔸 →L[𝕂] 𝔸} {q : ℝ} (hq : 0 ≤ q) (hT : ‖T‖ ≤ q)
    (hS : ‖S‖ ≤ q) :
    ∀ n : ℕ, ‖T ^ (n + 1) - S ^ (n + 1)‖ ≤ ((n : ℝ) + 1) * q ^ n * ‖T - S‖
  | 0 => by simp
  | n + 1 => by
    have ih := norm_pow_succ_sub_pow_succ_le hq hT hS n
    have hSn : ‖S ^ (n + 1)‖ ≤ q ^ (n + 1) :=
      (norm_pow_le' S n.succ_pos).trans (pow_le_pow_left₀ (norm_nonneg _) hS _)
    have hid : T ^ (n + 1 + 1) - S ^ (n + 1 + 1) =
        (T ^ (n + 1) - S ^ (n + 1)) * T + S ^ (n + 1) * (T - S) := by
      rw [sub_mul, mul_sub, ← pow_succ T (n + 1), ← pow_succ S (n + 1)]; abel
    rw [hid]
    calc ‖(T ^ (n + 1) - S ^ (n + 1)) * T + S ^ (n + 1) * (T - S)‖
        ≤ ‖T ^ (n + 1) - S ^ (n + 1)‖ * ‖T‖ + ‖S ^ (n + 1)‖ * ‖T - S‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ (((n : ℝ) + 1) * q ^ n * ‖T - S‖) * q + q ^ (n + 1) * ‖T - S‖ :=
          add_le_add (mul_le_mul ih hT (norm_nonneg _) (by positivity))
            (mul_le_mul_of_nonneg_right hSn (norm_nonneg _))
      _ = (((n + 1 : ℕ) : ℝ) + 1) * q ^ (n + 1) * ‖T - S‖ := by
          push_cast; ring

/-- The Lipschitz constant `(8/3) ∑ₙ (n+1) (3/4)^n` of `W ↦ β(ad_W) Y` on `‖W‖ ≤ 3/8`
(per unit of `‖Y‖`). -/
noncomputable def lipK : ℝ := 8 / 3 * ∑' n : ℕ, ((n : ℝ) + 1) * (3 / 4 : ℝ) ^ n

lemma summable_succ_mul_geom : Summable fun n : ℕ => ((n : ℝ) + 1) * (3 / 4 : ℝ) ^ n := by
  have h1 : Summable fun n : ℕ => (n : ℝ) ^ 1 * (3 / 4 : ℝ) ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one 1 (by rw [Real.norm_eq_abs]; norm_num)
  have h2 : Summable fun n : ℕ => (3 / 4 : ℝ) ^ n :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  refine (h1.add h2).congr fun n => ?_
  ring

lemma lipK_nonneg : 0 ≤ lipK :=
  mul_nonneg (by norm_num) (tsum_nonneg fun n => by positivity)

omit [CompleteSpace 𝔸] in
lemma norm_bplus_cast_le (n : ℕ) : ‖((bplus n : ℚ) : 𝕂)‖ ≤ 1 := by
  rw [← RCLike.ofReal_ratCast, RCLike.norm_ofReal, ← Rat.cast_abs]
  exact_mod_cast abs_bplus_le_one n

omit [CompleteSpace 𝔸] in
lemma summable_norm_betaAd_apply_term {W : 𝔸} (hW : ‖W‖ < 1 / 2) (Y : 𝔸) :
    Summable fun n : ℕ => ‖((bplus n : ℚ) : 𝕂) • (ad 𝕂 W ^ n) Y‖ := by
  have h2W : 2 * ‖W‖ < 1 := by linarith
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    ((summable_geometric_of_lt_one (by positivity) h2W).mul_right ‖Y‖)
  rw [norm_smul]
  calc ‖((bplus n : ℚ) : 𝕂)‖ * ‖(ad 𝕂 W ^ n) Y‖ ≤ 1 * ((2 * ‖W‖) ^ n * ‖Y‖) :=
        mul_le_mul (norm_bplus_cast_le n) (norm_ad_pow_apply_le W Y n) (norm_nonneg _) zero_le_one
    _ = (2 * ‖W‖) ^ n * ‖Y‖ := one_mul _

omit [CompleteSpace 𝔸] in
/-- Termwise Lipschitz bound for `ad_W^n Y` on `‖W‖ ≤ 3/8`. -/
lemma norm_ad_pow_apply_sub_le {W W' : 𝔸} (hW : ‖W‖ ≤ 3 / 8) (hW' : ‖W'‖ ≤ 3 / 8) (Y : 𝔸)
    (n : ℕ) :
    ‖(ad 𝕂 W ^ n) Y - (ad 𝕂 W' ^ n) Y‖ ≤
      8 / 3 * ‖W - W'‖ * (((n : ℝ) + 1) * (3 / 4 : ℝ) ^ n) * ‖Y‖ := by
  have hadW : ‖ad 𝕂 W‖ ≤ 3 / 4 := (norm_ad_le W).trans (by linarith)
  have hadW' : ‖ad 𝕂 W'‖ ≤ 3 / 4 := (norm_ad_le W').trans (by linarith)
  cases n with
  | zero => simp; positivity
  | succ m =>
    rw [← sub_apply]
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    have h := norm_pow_succ_sub_pow_succ_le (𝕂 := 𝕂) (by norm_num : (0 : ℝ) ≤ 3 / 4) hadW hadW' m
    have h2 := norm_ad_sub_le (𝕂 := 𝕂) W W'
    have hpow : ((m : ℝ) + 1) * (3 / 4 : ℝ) ^ m ≤
        4 / 3 * ((((m + 1 : ℕ) : ℝ) + 1) * (3 / 4 : ℝ) ^ (m + 1)) := by
      push_cast
      rw [pow_succ]
      have : (0 : ℝ) ≤ (3 / 4 : ℝ) ^ m := by positivity
      nlinarith
    calc ‖ad 𝕂 W ^ (m + 1) - ad 𝕂 W' ^ (m + 1)‖ * ‖Y‖
        ≤ (((m : ℝ) + 1) * (3 / 4 : ℝ) ^ m * (2 * ‖W - W'‖)) * ‖Y‖ := by
          refine mul_le_mul_of_nonneg_right (h.trans ?_) (norm_nonneg _)
          exact mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ (4 / 3 * ((((m + 1 : ℕ) : ℝ) + 1) * (3 / 4 : ℝ) ^ (m + 1)) * (2 * ‖W - W'‖)) * ‖Y‖ := by
          gcongr
      _ = 8 / 3 * ‖W - W'‖ * ((((m + 1 : ℕ) : ℝ) + 1) * (3 / 4 : ℝ) ^ (m + 1)) * ‖Y‖ := by
          ring

/-- **Lipschitz estimate**: `‖β(ad_W) Y - β(ad_{W'}) Y‖ ≤ lipK ‖Y‖ ‖W - W'‖` for
`‖W‖, ‖W'‖ ≤ 3/8`. -/
theorem norm_betaAd_apply_sub_le {W W' : 𝔸} (hW : ‖W‖ ≤ 3 / 8) (hW' : ‖W'‖ ≤ 3 / 8) (Y : 𝔸) :
    ‖betaAd 𝕂 W Y - betaAd 𝕂 W' Y‖ ≤ lipK * ‖Y‖ * ‖W - W'‖ := by
  have hW2 : ‖W‖ < 1 / 2 := by linarith
  have hW'2 : ‖W'‖ < 1 / 2 := by linarith
  have hs1 := (summable_norm_betaAd_apply_term (𝕂 := 𝕂) hW2 Y).of_norm
  have hs2 := (summable_norm_betaAd_apply_term (𝕂 := 𝕂) hW'2 Y).of_norm
  rw [betaAd_apply hW2, betaAd_apply hW'2, ← hs1.tsum_sub hs2]
  have hg : HasSum (fun n : ℕ => (8 / 3 * ‖W - W'‖ * ‖Y‖) * (((n : ℝ) + 1) * (3 / 4 : ℝ) ^ n))
      ((8 / 3 * ‖W - W'‖ * ‖Y‖) * ∑' n : ℕ, ((n : ℝ) + 1) * (3 / 4 : ℝ) ^ n) :=
    summable_succ_mul_geom.hasSum.mul_left _
  refine (tsum_of_norm_bounded hg fun n => ?_).trans (le_of_eq ?_)
  · rw [← smul_sub, norm_smul]
    calc ‖((bplus n : ℚ) : 𝕂)‖ * ‖(ad 𝕂 W ^ n) Y - (ad 𝕂 W' ^ n) Y‖
        ≤ 1 * (8 / 3 * ‖W - W'‖ * (((n : ℝ) + 1) * (3 / 4 : ℝ) ^ n) * ‖Y‖) :=
          mul_le_mul (norm_bplus_cast_le n) (norm_ad_pow_apply_sub_le hW hW' Y n)
            (norm_nonneg _) zero_le_one
      _ = _ := by ring
  · rw [lipK]; ring

end Lipschitz

section Membership

variable {𝕂 𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

/-- A closed Lie subalgebra of `𝔸`: a closed `𝕂`-subspace closed under the commutator
`⁅a, b⁆ = ab - ba`. -/
structure IsClosedLieSubalgebra (𝔤 : Submodule 𝕂 𝔸) : Prop where
  isClosed : IsClosed (𝔤 : Set 𝔸)
  lie_mem : ∀ a ∈ 𝔤, ∀ b ∈ 𝔤, ⁅a, b⁆ ∈ 𝔤

omit [CompleteSpace 𝔸] in
lemma IsClosedLieSubalgebra.ad_pow_apply_mem {𝔤 : Submodule 𝕂 𝔸} (h : IsClosedLieSubalgebra 𝔤)
    {W Y : 𝔸} (hW : W ∈ 𝔤) (hY : Y ∈ 𝔤) : ∀ n : ℕ, (ad 𝕂 W ^ n) Y ∈ 𝔤
  | 0 => by simpa using hY
  | n + 1 => by
    rw [pow_succ', mul_apply_eq_comp, ad_apply]
    exact h.lie_mem W hW _ (h.ad_pow_apply_mem hW hY n)

lemma IsClosedLieSubalgebra.betaAd_apply_mem {𝔤 : Submodule 𝕂 𝔸} (h : IsClosedLieSubalgebra 𝔤)
    {W Y : 𝔸} (hW : W ∈ 𝔤) (hY : Y ∈ 𝔤) (hWn : ‖W‖ < 1 / 2) : betaAd 𝕂 W Y ∈ 𝔤 := by
  rw [betaAd_apply hWn]
  have hsum := (summable_norm_betaAd_apply_term (𝕂 := 𝕂) hWn Y).of_norm
  refine h.isClosed.mem_of_tendsto hsum.hasSum (Eventually.of_forall fun s => ?_)
  exact 𝔤.sum_mem fun n _ => 𝔤.smul_mem _ (h.ad_pow_apply_mem hW hY n)

end Membership

section Main

variable {𝕂 𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

/-- **The BCH logarithm is a Lie element** (analytic form): there is `δ > 0` such that for
every closed Lie subalgebra `𝔤` and all `X, Y ∈ 𝔤` with `‖X‖ + ‖Y‖ < δ`,
`log(e^X e^Y) ∈ 𝔤`. -/
theorem exists_delta_mlog_mem :
    ∃ δ : ℝ, 0 < δ ∧ ∀ 𝔤 : Submodule 𝕂 𝔸, IsClosedLieSubalgebra 𝔤 →
      ∀ X Y : 𝔸, X ∈ 𝔤 → Y ∈ 𝔤 → ‖X‖ + ‖Y‖ < δ → mlog 𝕂 (exp X * exp Y - 1) ∈ 𝔤 := by
  obtain ⟨δ, hδ, hode⟩ := exists_delta_bch_ode (𝕂 := 𝕂) (𝔸 := 𝔸)
  refine ⟨δ, hδ, fun 𝔤 h𝔤 X Y hX hY hXY => ?_⟩
  obtain ⟨hZ0, hZnorm, hZderiv⟩ := hode X Y hXY
  set Z : 𝕂 → 𝔸 := fun t => mlog 𝕂 (exp X * exp (t • Y) - 1) with hZdef
  have hZ1 : mlog 𝕂 (exp X * exp Y - 1) = Z 1 := by simp [Z]
  rw [hZ1]
  have hne : (𝔤 : Set 𝔸).Nonempty := ⟨0, 𝔤.zero_mem⟩
  set K : ℝ := lipK * ‖Y‖ with hK
  have hK0 : 0 ≤ K := mul_nonneg lipK_nonneg (norm_nonneg _)
  let d : ℝ → ℝ := fun s => infDist (Z (s : 𝕂)) 𝔤
  have hnorm1 : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ‖(s : 𝕂)‖ ≤ 1 := fun s hs => by
    rw [RCLike.norm_ofReal, abs_of_nonneg hs.1]; exact hs.2
  -- continuity of the distance function
  have hdcont : ContinuousOn d (Set.Icc 0 1) := by
    intro s hs
    have h1 : ContinuousAt Z (s : 𝕂) := (hZderiv _ (hnorm1 s hs)).continuousAt
    have h2 : ContinuousAt (fun s : ℝ => Z (s : 𝕂)) s :=
      h1.comp RCLike.continuous_ofReal.continuousAt
    exact ((continuous_infDist_pt (𝔤 : Set 𝔸)).continuousAt.comp h2).continuousWithinAt
  -- the differential inequality `D⁺ d ≤ K d`
  have hdini : ∀ s ∈ Set.Ico (0 : ℝ) 1, ∀ r, K * d s < r →
      ∃ᶠ s' in 𝓝[>] s, (s' - s)⁻¹ * (d s' - d s) < r := by
    intro s hs r hr
    have hs1 : ‖(s : 𝕂)‖ ≤ 1 := hnorm1 s ⟨hs.1, hs.2.le⟩
    have hZs : ‖Z (s : 𝕂)‖ < 1 / 8 := hZnorm _ hs1
    have hds : d s ≤ ‖Z (s : 𝕂)‖ := by
      have := infDist_le_dist_of_mem (x := Z (s : 𝕂)) 𝔤.zero_mem
      rwa [dist_zero_right] at this
    have hd0' : 0 ≤ d s := infDist_nonneg
    set η : ℝ := (r - K * d s) / 2 with hη
    have hη0 : 0 < η := by rw [hη]; linarith
    have hlo := Asymptotics.isLittleO_iff.mp
      (hasDerivAt_iff_isLittleO.mp (hZderiv (s : 𝕂) hs1)) hη0
    have hten : Tendsto (fun s' : ℝ => (s' : 𝕂)) (𝓝[>] s) (𝓝 (s : 𝕂)) :=
      (RCLike.continuous_ofReal.tendsto s).mono_left nhdsWithin_le_nhds
    refine Eventually.frequently ?_
    filter_upwards [hten.eventually hlo, self_mem_nhdsWithin] with s' hs' hss'
    have hh : 0 < s' - s := sub_pos.mpr hss'
    set c : 𝕂 := ((s' - s : ℝ) : 𝕂) with hc
    have hcast : (s' : 𝕂) - (s : 𝕂) = c := by rw [hc]; push_cast; ring
    have hnormc : ‖c‖ = s' - s := by rw [hc, RCLike.norm_ofReal, abs_of_pos hh]
    rw [hcast, hnormc] at hs'
    -- key inequality: `d s' ≤ (1 + hK) d s + η h`
    have hkey : d s' ≤ d s + (s' - s) * (K * d s) + η * (s' - s) := by
      refine le_of_forall_pos_lt_add fun ε hε => ?_
      set ε' : ℝ := min (ε / (2 * (1 + (s' - s) * K))) (1 / 8) with hε'
      have hden : 0 < 2 * (1 + (s' - s) * K) := by positivity
      have hε'0 : 0 < ε' := lt_min (div_pos hε hden) (by norm_num)
      have hε'1 : ε' ≤ ε / (2 * (1 + (s' - s) * K)) := min_le_left _ _
      have hε'2 : ε' ≤ 1 / 8 := min_le_right _ _
      obtain ⟨w, hw𝔤, hw⟩ := (infDist_lt_iff hne).mp (show d s < d s + ε' by linarith)
      have hZw : ‖Z (s : 𝕂) - w‖ < d s + ε' := by rw [← dist_eq_norm]; exact hw
      have hwn : ‖w‖ ≤ 3 / 8 := by
        have : ‖w‖ ≤ ‖Z (s : 𝕂)‖ + ‖Z (s : 𝕂) - w‖ := by
          calc ‖w‖ = ‖Z (s : 𝕂) - (Z (s : 𝕂) - w)‖ := by rw [sub_sub_cancel]
            _ ≤ ‖Z (s : 𝕂)‖ + ‖Z (s : 𝕂) - w‖ := norm_sub_le _ _
        linarith
      have hZsn : ‖Z (s : 𝕂)‖ ≤ 3 / 8 := by linarith
      have hFw : betaAd 𝕂 w Y ∈ 𝔤 := h𝔤.betaAd_apply_mem hw𝔤 hY (by linarith)
      have hmem : w + c • betaAd 𝕂 w Y ∈ 𝔤 := 𝔤.add_mem hw𝔤 (𝔤.smul_mem _ hFw)
      have hlip := norm_betaAd_apply_sub_le (𝕂 := 𝕂) hZsn hwn Y
      calc d s' ≤ dist (Z (s' : 𝕂)) (w + c • betaAd 𝕂 w Y) := infDist_le_dist_of_mem hmem
        _ = ‖(Z (s' : 𝕂) - Z (s : 𝕂) - c • betaAd 𝕂 (Z (s : 𝕂)) Y) + (Z (s : 𝕂) - w)
              + c • (betaAd 𝕂 (Z (s : 𝕂)) Y - betaAd 𝕂 w Y)‖ := by
            rw [dist_eq_norm]; congr 1; simp only [smul_sub]; abel
        _ ≤ ‖Z (s' : 𝕂) - Z (s : 𝕂) - c • betaAd 𝕂 (Z (s : 𝕂)) Y‖ + ‖Z (s : 𝕂) - w‖
              + ‖c‖ * ‖betaAd 𝕂 (Z (s : 𝕂)) Y - betaAd 𝕂 w Y‖ := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_smul]
            linarith [norm_add_le (Z (s' : 𝕂) - Z (s : 𝕂) - c • betaAd 𝕂 (Z (s : 𝕂)) Y)
              (Z (s : 𝕂) - w)]
        _ ≤ η * (s' - s) + (d s + ε') + (s' - s) * (K * (d s + ε')) := by
            rw [hnormc]
            refine add_le_add (add_le_add hs' hZw.le) ?_
            refine mul_le_mul_of_nonneg_left (hlip.trans ?_) hh.le
            rw [hK]
            calc lipK * ‖Y‖ * ‖Z (s : 𝕂) - w‖ ≤ lipK * ‖Y‖ * (d s + ε') :=
                  mul_le_mul_of_nonneg_left hZw.le (by positivity)
              _ = _ := by ring
        _ < d s + (s' - s) * (K * d s) + η * (s' - s) + ε := by
            have h1 : (1 + (s' - s) * K) * ε' ≤ ε / 2 := by
              calc (1 + (s' - s) * K) * ε'
                  ≤ (1 + (s' - s) * K) * (ε / (2 * (1 + (s' - s) * K))) :=
                    mul_le_mul_of_nonneg_left hε'1 (by positivity)
                _ = ε / 2 := by field_simp
            nlinarith [h1, hε, hh, hK0]
    have hslope : (s' - s)⁻¹ * (d s' - d s) ≤ K * d s + η := by
      rw [inv_mul_le_iff₀ hh]
      nlinarith [hkey]
    calc (s' - s)⁻¹ * (d s' - d s) ≤ K * d s + η := hslope
      _ < r := by rw [hη]; linarith
  -- Gronwall's inequality
  have hd0 : d 0 = 0 := by
    have : Z ((0 : ℝ) : 𝕂) = X := by simpa [Z] using hZ0
    simp only [d, this]
    exact infDist_zero_of_mem hX
  have hgron := le_gronwallBound_of_liminf_deriv_right_le (f := d) (f' := fun s => K * d s)
    (δ := 0) (K := K) (ε := 0) (a := 0) (b := 1) hdcont hdini (by rw [hd0])
    (fun s _ => by simp)
  have h1 := hgron 1 (Set.right_mem_Icc.mpr zero_le_one)
  rw [gronwallBound_ε0_δ0] at h1
  have hd1 : d 1 = 0 := le_antisymm h1 infDist_nonneg
  have hcl : Z ((1 : ℝ) : 𝕂) ∈ closure (𝔤 : Set 𝔸) :=
    (mem_closure_iff_infDist_zero hne).mpr hd1
  rw [h𝔤.isClosed.closure_eq] at hcl
  simpa using hcl

end Main

end BCH

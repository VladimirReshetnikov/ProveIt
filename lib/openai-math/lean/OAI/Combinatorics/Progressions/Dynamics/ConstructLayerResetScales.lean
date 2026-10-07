import OAI.Combinatorics.Progressions.Estimates.MonotoneWeightLayer
import OAI.Combinatorics.Progressions.Geometry.UniformCoordinatePartition
import OAI.Combinatorics.Progressions.Sampling.NormalizedLayerScoreStep

namespace OAI

section

namespace Erdos3

structure LayerResetScales (s r : ℕ) (L : ℝ) where
  threshold : ℕ → ℕ
  cellScale : ℕ → ℕ
  score : ℕ → ℝ
  constant : ℕ → ℝ
  exponent : ℕ → ℕ
  score_pos : ∀ h ≤ s + 1, 0 < score h
  constant_nonneg : ∀ h ≤ s, 0 ≤ constant h
  partition : ∀ h ≤ s, PolynomialCoordinatePartitionBound.{0} h (constant h) (exponent h)
  cell_pos : ∀ h ≤ s, 0 < cellScale h
  scale_bound : ∀ h ≤ s, constant h * ((r : ℝ) + 1) ≤ cellScale h
  power_bound : ∀ h ≤ s, cellScale h ^ (exponent h * (r + 1) ^ (2 * h)) ≤ threshold h
  lift_error : ∀ h ≤ s, (2 : ℝ) ^ (h + 1) * ((h : ℝ) / cellScale h) < 1
  freeze_error : ∀ h ≤ s, (r : ℝ) * (2 * ((h : ℝ) / cellScale h)) < 1 / 12
  score_error : ∀ h ≤ s, 8 * L * r * h ≤ score h * cellScale h
  score_next : ∀ h ≤ s, score (h + 1) ≤ score h / 2
  length_bound : ∀ h ≤ s, (threshold (h + 1) : ℝ) ≤
    score h * cellScale h / (2 : ℝ) ^ (h + 3)

end Erdos3

end

section

namespace Erdos3

def layerResetThreshold (s B T h : ℕ) : ℕ := T ^ ((2 * B) ^ (s + 1 - h))

def layerResetCellScale (s B T h : ℕ) : ℕ := T ^ (2 * (2 * B) ^ (s - h))

@[simp] theorem layerResetThreshold_terminal (s B T : ℕ) :
    layerResetThreshold s B T (s + 1) = T := by simp [layerResetThreshold]

@[simp] theorem layerResetThreshold_initial (s B T : ℕ) :
    layerResetThreshold s B T 1 = T ^ ((2 * B) ^ s) := by simp [layerResetThreshold]

theorem layerResetThreshold_pos {s B T h : ℕ} (hT : 0 < T) :
    0 < layerResetThreshold s B T h := pow_pos hT _

theorem layerResetThreshold_ge {s B T h : ℕ} (hB : 0 < B) (hT : 0 < T) :
    T ≤ layerResetThreshold s B T h := by
  exact (Nat.pow_one T).symm.trans_le
    (Nat.pow_le_pow_right hT (by exact Nat.one_le_iff_ne_zero.mpr (ne_of_gt (pow_pos (by omega) _))))

theorem layerResetCellScale_sq {s B T h : ℕ} :
    layerResetCellScale s B T h = (layerResetThreshold s B T (h + 1)) ^ 2 := by
  have heq : s + 1 - (h + 1) = s - h := by omega
  simp only [layerResetCellScale, layerResetThreshold, heq, ← pow_mul]
  congr 1
  omega

theorem layerResetCellScale_ge {s B T h : ℕ} (hB : 0 < B) (hT : 0 < T) :
    T ≤ layerResetCellScale s B T h := by
  rw [layerResetCellScale_sq]
  exact (layerResetThreshold_ge hB hT).trans
    ((Nat.pow_one _).symm.trans_le (Nat.pow_le_pow_right (layerResetThreshold_pos hT) (by omega)))

theorem layerResetCellScale_power {s B T h : ℕ} (hh : h ≤ s) :
    layerResetCellScale s B T h ^ B = layerResetThreshold s B T h := by
  have heq : s + 1 - h = (s - h) + 1 := by omega
  simp only [layerResetCellScale, layerResetThreshold, heq, ← pow_mul, pow_succ]
  congr 1
  ring

theorem layerReset_exponent_polynomial (s p r : ℕ) :
    (2 * (p * (r + 1) ^ (2 * s))) ^ s = (2 * p) ^ s * (r + 1) ^ (2 * s * s) := by
  rw [← mul_assoc, mul_pow, ← pow_mul]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace LayerResetScales

theorem reset_from {s r : ℕ} {L : ℝ} (S : LayerResetScales s r L)
    (m h : ℕ) (hh : 0 < h) (hlevel : h + m = s + 1)
    {d N : ℕ} (A : PolynomialPatch Unit s d) (hrank : d ≤ r)
    (hlip : (A.kernel.lip : ℝ) ≤ L) (hweight : ∀ i, h ≤ A.weight i)
    (hN : S.threshold h ≤ N) (f : ℕ → ℝ)
    (hf : ∀ n < N, f n ∈ Set.Icc (0 : ℝ) 1)
    {b : ℝ} (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (hscore : S.score h ≤ 𝔼 n : Fin N, (f n.val - b) * A.value (fun _ => (n.val : ℝ))) :
    ∃ q a len : ℕ, 0 < q ∧ S.threshold (s + 1) ≤ len ∧
      (∀ n < len, a + q * n < N) ∧ b < 𝔼 n : Fin len, f (a + q * n.val) := by
  induction m generalizing h d N f with
  | zero =>
    have heq : h = s + 1 := by omega
    have hd : d = 0 := by
      by_contra hn
      have hi : 0 < d := Nat.pos_of_ne_zero hn
      have hlo := hweight ⟨0, hi⟩
      have hhi := A.weight_le ⟨0, hi⟩
      omega
    subst d
    have hNpos : 0 < N := by
      by_contra hn
      have hz : N = 0 := by omega
      subst N
      have hs := S.score_pos h (by omega)
      have hz : S.score h ≤ 0 := by simpa using hscore
      exact (not_le_of_gt hs) hz
    let : NeZero N := ⟨hNpos.ne'⟩
    have hc : 0 ≤ A.kernel.value 0 := by
      simpa only [PolynomialPatch.value_rank_zero] using (A.value_mem_Icc (fun _ => 0)).1
    have hmean : 0 < (𝔼 n : Fin N, f n.val) - b := by
      have hs := (S.score_pos h (by omega)).trans_le hscore
      simp only [PolynomialPatch.value_rank_zero, ← Finset.expect_mul,
        Finset.expect_sub_distrib, Fintype.expect_const] at hs
      by_contra hn
      exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hc)) hs
    refine ⟨1, 0, N, by omega, ?_, ?_, ?_⟩
    · simpa only [heq] using hN
    · intro n hn
      simpa using hn
    · simpa using (show b < 𝔼 n : Fin N, f n.val by linarith)
  | succ m ih =>
    have hhs : h ≤ s := by omega
    obtain ⟨D, hD, hhead, htail⟩ := monotone_weight_layer A.weight A.weight_mono hweight
    obtain ⟨E, rfl⟩ := Nat.exists_eq_add_of_le hD
    have hDr : D ≤ r := by omega
    have hDrR : (D : ℝ) ≤ r := by exact_mod_cast hDr
    have hscale : S.constant h * ((D : ℝ) + 1) ≤ S.cellScale h :=
      (mul_le_mul_of_nonneg_left (by linarith : (D : ℝ) + 1 ≤ r + 1)
        (S.constant_nonneg h hhs)).trans (S.scale_bound h hhs)
    have hsize : S.cellScale h ^ (S.exponent h * (D + 1) ^ (2 * h)) ≤ N := by
      apply le_trans (Nat.pow_le_pow_right (S.cell_pos h hhs)
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hDr 1) _)))
      exact (S.power_bound h hhs).trans hN
    have hfreeze : (D : ℝ) * (2 * ((h : ℝ) / S.cellScale h)) < 1 / 12 :=
      (mul_le_mul_of_nonneg_right hDrR (by positivity)).trans_lt (S.freeze_error h hhs)
    have hroom : 8 * (A.kernel.lip : ℝ) * D * h ≤ S.score h * S.cellScale h := by
      apply le_trans _ (S.score_error h hhs)
      have hprod := mul_le_mul hlip hDrR (by positivity : (0 : ℝ) ≤ D)
        (A.kernel.lip.coe_nonneg.trans hlip)
      nlinarith [mul_le_mul_of_nonneg_right hprod (Nat.cast_nonneg (α := ℝ) h)]
    let model := A.lowestLayerModel hh (fun i => hhead (i.castAdd E) i.isLt)
    obtain ⟨q, a, len, F, hq, hlen, hin, hFlip, hFw, hretained⟩ :=
      (S.partition h hhs).layer_score_step A model (S.cell_pos h hhs) hscale hsize
        (S.lift_error h hhs) hfreeze f hf hb (S.score_pos h (by omega)) hroom hscore
    have hnext : S.threshold (h + 1) ≤ len := by
      exact_mod_cast (S.length_bound h hhs).trans hlen
    have hw : ∀ i, h + 1 ≤ F.weight i := by
      intro i
      rw [hFw]
      exact htail _ (by simp)
    obtain ⟨q', a', len', hq', hlen', hin', hdense⟩ := ih (h + 1) (by omega) (by omega)
      F (by omega) (by simpa only [hFlip] using hlip) hw hnext
      (fun n => f (a + q * n)) (fun n hn => hf _ (hin n hn))
      ((S.score_next h hhs).trans hretained.le)
    refine ⟨q * q', a + q * a', len', Nat.mul_pos hq hq', hlen', ?_, ?_⟩
    · intro n hn
      convert hin (a' + q' * n) (hin' n hn) using 1
      ring
    · convert hdense using 1
      congr 1
      funext n
      congr 1
      ring

theorem density_increment {s r : ℕ} {L : ℝ} (S : LayerResetScales s r L)
    {d N : ℕ} (A : PolynomialPatch Unit s d) (hrank : d ≤ r)
    (hlip : (A.kernel.lip : ℝ) ≤ L) (hN : S.threshold 1 ≤ N)
    (f : ℕ → ℝ) (hf : ∀ n < N, f n ∈ Set.Icc (0 : ℝ) 1)
    {b : ℝ} (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (hscore : S.score 1 ≤ 𝔼 n : Fin N, (f n.val - b) * A.value (fun _ => (n.val : ℝ))) :
    ∃ q a len : ℕ, 0 < q ∧ S.threshold (s + 1) ≤ len ∧
      (∀ n < len, a + q * n < N) ∧ b < 𝔼 n : Fin len, f (a + q * n.val) :=
  S.reset_from s 1 (by omega) (by omega) A hrank hlip A.weight_pos hN f hf hb hscore

end LayerResetScales
end Erdos3

end

section

namespace Erdos3

noncomputable def powerLayerResetScales {s r T p : ℕ} {K L σ : ℝ}
    (hp : 0 < p) (hK : 0 ≤ K) (hL : 0 ≤ L) (hT : 0 < T) (hσ : 0 < σ)
    (hpartition : ∀ h ≤ s, PolynomialCoordinatePartitionBound.{0} h K p)
    (hscale : K * ((r : ℝ) + 1) ≤ T)
    (hlift : (2 : ℝ) ^ (s + 1) * s < T)
    (hfreeze : 24 * (r : ℝ) * s < T)
    (hroom : 8 * L * r * s * (2 : ℝ) ^ s ≤ σ * T)
    (hlength : (2 : ℝ) ^ (2 * s + 3) ≤ σ * T) : LayerResetScales s r L := by
  let B := p * (r + 1) ^ (2 * s)
  have hB : 0 < B := Nat.mul_pos hp (pow_pos (by omega) _)
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hge (h : ℕ) : (T : ℝ) ≤ layerResetCellScale s B T h := by
    exact_mod_cast layerResetCellScale_ge (h := h) hB hT
  have hcell (h : ℕ) : (0 : ℝ) < layerResetCellScale s B T h := hT0.trans_le (hge h)
  have hprod (h : ℕ) (hh : h ≤ s) (x : ℝ) (hx : (T : ℝ) ≤ x) :
      σ * T / (2 : ℝ) ^ s ≤ (σ / (2 : ℝ) ^ h) * x := by
    have hdiv : σ / (2 : ℝ) ^ s ≤ σ / (2 : ℝ) ^ h :=
      div_le_div_of_nonneg_left hσ.le (by positivity)
        (pow_le_pow_right₀ (by norm_num) hh)
    calc
      _ = (σ / (2 : ℝ) ^ s) * T := by ring
      _ ≤ _ := mul_le_mul hdiv hx hT0.le (by positivity)
  refine {
    threshold := layerResetThreshold s B T
    cellScale := layerResetCellScale s B T
    score := fun h => σ / (2 : ℝ) ^ h
    constant := fun _ => K
    exponent := fun _ => p
    score_pos := fun h _ => div_pos hσ (by positivity)
    constant_nonneg := fun _ _ => hK
    partition := hpartition
    cell_pos := fun h _ => hT.trans_le (layerResetCellScale_ge hB hT)
    scale_bound := fun h _ => hscale.trans (hge h)
    power_bound := ?_
    lift_error := ?_
    freeze_error := ?_
    score_error := ?_
    score_next := ?_
    length_bound := ?_
  }
  · intro h hh
    have he : p * (r + 1) ^ (2 * h) ≤ B :=
      Nat.mul_le_mul_left p (Nat.pow_le_pow_right (by omega) (by omega))
    exact (Nat.pow_le_pow_right (hT.trans_le (layerResetCellScale_ge hB hT)) he).trans_eq
      (layerResetCellScale_power hh)
  · intro h hh
    rw [← mul_div_assoc]
    apply (div_lt_one (hcell h)).mpr
    calc
      _ ≤ (2 : ℝ) ^ (s + 1) * s := mul_le_mul
        (pow_le_pow_right₀ (by norm_num) (by omega)) (by exact_mod_cast hh)
        (by positivity) (by positivity)
      _ < T := hlift
      _ ≤ _ := hge h
  · intro h hh
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 12)).mpr
    rw [show (r : ℝ) * (2 * ((h : ℝ) / layerResetCellScale s B T h)) * 12 =
      (24 * r * h) / layerResetCellScale s B T h by ring]
    apply (div_lt_one (hcell h)).mpr
    calc
      _ ≤ 24 * (r : ℝ) * s := mul_le_mul_of_nonneg_left (by exact_mod_cast hh) (by positivity)
      _ < T := hfreeze
      _ ≤ _ := hge h
  · intro h hh
    calc
      _ ≤ 8 * L * r * s := mul_le_mul_of_nonneg_left (by exact_mod_cast hh) (by positivity)
      _ ≤ σ * T / (2 : ℝ) ^ s := (le_div_iff₀ (by positivity)).mpr hroom
      _ ≤ _ := hprod h hh _ (hge h)
  · intro h _
    simp only [pow_succ, div_div]
    exact le_rfl
  · intro h hh
    let A := layerResetThreshold s B T (h + 1)
    have hA : (T : ℝ) ≤ A := by exact_mod_cast layerResetThreshold_ge (h := h + 1) hB hT
    have hc : (2 : ℝ) ^ (h + 3) ≤ (σ / (2 : ℝ) ^ h) * A := by
      calc
        _ ≤ (2 : ℝ) ^ (s + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
        _ ≤ σ * T / (2 : ℝ) ^ s := by
          apply (le_div_iff₀ (by positivity)).mpr
          simpa only [← pow_add, show s + 3 + s = 2 * s + 3 by omega] using hlength
        _ ≤ _ := hprod h hh _ hA
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ (h + 3))).mpr
    rw [layerResetCellScale_sq, Nat.cast_pow]
    change (A : ℝ) * 2 ^ (h + 3) ≤ (σ / 2 ^ h) * A ^ 2
    nlinarith [mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg (α := ℝ) A)]

end Erdos3

end

end OAI

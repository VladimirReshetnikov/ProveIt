import OAI.Combinatorics.Progressions.Dynamics.ReplacementCellPotential
import OAI.Combinatorics.Progressions.FixedDensity.Conclusions
import OAI.Combinatorics.Progressions.FixedDensity.CountExtraction
import OAI.Combinatorics.Progressions.FixedDensity.ShortInterval

namespace OAI

section

namespace Erdos3

noncomputable def densityParameter (α : ℝ) : ℝ := max 2 (Real.log (2 / α))

theorem densityParameter_ge_two (α : ℝ) : 2 ≤ densityParameter α := le_max_left _ _

theorem densityParameter_drop {α α' G p δ : ℝ}
    (hα : 0 < α) (hG : 0 < G) (hgain : G * α ≤ α')
    (hp : Real.log (2 / α) ≤ p) (hδ : δ ≤ Real.log G) (hroom : 2 ≤ p - δ) :
    densityParameter α' ≤ p - δ := by
  have hα' : 0 < α' := (mul_pos hG hα).trans_le hgain
  apply max_le hroom
  have hratio : 2 / α' ≤ 2 / (G * α) :=
    div_le_div_of_nonneg_left (by norm_num) (mul_pos hG hα) hgain
  have hlog := Real.log_le_log (by positivity : 0 < 2 / α') hratio
  have heq : Real.log (2 / (G * α)) = Real.log (2 / α) - Real.log G := by
    rw [Real.log_div (by norm_num) (mul_ne_zero hG.ne' hα.ne'),
      Real.log_mul hG.ne' hα.ne', Real.log_div (by norm_num) hα.ne']
    ring
  rw [heq] at hlog
  linarith

theorem selected_amplification_log_gain {κ H₀ K p : ℝ}
    (hκ : 0 < κ) (hH : 1 < κ * H₀) (hK : 1 < K) (hp : 1 ≤ p) :
    p ^ gainExponent K * (Real.log (κ * H₀) / 2) - Real.log 2 ≤
      Real.log (κ * amplificationGain κ H₀ ⌊levelCoefficient K * Real.log p⌋₊ / 2) := by
  have hbase : 0 < κ * H₀ := by linarith
  have hid : κ * amplificationGain κ H₀ ⌊levelCoefficient K * Real.log p⌋₊ =
      (κ * H₀) ^ (2 ^ ⌊levelCoefficient K * Real.log p⌋₊) := by
    rw [amplificationGain_closed hκ.ne']
    field_simp
  rw [Real.log_div (by rw [hid]; positivity) (by norm_num), hid, Real.log_pow]
  have hlow := mul_le_mul_of_nonneg_right (gain_base_at_selected_level hK hp).1
    (Real.log_nonneg hH.le)
  norm_cast at hlow ⊢
  linarith

end Erdos3

end

section

namespace Erdos3

theorem density_le_exp_sub_parameter {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    α ≤ Real.exp (2 - densityParameter α) := by
  have hlogα : Real.log α ≤ 0 := Real.log_nonpos hα.le hα1
  have hlog2 : Real.log 2 ≤ 2 := (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
  have hp : densityParameter α ≤ 2 - Real.log α := by
    apply max_le (by linarith)
    rw [Real.log_div (by norm_num) hα.ne']
    linarith
  exact (Real.log_le_iff_le_exp hα).mp (by linarith)

theorem density_parameter_ge_of_invariant_failure {α A β C L : ℝ}
    (hA : 0 < A) (hβ : 0 < β) (hL : 0 ≤ L) (hC : 2 * C ≤ L)
    (hfail : L < A * densityParameter α ^ β + C) :
    (1 / (2 * A)) ^ (1 / β) * L ^ (1 / β) ≤ densityParameter α := by
  have hp : 0 < densityParameter α := by linarith [densityParameter_ge_two α]
  have hpower : L / (2 * A) ≤ densityParameter α ^ β := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hroot := Real.rpow_le_rpow (div_nonneg hL (by positivity)) hpower (by positivity : 0 ≤ 1 / β)
  have heq : (densityParameter α ^ β) ^ (1 / β) = densityParameter α := by
    rw [← Real.rpow_mul hp.le, mul_one_div_cancel hβ.ne', Real.rpow_one]
  rw [heq] at hroot
  have hleft : (L / (2 * A)) ^ (1 / β) = (1 / (2 * A)) ^ (1 / β) * L ^ (1 / β) := by
    rw [show L / (2 * A) = (1 / (2 * A)) * L by ring,
      Real.mul_rpow (by positivity) hL]
  rwa [hleft] at hroot

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def intervalIndicator (S : Finset ℕ) (n : ℕ) : ℝ := if n ∈ S then 1 else 0

noncomputable def intervalDensity (N : ℕ) (S : Finset ℕ) : ℝ := S.card / (N : ℝ)

theorem intervalIndicator_mem_Icc (S : Finset ℕ) (n : ℕ) :
    intervalIndicator S n ∈ Set.Icc (0 : ℝ) 1 := by
  unfold intervalIndicator
  split <;> norm_num

theorem mean_intervalIndicator {N : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.range N) :
    (𝔼 n : Fin N, intervalIndicator S n.val) = intervalDensity N S := by
  classical
  rw [Fintype.expect_eq_sum_div_card, Fintype.card_fin]
  have hfilter : (Finset.range N).filter (fun n => n ∈ S) = S := by
    ext n
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hS h, h⟩⟩
  have hsum : (∑ n : Fin N, intervalIndicator S n.val) = (S.card : ℝ) := by
    rw [Fin.sum_univ_eq_sum_range]
    simp only [intervalIndicator, ← Finset.sum_filter, Finset.sum_const,
      nsmul_eq_mul, mul_one, hfilter]
  rw [hsum]
  rfl

theorem intervalDensity_pos {N : ℕ} {S : Finset ℕ} (hN : 0 < N) (hS : S.Nonempty) :
    0 < intervalDensity N S :=
  div_pos (by exact_mod_cast Finset.card_pos.mpr hS) (by exact_mod_cast hN)

theorem intervalDensity_le_one {N : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.range N) :
    intervalDensity N S ≤ 1 := by
  have hcard : S.card ≤ N := (Finset.card_le_card hS).trans_eq (Finset.card_range N)
  exact div_le_one_of_le₀ (by exact_mod_cast hcard) (Nat.cast_nonneg N)

def progressionPreimage (S : Finset ℕ) (a q M : ℕ) : Finset ℕ :=
  (Finset.range M).filter fun n => a + q * n ∈ S

theorem progressionPreimage_subset (S : Finset ℕ) (a q M : ℕ) :
    progressionPreimage S a q M ⊆ Finset.range M := Finset.filter_subset _ _

theorem APFree.progressionPreimage {S : Finset ℕ} {k : ℕ} (hS : APFree (S : Set ℕ) k)
    (a q M : ℕ) (hq : 0 < q) : APFree (progressionPreimage S a q M : Set ℕ) k := by
  apply (hS.affine_preimage a q hq).mono
  intro n hn
  exact (Finset.mem_filter.mp hn).2

theorem mean_progression_indicator (S : Finset ℕ) (a q M : ℕ) :
    (𝔼 n : Fin M, intervalIndicator S (a + q * n.val)) =
      intervalDensity M (progressionPreimage S a q M) := by
  rw [← mean_intervalIndicator (progressionPreimage_subset S a q M)]
  apply Finset.expect_congr rfl
  intro n _
  simp only [intervalIndicator, progressionPreimage, Finset.mem_filter, Finset.mem_range,
    n.isLt, true_and]

theorem intervalDensity_pos_iff {N : ℕ} {S : Finset ℕ} (hN : 0 < N) :
    0 < intervalDensity N S ↔ S.Nonempty := by
  constructor
  · intro h
    by_contra hn
    have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp [he, intervalDensity] at h
  · exact intervalDensity_pos hN

end Erdos3

end

section

namespace Erdos3

open Filter

theorem eventually_sublinear_drop_room {ν c : ℝ} (hν : ν < 1) :
    ∀ᶠ p : ℝ in atTop, 2 ≤ p - c * p ^ ν := by
  have hgrowth := (tendsto_rpow_atTop (sub_pos.mpr hν)).eventually_ge_atTop (2 * c)
  filter_upwards [hgrowth, eventually_ge_atTop (4 : ℝ)] with p hp hp4
  have hp0 : 0 < p := by linarith
  have hmul := mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hp0.le ν)
  have heq : p ^ (1 - ν) * p ^ ν = p := by
    rw [← Real.rpow_add hp0, sub_add_cancel, Real.rpow_one]
  rw [heq] at hmul
  linarith

theorem exists_selected_density_drop {κ H₀ K : ℝ}
    (hκ : 0 < κ) (hH : 1 < κ * H₀) (hK : 2 ≤ K) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ p : ℝ in atTop,
      c * p ^ gainExponent K ≤
        Real.log (κ * amplificationGain κ H₀ ⌊levelCoefficient K * Real.log p⌋₊ / 2) ∧
      2 ≤ p - c * p ^ gainExponent K := by
  let c := Real.log (κ * H₀) / 4
  have hc : 0 < c := div_pos (Real.log_pos hH) (by norm_num)
  obtain ⟨hν, hν4⟩ := gainExponent_pos_le_quarter hK
  have hroom := eventually_sublinear_drop_room (c := c) (by linarith : gainExponent K < 1)
  have hlarge := (tendsto_rpow_atTop hν).eventually_ge_atTop (Real.log 2 / c)
  refine ⟨c, hc, ?_⟩
  filter_upwards [hroom, hlarge, eventually_ge_atTop (1 : ℝ)] with p hroom hlarge hp
  refine ⟨?_, hroom⟩
  have hgain := selected_amplification_log_gain hκ hH (by linarith : 1 < K) hp
  have hlog2 : Real.log 2 ≤ c * p ^ gainExponent K := by
    have h := (div_le_iff₀ hc).mp hlarge
    simpa only [mul_comm] using h
  dsimp only [c] at hlog2 ⊢
  nlinarith

end Erdos3

end

section

namespace Erdos3.FixedDensity

theorem exists_naturalAP_of_cyclicAPVal_shortInterval
    {A : Set ℕ} {k N : ℕ} [NeZero N]
    (a d : ZMod N) (hd : d ≠ 0) (hk : 2 ≤ k)
    (L U : ℤ)
    (hinterval :
      ∀ j : ℕ, j < k →
        L ≤ cyclicAPVal a d j ∧ cyclicAPVal a d j ≤ U)
    (hwidth : 2 * (U - L) < (N : ℤ))
    (hA : ∀ j : ℕ, j < k → cyclicAPVal a d j ∈ A) :
    ∃ x step : ℕ, 1 ≤ step ∧
      ∀ j : ℕ, j < k → x + step * j ∈ A := by
  obtain ⟨s, hs, haffine⟩ :=
    cyclicAPVal_isIntegerAP a d hd L U hinterval hwidth
  rcases lt_or_gt_of_ne hs with hsneg | hspos
  · let step : ℕ := (-s).toNat
    have hstep_cast : (step : ℤ) = -s := by
      exact Int.natCast_toNat_eq_self.mpr (neg_nonneg.mpr hsneg.le)
    have hstep_pos : 0 < step := by omega
    refine ⟨cyclicAPVal a d (k - 1), step, hstep_pos, ?_⟩
    intro j hj
    have hlast : k - 1 < k := by omega
    have hrev : k - 1 - j < k := by omega
    have hindex :
        ((k - 1 - j : ℕ) : ℤ) = (k - 1 : ℕ) - (j : ℤ) := by
      omega
    have hterm :
        cyclicAPVal a d (k - 1) + step * j =
          cyclicAPVal a d (k - 1 - j) := by
      apply Int.ofNat_inj.mp
      push_cast
      rw [hstep_cast, haffine (k - 1) hlast,
        haffine (k - 1 - j) hrev, hindex]
      ring
    rw [hterm]
    exact hA (k - 1 - j) hrev
  · let step : ℕ := s.toNat
    have hstep_cast : (step : ℤ) = s := by
      exact Int.natCast_toNat_eq_self.mpr hspos.le
    have hstep_pos : 0 < step := by omega
    refine ⟨cyclicAPVal a d 0, step, hstep_pos, ?_⟩
    intro j hj
    have hterm :
        cyclicAPVal a d 0 + step * j = cyclicAPVal a d j := by
      apply Int.ofNat_inj.mp
      push_cast
      rw [hstep_cast, haffine j hj]
      ring
    rw [hterm]
    exact hA j hj

end Erdos3.FixedDensity

namespace Erdos3

open FixedDensity

noncomputable def cyclicIntervalSet (S : Finset ℕ) (m : ℕ) [NeZero m] : Finset (ZMod m) := by
  classical
  exact Finset.univ.filter fun x => x.val ∈ S

theorem cyclicIntervalSet_card {S : Finset ℕ} {N m : ℕ} [NeZero m]
    (hS : S ⊆ Finset.range N) (hNm : N ≤ m) : (cyclicIntervalSet S m).card = S.card := by
  classical
  symm
  apply Finset.card_bij (fun (x : ℕ) _ => (x : ZMod m))
  · intro x hx
    have hxm : x < m := (Finset.mem_range.mp (hS hx)).trans_le hNm
    simpa only [cyclicIntervalSet, Finset.mem_filter, Finset.mem_univ, true_and,
      ZMod.val_natCast_of_lt hxm] using hx
  · intro x hx y hy hxy
    have hxm : x < m := (Finset.mem_range.mp (hS hx)).trans_le hNm
    have hym : y < m := (Finset.mem_range.mp (hS hy)).trans_le hNm
    simpa only [ZMod.val_natCast_of_lt hxm, ZMod.val_natCast_of_lt hym] using
      congrArg (ZMod.val : ZMod m → ℕ) hxy
  · intro z hz
    have hzS : z.val ∈ S := (Finset.mem_filter.mp hz).2
    exact ⟨z.val, hzS, ZMod.natCast_zmod_val z⟩

theorem fixed_density_hasAP (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀, ∀ S : Finset ℕ,
      S ⊆ Finset.range N → δ * N ≤ (S.card : ℝ) → HasAP (S : Set ℕ) k := by
  classical
  let K := max 2 k
  obtain ⟨c, hc, hcount⟩ := FixedDensity.szemeredi K (le_max_left _ _)
    (div_pos hδ (by norm_num : (0 : ℝ) < 4))
  let N₀ := ⌈1 / c⌉₊ + 1
  refine ⟨N₀, by dsimp [N₀]; omega, ?_⟩
  intro N hN S hS hdensity
  have hN0 : 0 < N := by dsimp [N₀] at hN; omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  have hNc : 1 / c < (N : ℝ) := by
    have hlo := Nat.le_ceil (1 / c)
    have hhi : (⌈1 / c⌉₊ : ℝ) + 1 ≤ N := by exact_mod_cast hN
    linarith
  let m := 4 * N
  let : NeZero m := ⟨by dsimp [m]; omega⟩
  let T := cyclicIntervalSet S m
  have hNm : N ≤ m := by dsimp [m]; omega
  have hmR : (0 : ℝ) < m := by dsimp [m]; positivity
  have hmean : δ / 4 ≤ mean (finsetIndicator T) := by
    rw [mean_finsetIndicator, cyclicIntervalSet_card hS hNm, ZMod.card]
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 4) hmR).mpr
    dsimp [m]
    push_cast
    nlinarith
  have hcyclic := hcount m T hmean
  have hf0 : ∀ x : ZMod m, 0 ≤ finsetIndicator T x := by
    intro x
    unfold finsetIndicator
    split <;> norm_num
  have hf1 : ∀ x : ZMod m, finsetIndicator T x ≤ 1 := by
    intro x
    unfold finsetIndicator
    split <;> norm_num
  have hmean1 : mean (finsetIndicator T) ≤ 1 := mean_le_of_le_const hf1
  have hmc : 1 < (m : ℝ) * c := by
    have hNc' := (div_lt_iff₀ hc).mp hNc
    have hNmR : (N : ℝ) ≤ m := by exact_mod_cast hNm
    exact hNc'.trans_le (mul_le_mul_of_nonneg_right hNmR hc.le)
  have hoff : 0 < cyclicAPOffDiagMass K m (finsetIndicator T) := by
    apply cyclicAPOffDiagMass_pos_of_count (by dsimp [K]; omega) hf0 hf1
    calc
      _ = mean (finsetIndicator T) := by simp
      _ ≤ 1 := hmean1
      _ < (m : ℝ) * c := hmc
      _ ≤ _ := mul_le_mul_of_nonneg_left hcyclic hmR.le
  obtain ⟨a, d, hd, hpos⟩ := exists_cyclicAP_of_offDiagMass_pos hf0 hoff
  have hterms (j : ℕ) (hj : j < K) : cyclicAPVal a d j ∈ S := by
    have hpositive := hpos (⟨j, hj⟩ : Fin K)
    have hmem : cyclicAPTerm a d (⟨j, hj⟩ : Fin K) ∈ T := by
      by_contra hn
      rw [finsetIndicator_of_not_mem hn] at hpositive
      linarith
    simpa only [T, cyclicIntervalSet, Finset.mem_filter, Finset.mem_univ, true_and,
      cyclicAPVal, cyclicAPTerm] using hmem
  have hinterval : ∀ j < K, (0 : ℤ) ≤ cyclicAPVal a d j ∧ (cyclicAPVal a d j : ℤ) ≤ N := by
    intro j hj
    have hlt := Finset.mem_range.mp (hS (hterms j hj))
    exact ⟨by positivity, by exact_mod_cast hlt.le⟩
  have hwidth : 2 * ((N : ℤ) - 0) < (m : ℤ) := by dsimp [m]; omega
  obtain ⟨a', d', hd', hAP⟩ := exists_naturalAP_of_cyclicAPVal_shortInterval
    a d hd (le_max_left _ _) 0 N hinterval hwidth hterms
  refine ⟨a', d', by omega, ?_⟩
  intro j hj
  simpa only [mul_comm] using hAP j (hj.trans_le (le_max_right 2 k))

end Erdos3

end

section

namespace Erdos3

theorem exp_neg_le_density_of_parameter_le {α T : ℝ}
    (hα : 0 < α) (hT : densityParameter α ≤ T) : Real.exp (-T) ≤ α := by
  have hlog : Real.log (2 / α) ≤ T := (le_max_right _ _).trans hT
  rw [Real.log_div (by norm_num) hα.ne'] at hlog
  apply (Real.le_log_iff_exp_le hα).mp
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  linarith

theorem fixed_density_terminal (k : ℕ) (T : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (S : Finset ℕ), 1 < N →
      S ⊆ Finset.range N → APFree (S : Set ℕ) k → S.Nonempty →
      densityParameter (intervalDensity N S) ≤ T → C ≤ Real.log (Real.log N) → False := by
  obtain ⟨N₀, _, hN₀⟩ := fixed_density_hasAP k (Real.exp_pos (-T))
  let M := max 2 N₀
  have hM1 : (1 : ℝ) < M := by exact_mod_cast (show 1 < M by dsimp [M]; omega)
  let C := max 0 (Real.log (Real.log M))
  refine ⟨C, le_max_left _ _, ?_⟩
  intro N S hN hS hfree hnonempty hp hsize
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hMNlog : Real.log M ≤ Real.log N :=
    (Real.log_le_log_iff (Real.log_pos hM1) (Real.log_pos hN1)).mp
      ((le_max_right _ _).trans hsize)
  have hMNreal : (M : ℝ) ≤ N :=
    (Real.log_le_log_iff (by linarith) (by linarith)).mp hMNlog
  have hMN : M ≤ N := by exact_mod_cast hMNreal
  have hN₀N : N₀ ≤ N := (le_max_right 2 N₀).trans hMN
  have hα : 0 < intervalDensity N S := intervalDensity_pos (by omega) hnonempty
  have hdensity := exp_neg_le_density_of_parameter_le hα hp
  have hcard : Real.exp (-T) * N ≤ (S.card : ℝ) :=
    (le_div_iff₀ (by linarith : (0 : ℝ) < N)).mp hdensity
  exact hfree (hN₀ N hN₀N S hS hcard)

end Erdos3

end

section

namespace Erdos3

structure APFreeInterval (k : ℕ) where
  length : ℕ
  length_gt_one : 1 < length
  points : Finset ℕ
  subset : points ⊆ Finset.range length
  nonempty : points.Nonempty
  free : APFree (points : Set ℕ) k

namespace APFreeInterval

variable {k : ℕ}

noncomputable def density (S : APFreeInterval k) : ℝ := intervalDensity S.length S.points

noncomputable def parameter (S : APFreeInterval k) : ℝ := densityParameter S.density

theorem density_pos (S : APFreeInterval k) : 0 < S.density :=
  intervalDensity_pos (by have := S.length_gt_one; omega) S.nonempty

theorem parameter_ge_two (S : APFreeInterval k) : 2 ≤ S.parameter := densityParameter_ge_two _

def reindex (S : APFreeInterval k) (a q len : ℕ) (hq : 0 < q) (hlen : 1 < len)
    (hpos : 0 < intervalDensity len (progressionPreimage S.points a q len)) : APFreeInterval k where
  length := len
  length_gt_one := hlen
  points := progressionPreimage S.points a q len
  subset := progressionPreimage_subset _ _ _ _
  nonempty := (intervalDensity_pos_iff (by omega)).mp hpos
  free := S.free.progressionPreimage a q len hq

end APFreeInterval

theorem no_interval_invariant_of_descent (k : ℕ) (T Cmin : ℝ) :
    ∃ C₀ : ℝ, Cmin ≤ C₀ ∧ 0 ≤ C₀ ∧ ∀ A β : ℝ, 0 ≤ A →
      (∀ S : APFreeInterval k, A * S.parameter ^ β + C₀ ≤ Real.log (Real.log S.length) →
        T < S.parameter → ∃ S' : APFreeInterval k,
          A * S'.parameter ^ β + C₀ ≤ Real.log (Real.log S'.length) ∧
          S'.parameter + 1 ≤ S.parameter) →
      ∀ S : APFreeInterval k, ¬ A * S.parameter ^ β + C₀ ≤ Real.log (Real.log S.length) := by
  obtain ⟨C, hC, hterminal⟩ := fixed_density_terminal k T
  refine ⟨max Cmin C, le_max_left _ _, hC.trans (le_max_right _ _), ?_⟩
  intro A β hA hstep
  apply no_invariant_of_descent
    (P := fun S : APFreeInterval k => A * S.parameter ^ β + max Cmin C ≤ Real.log (Real.log S.length))
    APFreeInterval.parameter T
  · intro S _
    linarith [S.parameter_ge_two]
  · intro S hinvariant hsmall
    apply hterminal S.length S.points S.length_gt_one S.subset S.free S.nonempty hsmall
    have hnonneg : 0 ≤ A * S.parameter ^ β := mul_nonneg hA (Real.rpow_nonneg (by linarith [S.parameter_ge_two]) _)
    have hreserve : C ≤ max Cmin C := le_max_right _ _
    linarith
  · exact hstep

end Erdos3

end

section

namespace Erdos3

theorem densityParameter_eq_log_of_two_lt {α : ℝ}
    (hp : 2 < densityParameter α) :
    densityParameter α = Real.log (2 / α) := by
  have hlog : 2 < Real.log (2 / α) :=
    (lt_max_iff.mp hp).resolve_left (lt_irrefl 2)
  exact max_eq_right hlog.le

theorem exp_neg_densityParameter_eq_half {α : ℝ}
    (hα : 0 < α) (hp : 2 < densityParameter α) :
    Real.exp (-densityParameter α) = α / 2 := by
  rw [densityParameter_eq_log_of_two_lt hp, Real.exp_neg,
    Real.exp_log (div_pos (by norm_num) hα)]
  simp only [inv_div]

namespace APFreeInterval

theorem exp_neg_parameter_eq_half {k : ℕ} (S : APFreeInterval k)
    (hp : 2 < S.parameter) : Real.exp (-S.parameter) = S.density / 2 :=
  exp_neg_densityParameter_eq_half S.density_pos hp

end APFreeInterval
end Erdos3

end

end OAI

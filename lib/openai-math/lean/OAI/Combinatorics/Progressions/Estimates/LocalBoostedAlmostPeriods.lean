import OAI.Combinatorics.Progressions.Dynamics.CrootSisaskSampleBudget
import OAI.Combinatorics.Progressions.Sampling.CyclicSamplingMoments

namespace OAI

section

namespace Erdos3.CyclicCrootSisask

open Finset
open scoped BigOperators

variable {N : ℕ} [NeZero N]

omit [NeZero N] in
theorem setAverageTranslate_sub (A : Finset (ZMod N)) (f g : ZMod N → ℝ) (x : ZMod N) :
    setAverageTranslate A (fun y => f y - g y) x =
      setAverageTranslate A f x - setAverageTranslate A g x := by
  simp only [setAverageTranslate, Finset.sum_sub_distrib, sub_div]

omit [NeZero N] in
theorem setAverageTranslate_rightTranslate (A : Finset (ZMod N)) (f : ZMod N → ℝ) (x t : ZMod N) :
    setAverageTranslate A (fun y => f (y + t)) x = setAverageTranslate A f (x + t) := by
  unfold setAverageTranslate
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  change f (x - a + t) = f (x + t - a)
  rw [show x - a + t = x + t - a by abel]

omit [NeZero N] in
theorem setAverageTranslate_abs_pow_le {A : Finset (ZMod N)} (hA : A.Nonempty)
    (f : ZMod N → ℝ) (x : ZMod N) (n : ℕ) :
    |setAverageTranslate A f x| ^ n ≤ (∑ a ∈ A, |f (x - a)| ^ n) / A.card := by
  have hc : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  cases n with
  | zero => simp [hc.ne']
  | succ n =>
    have habs : |setAverageTranslate A f x| ≤ (∑ a ∈ A, |f (x - a)|) / A.card := by
      rw [setAverageTranslate, abs_div, abs_of_pos hc]
      exact div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) hc.le
    have hj := pow_sum_div_card_le_sum_pow (s := A) (fun a _ => abs_nonneg (f (x - a))) n
    calc
      _ ≤ ((∑ a ∈ A, |f (x - a)|) / A.card) ^ (n + 1) :=
        pow_le_pow_left₀ (abs_nonneg _) habs _
      _ = (∑ a ∈ A, |f (x - a)|) ^ (n + 1) / (A.card : ℝ) ^ n / A.card := by
        rw [div_pow, pow_succ (A.card : ℝ) n, div_mul_eq_div_div]
      _ ≤ _ := div_le_div_of_nonneg_right hj hc.le

theorem setAverageTranslate_abs_pow_le_total {A : Finset (ZMod N)} (hA : A.Nonempty)
    (f : ZMod N → ℝ) (x : ZMod N) (n : ℕ) :
    |setAverageTranslate A f x| ^ n ≤ (∑ y, |f y| ^ n) / A.card := by
  apply (setAverageTranslate_abs_pow_le hA f x n).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  calc
    _ ≤ ∑ y, |f (x - y)| ^ n := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ A) (fun _ _ _ => by positivity)
    _ = _ := Fintype.sum_equiv (Equiv.subLeft x) _ _ (fun _ => rfl)

theorem convolution_period_moment_bound {L : Finset (ZMod N)} (hL : L.Nonempty)
    (u : ZMod N → ℝ) (t x : ZMod N) (n : ℕ) {E : ℝ}
    (hperiod : ∑ y, |u (y + t) - u y| ^ n ≤ E) :
    |setAverageTranslate L u (x + t) - setAverageTranslate L u x| ^ n ≤ E / L.card := by
  have h := setAverageTranslate_abs_pow_le_total hL (fun y => u (y + t) - u y) x n
  rw [setAverageTranslate_sub, setAverageTranslate_rightTranslate] at h
  exact h.trans (div_le_div_of_nonneg_right hperiod (Nat.cast_nonneg _))

def realSetIndicator (M : Finset (ZMod N)) (x : ZMod N) : ℝ := if x ∈ M then 1 else 0

theorem sum_realSetIndicator_moment (M : Finset (ZMod N)) {n : ℕ} (hn : n ≠ 0) :
    (∑ x, |realSetIndicator M x| ^ n) = (M.card : ℝ) := by
  have hp (x : ZMod N) : |realSetIndicator M x| ^ n = if x ∈ M then 1 else 0 := by
    by_cases hx : x ∈ M <;> simp [realSetIndicator, hx, hn]
  simp only [hp]
  simp

theorem triple_period_moment_bound {L : Finset (ZMod N)} (hL : L.Nonempty)
    (A M : Finset (ZMod N)) (t x : ZMod N) {n : ℕ} (hn : n ≠ 0) {epsilon : ℝ}
    (hperiod : ∑ y,
      |setAverageTranslate A (realSetIndicator M) (y + t) -
        setAverageTranslate A (realSetIndicator M) y| ^ n ≤
          epsilon ^ n * ∑ y, |realSetIndicator M y| ^ n) :
    |setAverageTranslate L (setAverageTranslate A (realSetIndicator M)) (x + t) -
      setAverageTranslate L (setAverageTranslate A (realSetIndicator M)) x| ^ n ≤
        epsilon ^ n * ((M.card : ℝ) / L.card) := by
  have h := convolution_period_moment_bound hL
    (setAverageTranslate A (realSetIndicator M)) t x n hperiod
  simpa only [sum_realSetIndicator_moment M hn, mul_div_assoc] using h

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.CyclicCrootSisask

open Finset
open scoped BigOperators

local notation:70 s:70 " ^^ " n:71 => Fintype.piFinset fun _ : Fin n ↦ s

theorem half_card_le_filter_of_sum_le {ι : Type*} (S : Finset ι) (g : ι → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hg : ∀ a ∈ S, 0 ≤ g a)
    (htotal : ∑ a ∈ S, g a ≤ (1 / 2 : ℝ) * C * S.card) :
    (S.card : ℝ) / 2 ≤ (S.filter (fun a => g a ≤ C)).card := by
  classical
  by_cases hpos : 0 < C
  · have h := markov_card_good hpos hg htotal
    norm_num at h
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using h
  · have hzero : C = 0 := le_antisymm (not_lt.mp hpos) hC
    have hsum : ∑ a ∈ S, g a = 0 := by
      apply le_antisymm
      · simpa only [hzero, mul_zero, zero_mul] using htotal
      · exact Finset.sum_nonneg hg
    have hpoint := (Finset.sum_eq_zero_iff_of_nonneg hg).mp hsum
    have hfilter : S.filter (fun a => g a ≤ C) = S := by
      apply Finset.filter_eq_self.mpr
      intro a ha
      rw [hpoint a ha, hzero]
    rw [hfilter]
    have : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
    linarith

variable {N k m : ℕ} [NeZero N]

theorem half_samples_good_input_moment {A : Finset (ZMod N)} (hA : A.Nonempty)
    (f : ZMod N → ℝ) (hm : m ≠ 0) :
    (A.card : ℝ) ^ k / 2 ≤
      (goodSamples A f k m (samplingMomentCost m k * ∑ x, |f x| ^ (2 * m))).card := by
  let C := samplingMomentCost m k * ∑ x, |f x| ^ (2 * m)
  have hC : 0 ≤ C := mul_nonneg (samplingMomentCost_nonneg _ _)
    (Finset.sum_nonneg (fun _ _ => by positivity))
  have htotal : ∑ a ∈ A ^^ k, ∑ x, |sampleDeviation A f a x| ^ (2 * m) ≤
      (1 / 2 : ℝ) * C * (A ^^ k).card := by
    apply (global_sampleDeviation_input_moment (k := k) hA f hm).trans_eq
    simp only [C, samplingMomentCost, Fintype.card_piFinset_const, Nat.cast_pow]
    ring
  have h := half_card_le_filter_of_sum_le (A ^^ k)
    (fun a => ∑ x, |sampleDeviation A f a x| ^ (2 * m)) hC
    (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity)) htotal
  simpa only [goodSamples, C, Fintype.card_piFinset_const, Nat.cast_pow] using h

theorem goodSamples_relative_moment_bound {A : Finset (ZMod N)} {f : ZMod N → ℝ}
    (hm : 0 < m) (hk : 0 < k) {epsilon : ℝ}
    (hsize : 256 * (m : ℝ) ≤ epsilon ^ 2 * k)
    {a : Fin k → ZMod N} {t : ZMod N}
    (ha : a ∈ goodSamples A f k m (samplingMomentCost m k * ∑ x, |f x| ^ (2 * m)))
    (hat : (a - fun _ => t) ∈
      goodSamples A f k m (samplingMomentCost m k * ∑ x, |f x| ^ (2 * m))) :
    ∑ x, |setAverageTranslate A f (x + t) - setAverageTranslate A f x| ^ (2 * m) ≤
      epsilon ^ (2 * m) * ∑ x, |f x| ^ (2 * m) := by
  have hraw := goodSamples_give_almost_period ha hat
  have hbudget := samplingMomentCost_error hm hsize
  have hS : (0 : ℝ) ≤ ∑ x, |f x| ^ (2 * m) := Finset.sum_nonneg (fun _ _ => by positivity)
  have hupper := mul_le_mul_of_nonneg_right hbudget hS
  have hfinal : (k : ℝ) ^ (2 * m) *
      (∑ x, |setAverageTranslate A f (x + t) - setAverageTranslate A f x| ^ (2 * m)) ≤
        (k : ℝ) ^ (2 * m) * (epsilon ^ (2 * m) * ∑ x, |f x| ^ (2 * m)) := by
    apply hraw.trans
    simpa only [mul_assoc] using hupper
  exact le_of_mul_le_mul_left hfinal (pow_pos (by exact_mod_cast hk) _)

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.CyclicCrootSisask

variable {N : ℕ}

noncomputable def convolutionMomentOrder (M L : Finset (ZMod N)) : ℕ :=
  ⌈1 + Real.log (max 1 ((M.card : ℝ) / L.card))⌉₊

theorem convolutionMomentOrder_pos (M L : Finset (ZMod N)) :
    0 < convolutionMomentOrder M L := by
  apply Nat.ceil_pos.mpr
  have h := Real.log_nonneg (le_max_left 1 ((M.card : ℝ) / L.card))
  linarith

theorem cardinal_ratio_le_exp_momentOrder (M L : Finset (ZMod N)) :
    (M.card : ℝ) / L.card ≤ Real.exp (2 * (convolutionMomentOrder M L : ℝ)) := by
  let R : ℝ := max 1 ((M.card : ℝ) / L.card)
  have hR : 0 < R := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hceil : 1 + Real.log R ≤ (convolutionMomentOrder M L : ℝ) := Nat.le_ceil _
  have hm : (0 : ℝ) ≤ convolutionMomentOrder M L := Nat.cast_nonneg _
  calc
    _ ≤ R := le_max_right _ _
    _ = Real.exp (Real.log R) := (Real.exp_log hR).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem convolution_moment_to_pointwise (M L : Finset (ZMod N)) {delta z : ℝ}
    (hdelta : 0 < delta)
    (hz : |z| ^ (2 * convolutionMomentOrder M L) ≤
      (delta / Real.exp 1) ^ (2 * convolutionMomentOrder M L) * ((M.card : ℝ) / L.card)) :
    |z| ≤ delta := by
  let m := convolutionMomentOrder M L
  have hm : 0 < m := convolutionMomentOrder_pos M L
  have hexp : Real.exp (2 * (m : ℝ)) = Real.exp 1 ^ (2 * m) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_one] using Real.exp_nat_mul 1 (2 * m)
  apply le_of_pow_le_pow_left₀ (show 2 * m ≠ 0 by omega) hdelta.le
  calc
    _ ≤ (delta / Real.exp 1) ^ (2 * m) * ((M.card : ℝ) / L.card) := hz
    _ ≤ (delta / Real.exp 1) ^ (2 * m) * Real.exp (2 * (m : ℝ)) :=
      mul_le_mul_of_nonneg_left (cardinal_ratio_le_exp_momentOrder M L) (by positivity)
    _ = delta ^ (2 * m) := by
      rw [hexp, div_pow, div_mul_cancel₀ _ (pow_ne_zero _ (Real.exp_ne_zero _))]

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.CyclicCrootSisask

open Finset
open scoped BigOperators

variable {N : ℕ}

theorem setAverageTranslate_approx_of_shifts {A : Finset (ZMod N)} (hA : A.Nonempty)
    (u : ZMod N → ℝ) {delta : ℝ}
    (hshift : ∀ t ∈ A, ∀ x, |u (x + t) - u x| ≤ delta) (x : ZMod N) :
    |setAverageTranslate A u x - u x| ≤ delta := by
  have hc : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have heq : setAverageTranslate A u x - u x =
      (∑ t ∈ A, (u (x - t) - u x)) / A.card := by
    rw [setAverageTranslate, Finset.sum_sub_distrib, sub_div]
    simp only [Finset.sum_const, nsmul_eq_mul]
    field_simp
  have hpoint (t : ZMod N) (ht : t ∈ A) : |u (x - t) - u x| ≤ delta := by
    have h := hshift t ht (x - t)
    simpa only [sub_add_cancel, abs_sub_comm] using h
  rw [heq, abs_div, abs_of_pos hc]
  calc
    _ ≤ (∑ t ∈ A, |u (x - t) - u x|) / A.card :=
      div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) hc.le
    _ ≤ (∑ _t ∈ A, delta) / A.card :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum hpoint) hc.le
    _ = delta := by simp [hc.ne']

noncomputable def iteratedSetAverage (A : Finset (ZMod N)) (u : ZMod N → ℝ) :
    ℕ → ZMod N → ℝ
  | 0 => u
  | n + 1 => setAverageTranslate A (iteratedSetAverage A u n)

theorem iteratedSetAverage_uniform_error {A : Finset (ZMod N)} (hA : A.Nonempty)
    (u : ZMod N → ℝ) {delta : ℝ} (hdelta : 0 ≤ delta)
    (hstep : ∀ x, |setAverageTranslate A u x - u x| ≤ delta) (n : ℕ) :
    ∀ x, |iteratedSetAverage A u n x - u x| ≤ n * delta := by
  induction n with
  | zero => intro x; simp [iteratedSetAverage]
  | succ n ih =>
    intro x
    change |setAverageTranslate A (iteratedSetAverage A u n) x - u x| ≤ _
    have herror : |setAverageTranslate A (iteratedSetAverage A u n) x - setAverageTranslate A u x| ≤
        n * delta := by
      rw [← setAverageTranslate_sub]
      exact abs_setAverageTranslate_le hA (fun y => iteratedSetAverage A u n y - u y)
        (mul_nonneg (Nat.cast_nonneg _) hdelta) ih x
    calc
      _ = |(setAverageTranslate A (iteratedSetAverage A u n) x - setAverageTranslate A u x) +
          (setAverageTranslate A u x - u x)| := by congr 1; ring
      _ ≤ |setAverageTranslate A (iteratedSetAverage A u n) x - setAverageTranslate A u x| +
          |setAverageTranslate A u x - u x| := abs_add_le _ _
      _ ≤ n * delta + delta := add_le_add herror (hstep x)
      _ = _ := by push_cast; ring

theorem iteratedSetAverage_approx_of_shifts {A : Finset (ZMod N)} (hA : A.Nonempty)
    (u : ZMod N → ℝ) {delta : ℝ} (hdelta : 0 ≤ delta)
    (hshift : ∀ t ∈ A, ∀ x, |u (x + t) - u x| ≤ delta) (n : ℕ) (x : ZMod N) :
    |iteratedSetAverage A u n x - u x| ≤ n * delta :=
  iteratedSetAverage_uniform_error hA u hdelta (setAverageTranslate_approx_of_shifts hA u hshift) n x

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.CyclicCrootSisask

open Finset
open scoped BigOperators Pointwise

local notation:70 s:70 " ^^ " n:71 => Fintype.piFinset fun _ : Fin n ↦ s

variable {N : ℕ} [NeZero N]

theorem exists_local_almostPeriods {A S : Finset (ZMod N)}
    (hA : A.Nonempty) (hS : S.Nonempty) (f : ZMod N → ℝ)
    {m : ℕ} (hm : 0 < m) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    let k := crootSisaskSampleSize m epsilon
    ∃ T : Finset (ZMod N), T ⊆ S ∧ T.Nonempty ∧
      (((A.card : ℝ) ^ k / 2 * S.card) / ((A + S).card : ℝ) ^ k ≤ T.card) ∧
      ∀ s ∈ T, ∀ t ∈ T,
        ∑ x, |setAverageTranslate A f (x + (t - s)) - setAverageTranslate A f x| ^ (2 * m) ≤
          epsilon ^ (2 * m) * ∑ x, |f x| ^ (2 * m) := by
  classical
  intro k
  let C := samplingMomentCost m k * ∑ x, |f x| ^ (2 * m)
  let L := goodSamples A f k m C
  have hhalf : (A.card : ℝ) ^ k / 2 ≤ L.card := half_samples_good_input_moment hA f hm.ne'
  have hLpos : (0 : ℝ) < L.card :=
    (div_pos (pow_pos (by exact_mod_cast hA.card_pos) _) (by norm_num)).trans_le hhalf
  have hL : L.Nonempty := Finset.card_pos.mp (by exact_mod_cast hLpos)
  have hLA : L ⊆ A ^^ k := Finset.filter_subset _ _
  obtain ⟨x, T, hTS, hT, hcount, hgood⟩ := exists_local_shift_fiber hA hS L hL hLA
  refine ⟨T, hTS, hT, ?_, ?_⟩
  · apply le_trans _ hcount
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hhalf (Nat.cast_nonneg _)) (by positivity)
  · intro s hs t ht
    have hbase : (x - fun _ => s) ∈ goodSamples A f k m C := hgood s hs
    have hshift : ((x - fun _ => s) - fun _ => t - s) ∈ goodSamples A f k m C := by
      have heq : ((x - fun _ => s) - fun _ => t - s) = x - fun _ => t := by
        funext i
        simp only [Pi.sub_apply]
        abel
      rw [heq]
      exact hgood t ht
    exact goodSamples_relative_moment_bound hm (crootSisaskSampleSize_pos hm hepsilon)
      (crootSisaskSampleSize_bound m hepsilon) hbase hshift

theorem exists_local_almostPeriods_of_smallDoubling {A S : Finset (ZMod N)}
    (hA : A.Nonempty) (hS : S.Nonempty) (f : ZMod N → ℝ)
    {m : ℕ} (hm : 0 < m) {epsilon K : ℝ} (hepsilon : 0 < epsilon) (hK : 0 < K)
    (hdoubling : ((A + S).card : ℝ) ≤ K * A.card) :
    let k := crootSisaskSampleSize m epsilon
    ∃ T : Finset (ZMod N), T ⊆ S ∧ T.Nonempty ∧
      (S.card : ℝ) / (2 * K ^ k) ≤ T.card ∧
      ∀ s ∈ T, ∀ t ∈ T,
        ∑ x, |setAverageTranslate A f (x + (t - s)) - setAverageTranslate A f x| ^ (2 * m) ≤
          epsilon ^ (2 * m) * ∑ x, |f x| ^ (2 * m) := by
  intro k
  obtain ⟨T, hTS, hT, hcount, halmost⟩ := exists_local_almostPeriods hA hS f hm hepsilon
  refine ⟨T, hTS, hT, ?_, halmost⟩
  have hApos : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hsumpos : (0 : ℝ) < (A + S).card := by exact_mod_cast (hA.add hS).card_pos
  have hden : 0 < ((A + S).card : ℝ) ^ k := pow_pos hsumpos _
  have hKden : 0 < 2 * K ^ k := mul_pos (by norm_num) (pow_pos hK _)
  apply le_trans _ hcount
  apply (div_le_div_iff₀ hKden hden).mpr
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg _) hdoubling k
  have hmul := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg S.card : (0 : ℝ) ≤ S.card)
  calc
    _ ≤ (S.card : ℝ) * (K * A.card) ^ k := hmul
    _ = _ := by rw [mul_pow]; ring

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.CyclicCrootSisask

open scoped BigOperators Pointwise

variable {N : ℕ} [NeZero N]

theorem exists_local_triple_almostPeriods {A S L : Finset (ZMod N)}
    (hA : A.Nonempty) (hS : S.Nonempty) (hL : L.Nonempty)
    (M : Finset (ZMod N)) {delta : ℝ} (hdelta : 0 < delta) :
    let m := convolutionMomentOrder M L
    let k := crootSisaskSampleSize m (delta / Real.exp 1)
    ∃ T : Finset (ZMod N), T ⊆ S ∧ T.Nonempty ∧
      (((A.card : ℝ) ^ k / 2 * S.card) / ((A + S).card : ℝ) ^ k ≤ T.card) ∧
      ∀ s ∈ T, ∀ t ∈ T, ∀ x : ZMod N,
        |setAverageTranslate L (setAverageTranslate A (realSetIndicator M)) (x + (t - s)) -
          setAverageTranslate L (setAverageTranslate A (realSetIndicator M)) x| ≤ delta := by
  intro m k
  obtain ⟨T, hTS, hT, hcount, hperiod⟩ := exists_local_almostPeriods hA hS (realSetIndicator M)
    (convolutionMomentOrder_pos M L) (div_pos hdelta (Real.exp_pos _))
  refine ⟨T, hTS, hT, hcount, ?_⟩
  intro s hs t ht x
  apply convolution_moment_to_pointwise M L hdelta
  exact triple_period_moment_bound hL A M (t - s) x
    (show 2 * m ≠ 0 by have := convolutionMomentOrder_pos M L; dsimp only [m]; omega)
    (hperiod s hs t ht)

theorem exists_local_triple_almostPeriods_of_smallDoubling {A S L : Finset (ZMod N)}
    (hA : A.Nonempty) (hS : S.Nonempty) (hL : L.Nonempty)
    (M : Finset (ZMod N)) {delta K : ℝ} (hdelta : 0 < delta) (hK : 0 < K)
    (hdoubling : ((A + S).card : ℝ) ≤ K * A.card) :
    let m := convolutionMomentOrder M L
    let k := crootSisaskSampleSize m (delta / Real.exp 1)
    ∃ T : Finset (ZMod N), T ⊆ S ∧ T.Nonempty ∧
      (S.card : ℝ) / (2 * K ^ k) ≤ T.card ∧
      ∀ s ∈ T, ∀ t ∈ T, ∀ x : ZMod N,
        |setAverageTranslate L (setAverageTranslate A (realSetIndicator M)) (x + (t - s)) -
          setAverageTranslate L (setAverageTranslate A (realSetIndicator M)) x| ≤ delta := by
  intro m k
  obtain ⟨T, hTS, hT, hcount, hperiod⟩ := exists_local_almostPeriods_of_smallDoubling
    hA hS (realSetIndicator M) (convolutionMomentOrder_pos M L)
    (div_pos hdelta (Real.exp_pos _)) hK hdoubling
  refine ⟨T, hTS, hT, hcount, ?_⟩
  intro s hs t ht x
  apply convolution_moment_to_pointwise M L hdelta
  exact triple_period_moment_bound hL A M (t - s) x
    (show 2 * m ≠ 0 by have := convolutionMomentOrder_pos M L; dsimp only [m]; omega)
    (hperiod s hs t ht)

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.CyclicCrootSisask

open Finset
open scoped BigOperators Pointwise

variable {N : ℕ} [NeZero N]

theorem exists_local_boosted_triple_almostPeriods {A S L : Finset (ZMod N)}
    (hA : A.Nonempty) (hS : S.Nonempty) (hL : L.Nonempty)
    (M : Finset (ZMod N)) (q : ℕ) (hq : 0 < q) {delta : ℝ} (hdelta : 0 < delta) :
    let m := convolutionMomentOrder M L
    let k := crootSisaskSampleSize m ((delta / q) / Real.exp 1)
    let u := setAverageTranslate L (setAverageTranslate A (realSetIndicator M))
    ∃ (T X : Finset (ZMod N)) (z : ZMod N), T ⊆ S ∧ z ∈ T ∧
      X = T.map (Equiv.subRight z).toEmbedding ∧ 0 ∈ X ∧ X ⊆ S - S ∧
      (((A.card : ℝ) ^ k / 2 * S.card) / ((A + S).card : ℝ) ^ k ≤ T.card) ∧
      ∀ x, |iteratedSetAverage X u q x - u x| ≤ delta := by
  intro m k u
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hdeltaq : 0 < delta / (q : ℝ) := div_pos hdelta hqR
  obtain ⟨T, hTS, hT, hcount, hperiod⟩ := exists_local_triple_almostPeriods hA hS hL M hdeltaq
  obtain ⟨z, hz⟩ := hT
  let X := T.map (Equiv.subRight z).toEmbedding
  have hzero : (0 : ZMod N) ∈ X := by
    apply Finset.mem_map.mpr
    exact ⟨z, hz, sub_self z⟩
  have hXS : X ⊆ S - S := by
    intro t ht
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp ht
    exact Finset.sub_mem_sub (hTS ha) (hTS hz)
  refine ⟨T, X, z, hTS, hz, rfl, hzero, hXS, hcount, ?_⟩
  have hshift : ∀ t ∈ X, ∀ x, |u (x + t) - u x| ≤ delta / (q : ℝ) := by
    intro t ht x
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp ht
    exact hperiod z hz a ha x
  intro x
  have h := iteratedSetAverage_approx_of_shifts (show X.Nonempty from ⟨0, hzero⟩)
    u hdeltaq.le hshift q x
  have hcancel : (q : ℝ) * (delta / q) = delta := by field_simp
  exact h.trans_eq hcancel

end Erdos3.CyclicCrootSisask

end

end OAI

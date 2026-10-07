import Mathlib.Data.Fintype.EquivFin
import Mathlib.Topology.MetricSpace.Lipschitz
import OAI.Combinatorics.Progressions.Dynamics.CandidateFrontSourceLossBudget
import OAI.Combinatorics.Progressions.Estimates.NormalizedCutoffs
import OAI.Combinatorics.Progressions.Sampling.NormalizedRealBoxHalfGrid

namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {ι X : Type*} [Fintype ι] [PseudoMetricSpace X]

theorem metric_cover_of_box_grid (f : (ι → ℝ) → X) {K : ℝ≥0} {B : ℝ} (hB : 0 < B)
    (hLip : LipschitzOnWith K f {v | ∀ i, |v i| ≤ B})
    (hcover : ∀ x, ∃ v, (∀ i, |v i| ≤ B) ∧ f v = x) (N : ℕ) (hN : 0 < N) :
    ∀ x, ∃ k : ι → Fin (N + 1),
      dist x (f (uniformBoxGrid B N k)) ≤ K * (2 * B / N) := by
  intro x
  obtain ⟨v, hv, rfl⟩ := hcover x
  obtain ⟨k, hk⟩ := exists_uniformBoxGrid_approx hB hN v hv
  refine ⟨k, ?_⟩
  exact (hLip.dist_le_mul v hv _ (uniformBoxGrid_mem hB.le hN k)).trans
    (mul_le_mul_of_nonneg_left hk K.coe_nonneg)

noncomputable def boxCoverMeshCount (B : ℝ) (K : ℝ≥0) (ε : ℝ) : ℕ :=
  ⌈2 * B * K / ε⌉₊ + 1

theorem boxCoverMeshCount_pos (B : ℝ) (K : ℝ≥0) (ε : ℝ) : 0 < boxCoverMeshCount B K ε := by
  unfold boxCoverMeshCount
  omega

theorem boxCoverMeshCount_error {B ε : ℝ} (K : ℝ≥0) (hε : 0 < ε) :
    K * (2 * B / boxCoverMeshCount B K ε) ≤ ε := by
  have hN : (0 : ℝ) < boxCoverMeshCount B K ε := by exact_mod_cast boxCoverMeshCount_pos B K ε
  have hceil : 2 * B * K / ε ≤ (boxCoverMeshCount B K ε : ℝ) := by
    exact (Nat.le_ceil _).trans (by unfold boxCoverMeshCount; push_cast; linarith)
  have hm := (div_le_iff₀ hε).mp hceil
  rw [← mul_div_assoc, div_le_iff₀ hN]
  nlinarith

theorem exists_finite_metric_cover_of_box (f : (ι → ℝ) → X) {K : ℝ≥0} {B ε : ℝ}
    (hB : 0 < B) (hε : 0 < ε) (hLip : LipschitzOnWith K f {v | ∀ i, |v i| ≤ B})
    (hcover : ∀ x, ∃ v, (∀ i, |v i| ≤ B) ∧ f v = x) :
    ∃ c : (ι → Fin (boxCoverMeshCount B K ε + 1)) → X,
      ∀ x, ∃ i, dist x (c i) ≤ ε := by
  refine ⟨fun i => f (uniformBoxGrid B (boxCoverMeshCount B K ε) i), ?_⟩
  intro x
  obtain ⟨i, hi⟩ := metric_cover_of_box_grid f hB hLip hcover _ (boxCoverMeshCount_pos B K ε) x
  exact ⟨i, hi.trans (boxCoverMeshCount_error K hε)⟩

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {X : Type*} [PseudoMetricSpace X]

noncomputable def metricTent (c : X) (r : ℝ) (x : X) : ℝ := max 0 (2 * r - dist x c)

theorem metricTent_nonneg (c : X) (r : ℝ) (x : X) : 0 ≤ metricTent c r x := le_max_left _ _

theorem metricTent_le (c : X) {r : ℝ} (hr : 0 ≤ r) (x : X) : metricTent c r x ≤ 2 * r :=
  max_le (by linarith) (by linarith [dist_nonneg (x := x) (y := c)])

theorem metricTent_zero_of_far (c x : X) {r : ℝ} (hx : 2 * r ≤ dist x c) : metricTent c r x = 0 := by
  exact max_eq_left (by linarith)

theorem abs_metricTent_sub_le (c : X) (r : ℝ) (x y : X) :
    |metricTent c r x - metricTent c r y| ≤ dist x y := by
  calc
    _ = |max (2 * r - dist x c) 0 - max (2 * r - dist y c) 0| := by
      simp only [metricTent, max_comm]
    _ ≤ |(2 * r - dist x c) - (2 * r - dist y c)| := abs_max_sub_max_le_abs _ _ _
    _ = |dist x c - dist y c| := by
      rw [show (2 * r - dist x c) - (2 * r - dist y c) = -(dist x c - dist y c) by ring, abs_neg]
    _ ≤ dist x y := abs_dist_sub_le x y c

theorem lipschitz_metricTent (c : X) (r : ℝ) : LipschitzWith 1 (metricTent c r) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using abs_metricTent_sub_le c r x y

variable {ι : Type*} [Fintype ι]

noncomputable def metricTentSum (c : ι → X) (r : ℝ) (x : X) : ℝ := ∑ i, metricTent (c i) r x

theorem metricTentSum_ge (c : ι → X) {r : ℝ} (hcover : ∀ x, ∃ i, dist x (c i) ≤ r) (x : X) :
    r ≤ metricTentSum c r x := by
  obtain ⟨i, hi⟩ := hcover x
  calc
    r ≤ metricTent (c i) r x := (by linarith : r ≤ 2 * r - dist x (c i)).trans (le_max_right _ _)
    _ ≤ metricTentSum c r x := Finset.single_le_sum (fun j _ => metricTent_nonneg (c j) r x) (Finset.mem_univ i)

theorem abs_metricTentSum_sub_le (c : ι → X) (r : ℝ) (x y : X) :
    |metricTentSum c r x - metricTentSum c r y| ≤ Fintype.card ι * dist x y := by
  unfold metricTentSum
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |metricTent (c i) r x - metricTent (c i) r y| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, dist x y := Finset.sum_le_sum fun i _ => abs_metricTent_sub_le (c i) r x y
    _ = _ := by simp

noncomputable def metricTentPartition (c : ι → X) (r : ℝ) (i : ι) (x : X) : ℝ :=
  metricTent (c i) r x / metricTentSum c r x

theorem metricTentPartition_nonneg (c : ι → X) (r : ℝ) (i : ι) (x : X) :
    0 ≤ metricTentPartition c r i x :=
  div_nonneg (metricTent_nonneg _ _ _) (Finset.sum_nonneg fun j _ => metricTent_nonneg (c j) r x)

theorem sum_metricTentPartition (c : ι → X) {r : ℝ} (hr : 0 < r)
    (hcover : ∀ x, ∃ i, dist x (c i) ≤ r) (x : X) : ∑ i, metricTentPartition c r i x = 1 := by
  simp only [metricTentPartition, ← Finset.sum_div]
  exact div_self (hr.trans_le (metricTentSum_ge c hcover x)).ne'

theorem metricTentPartition_le_one (c : ι → X) {r : ℝ} (hr : 0 < r)
    (hcover : ∀ x, ∃ i, dist x (c i) ≤ r) (i : ι) (x : X) : metricTentPartition c r i x ≤ 1 := by
  rw [← sum_metricTentPartition c hr hcover x]
  exact Finset.single_le_sum (fun j _ => metricTentPartition_nonneg c r j x) (Finset.mem_univ i)

theorem metricTentPartition_zero_of_far (c : ι → X) (r : ℝ) (i : ι) (x : X)
    (hx : 2 * r ≤ dist x (c i)) : metricTentPartition c r i x = 0 := by
  simp only [metricTentPartition, metricTent_zero_of_far (c i) x hx, zero_div]

theorem abs_metricTentPartition_sub_le (c : ι → X) {r : ℝ} (hr : 0 < r)
    (hcover : ∀ x, ∃ i, dist x (c i) ≤ r) (i : ι) (x y : X) :
    |metricTentPartition c r i x - metricTentPartition c r i y| ≤
      ((2 * Fintype.card ι + 1) / r) * dist x y := by
  have h := abs_div_sub_div_bound hr (metricTentSum_ge c hcover x) (metricTentSum_ge c hcover y)
    dist_nonneg (by positivity : 0 ≤ 2 * r) (by positivity : 0 ≤ (Fintype.card ι : ℝ) * dist x y)
    (abs_metricTent_sub_le (c i) r x y)
    (by simpa only [abs_of_nonneg (metricTent_nonneg _ _ _)] using metricTent_le (c i) hr.le y)
    (abs_metricTentSum_sub_le c r x y)
  apply h.trans_eq
  field_simp
  ring

theorem lipschitz_metricTentPartition (c : ι → X) {r : ℝ≥0} (hr : 0 < r)
    (hcover : ∀ x, ∃ i, dist x (c i) ≤ r) (i : ι) :
    LipschitzWith ((2 * Fintype.card ι + 1) / r) (metricTentPartition c r i) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [Real.dist_eq, NNReal.coe_div, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_one,
    NNReal.coe_ofNat] using abs_metricTentPartition_sub_le c (show (0 : ℝ) < r from hr) hcover i x y

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem boxCoverMeshCount_add_one_le_exp {B ε p : ℝ} (K : ℝ≥0)
    (hB0 : 0 ≤ B) (hε : 0 < ε) (hp : 0 ≤ p)
    (hB : B ≤ Real.exp p) (hK : (K : ℝ) ≤ Real.exp p) (hεinv : 1 / ε ≤ Real.exp p) :
    ((boxCoverMeshCount B K ε + 1 : ℕ) : ℝ) ≤ Real.exp (3 * p + 4) := by
  have hprod : 2 * B * K / ε ≤ 2 * Real.exp (3 * p) := by
    calc
      _ = 2 * (B * K * (1 / ε)) := by ring
      _ ≤ 2 * (Real.exp p * Real.exp p * Real.exp p) := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 2; ring
  have hceil := (Nat.ceil_lt_add_one (by positivity : 0 ≤ 2 * B * K / ε)).le
  have hone : 1 ≤ Real.exp (3 * p) := Real.one_le_exp (by linarith)
  have hfive : (5 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  calc
    _ ≤ 5 * Real.exp (3 * p) := by
      unfold boxCoverMeshCount
      push_cast
      linarith
    _ ≤ Real.exp 4 * Real.exp (3 * p) := mul_le_mul_of_nonneg_right hfive (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem boxCoverCount_le_exp (C d : ℕ) (hC : 2 ≤ C) (K : ℝ≥0) {B ε p : ℝ}
    (hB0 : 0 ≤ B) (hε : 0 < ε) (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p)
    (hB : B ≤ Real.exp ((p + C) ^ C)) (hK : (K : ℝ) ≤ Real.exp ((p + C) ^ C))
    (hεinv : 1 / ε ≤ Real.exp ((p + C) ^ C)) :
    (((boxCoverMeshCount B K ε + 1) ^ d : ℕ) : ℝ) ≤
      Real.exp ((p + (C + 5)) ^ (C + 5)) := by
  let t : ℝ := p + (C + 5 : ℕ)
  have ht : 5 ≤ t := by dsimp [t]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) C]
  have ht1 : 1 ≤ t := by linarith
  have hpt : p ≤ t := by dsimp [t]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) C]
  have hq : (p + C) ^ C ≤ t ^ C :=
    pow_le_pow_left₀ (by positivity) (by dsimp [t]; push_cast; linarith) C
  have hfactor : 3 * (p + C) ^ C + 4 ≤ t ^ (C + 2) := by
    have hpow : 1 ≤ t ^ C := one_le_pow₀ ht1
    have hsquare : 7 ≤ t ^ 2 := by nlinarith
    calc
      _ ≤ 7 * t ^ C := by linarith
      _ ≤ t ^ 2 * t ^ C := mul_le_mul_of_nonneg_right hsquare (by positivity)
      _ = _ := by rw [pow_add]; ring
  have hmesh := boxCoverMeshCount_add_one_le_exp K hB0 hε (by positivity) hB hK hεinv
  rw [Nat.cast_pow]
  calc
    _ ≤ (Real.exp (3 * (p + C) ^ C + 4)) ^ d := pow_le_pow_left₀ (by positivity) hmesh d
    _ = Real.exp ((d : ℝ) * (3 * (p + C) ^ C + 4)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (t * t ^ (C + 2)) := Real.exp_le_exp.mpr
      (mul_le_mul (hd.trans hpt) hfactor (by positivity) (by linarith))
    _ = Real.exp (t ^ (C + 3)) := by rw [show C + 3 = (C + 2) + 1 by omega, pow_succ' t (C + 2)]
    _ ≤ Real.exp (t ^ (C + 5)) := Real.exp_le_exp.mpr (pow_le_pow_right₀ ht1 (by omega))
    _ = _ := by simp [t]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem exists_metric_partition_of_box {ι X : Type*} [Fintype ι] [PseudoMetricSpace X]
    (f : (ι → ℝ) → X) {K : ℝ≥0} {B : ℝ} (hB : 0 < B)
    (hLip : LipschitzOnWith K f {v | ∀ i, |v i| ≤ B})
    (hcover : ∀ x, ∃ v, (∀ i, |v i| ≤ B) ∧ f v = x) (r : ℝ≥0) (hr : 0 < r) :
    let n := (boxCoverMeshCount B K r + 1) ^ Fintype.card ι
    ∃ c : Fin n → X, ∃ ψ : Fin n → X → ℝ,
      (∀ i x, 0 ≤ ψ i x ∧ ψ i x ≤ 1) ∧
      (∀ x, ∑ i, ψ i x = 1) ∧
      (∀ i x, 2 * (r : ℝ) ≤ dist x (c i) → ψ i x = 0) ∧
      (∀ i, LipschitzWith ((2 * n + 1 : ℝ≥0) / r) (ψ i)) := by
  classical
  let N := boxCoverMeshCount B K r
  let n := (N + 1) ^ Fintype.card ι
  let I := ι → Fin (N + 1)
  have hcard : Fintype.card I = n := by simp [I, n]
  let e : I ≃ Fin n := Fintype.equivFinOfCardEq hcard
  obtain ⟨c, hc⟩ := exists_finite_metric_cover_of_box f hB (show (0 : ℝ) < r from hr) hLip hcover
  let centers : Fin n → X := fun i => c (e.symm i)
  have hcenters (x : X) : ∃ i, dist x (centers i) ≤ r := by
    obtain ⟨i, hi⟩ := hc x
    refine ⟨e i, ?_⟩
    simpa only [centers, Equiv.symm_apply_apply] using hi
  refine ⟨centers, metricTentPartition centers r, ?_, ?_, ?_, ?_⟩
  · intro i x
    exact ⟨metricTentPartition_nonneg centers r i x, metricTentPartition_le_one centers hr hcenters i x⟩
  · exact sum_metricTentPartition centers hr hcenters
  · exact metricTentPartition_zero_of_far centers r
  · intro i
    simpa only [Fintype.card_fin] using lipschitz_metricTentPartition centers hr hcenters i

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem shifted_power_self_mono {p : ℝ} (hp : 0 ≤ p) {C D : ℕ} (hC : 1 ≤ C) (hCD : C ≤ D) :
    (p + C) ^ C ≤ (p + D) ^ D := by
  have hD : (1 : ℝ) ≤ D := by exact_mod_cast hC.trans hCD
  apply (pow_le_pow_left₀ (by positivity) (add_le_add le_rfl (Nat.cast_le.mpr hCD)) C).trans
  exact pow_le_pow_right₀ (by linarith) hCD

theorem metricPartition_constant_le_exp (n : ℕ) (r : ℝ≥0) {p : ℝ}
    (hp : 0 ≤ p) (hn : (n : ℝ) ≤ Real.exp p) (hr : 1 / (r : ℝ) ≤ Real.exp p) :
    (((2 * n + 1 : ℝ≥0) / r : ℝ≥0) : ℝ) ≤ Real.exp (2 * p + 2) := by
  have hnum : 2 * (n : ℝ) + 1 ≤ 3 * Real.exp p := by
    linarith [Real.one_le_exp_iff.mpr hp]
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  change (2 * (n : ℝ) + 1) / r ≤ _
  calc
    _ = (2 * (n : ℝ) + 1) * (1 / r) := by ring
    _ ≤ (3 * Real.exp p) * Real.exp p :=
      mul_le_mul hnum hr (by positivity) (by positivity)
    _ = 3 * Real.exp (2 * p) := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    _ ≤ Real.exp 2 * Real.exp (2 * p) := mul_le_mul_of_nonneg_right hthree (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem metricPartition_constant_power_budget (C n : ℕ) (hC : 2 ≤ C) (r : ℝ≥0) {p : ℝ}
    (hp : 0 ≤ p) (hn : (n : ℝ) ≤ Real.exp ((p + C) ^ C))
    (hr : 1 / (r : ℝ) ≤ Real.exp ((p + C) ^ C)) :
    (((2 * n + 1 : ℝ≥0) / r : ℝ≥0) : ℝ) ≤ Real.exp ((p + (C + 3)) ^ (C + 3)) := by
  apply (metricPartition_constant_le_exp n r (by positivity) hn hr).trans
  apply Real.exp_le_exp.mpr
  let t : ℝ := p + (C + 3 : ℕ)
  have ht : 5 ≤ t := by
    have hC' : (2 : ℝ) ≤ C := by exact_mod_cast hC
    dsimp [t]
    push_cast
    linarith
  have hpow : 1 ≤ t ^ C := one_le_pow₀ (by linarith)
  have hq : (p + C) ^ C ≤ t ^ C :=
    pow_le_pow_left₀ (by positivity) (by dsimp [t]; push_cast; linarith) C
  calc
    _ ≤ 4 * t ^ C := by linarith
    _ ≤ t * t ^ C := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = t ^ (C + 1) := (pow_succ' t C).symm
    _ ≤ t ^ (C + 3) := pow_le_pow_right₀ (by linarith) (by omega)
    _ = _ := by simp [t]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem exists_metric_partition_exp_bound {ι X : Type*} [Fintype ι] [PseudoMetricSpace X]
    (f : (ι → ℝ) → X) {K : ℝ≥0} {B p : ℝ} (hB : 0 < B)
    (hLip : LipschitzOnWith K f {v | ∀ i, |v i| ≤ B})
    (hcover : ∀ x, ∃ v, (∀ i, |v i| ≤ B) ∧ f v = x)
    (r : ℝ≥0) (hr : 0 < r) (C : ℕ) (hC : 2 ≤ C)
    (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hBp : B ≤ Real.exp ((p + C) ^ C)) (hKp : (K : ℝ) ≤ Real.exp ((p + C) ^ C))
    (hrp : 1 / (r : ℝ) ≤ Real.exp ((p + C) ^ C)) :
    ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + (C + 8)) ^ (C + 8)) ∧
      ∃ L : ℝ≥0, (L : ℝ) ≤ Real.exp ((p + (C + 8)) ^ (C + 8)) ∧
      ∃ c : Fin n → X, ∃ ψ : Fin n → X → ℝ,
        (∀ i x, 0 ≤ ψ i x ∧ ψ i x ≤ 1) ∧
        (∀ x, ∑ i, ψ i x = 1) ∧
        (∀ i x, 2 * (r : ℝ) ≤ dist x (c i) → ψ i x = 0) ∧
        (∀ i, LipschitzWith L (ψ i)) := by
  let n := (boxCoverMeshCount B K r + 1) ^ Fintype.card ι
  obtain ⟨c, ψ, hψ, hsum, hsupport, hψLip⟩ := exists_metric_partition_of_box f hB hLip hcover r hr
  have hn : (n : ℝ) ≤ Real.exp ((p + (C + 5)) ^ (C + 5)) :=
    boxCoverCount_le_exp C (Fintype.card ι) hC K hB.le hr hp hd hBp hKp hrp
  have hC5 := shifted_power_self_mono (C := C) (D := C + 5) hp (by omega) (by omega)
  have hrp' : 1 / (r : ℝ) ≤ Real.exp ((p + (C + 5)) ^ (C + 5)) :=
    hrp.trans (Real.exp_le_exp.mpr (by simpa only [Nat.cast_add, Nat.cast_ofNat] using hC5))
  have hL := metricPartition_constant_power_budget (C + 5) n (by omega) r hp
    (by simpa only [Nat.cast_add, Nat.cast_ofNat] using hn)
    (by simpa only [Nat.cast_add, Nat.cast_ofNat] using hrp')
  refine ⟨n, by dsimp [n]; positivity, ?_, (2 * n + 1 : ℝ≥0) / r, ?_, c, ψ,
    hψ, hsum, hsupport, hψLip⟩
  · apply hn.trans
    apply Real.exp_le_exp.mpr
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      shifted_power_self_mono (C := C + 5) (D := C + 8) hp (by omega) (by omega)
  · simpa only [Nat.cast_add, Nat.cast_ofNat, Nat.add_assoc, Nat.reduceAdd,
      add_assoc, show (5 : ℝ) + 3 = 8 by norm_num] using hL

end Erdos3

end

end OAI

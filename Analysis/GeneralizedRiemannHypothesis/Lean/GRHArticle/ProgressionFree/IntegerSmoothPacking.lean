import GRHArticle.ProgressionFree.IntegerPrefixTransfer

/-!
# Fractional packings of forbidden triples

Each progression in a packing must lose a vertex. Bounding the load at every
vertex by its reciprocal weight therefore bounds the total mass of a smooth
admissible set, including its infinite tail.
-/

namespace GRHArticle.ProgressionFree

open Finset
open scoped BigOperators

/-- An integral geometric progression and its integer packing weight. -/
structure IntegerPackingTriple where
  first : ℕ
  ratio : ℕ
  weight : ℕ
  deriving DecidableEq

def IntegerPackingTriple.vertices (e : IntegerPackingTriple) : Finset ℕ :=
  {e.first, e.first*e.ratio, e.first*e.ratio*e.ratio}

/-- Total weight incident at a vertex, in units of the chosen common scale. -/
def integerPackingLoad (E : Finset IntegerPackingTriple) (n : ℕ) : ℕ :=
  ∑ e ∈ E, if n ∈ e.vertices then e.weight else 0

open scoped Classical in
private theorem omitted_packing_mass (integral : Bool) (A : Set ℕ)
    (ha : IntegerPrefixAdmissible integral A) (E : Finset IntegerPackingTriple)
    (V : Finset ℕ) (scale : ℕ) (hs : 0 < scale)
    (hE : ∀ e ∈ E, 0 < e.first ∧ 1 < e.ratio ∧ e.vertices ⊆ V)
    (hV : ∀ n ∈ V, 0 < n ∧ n * integerPackingLoad E n ≤ scale) :
    (∑ e ∈ E, e.weight : ℕ) / (scale : ℝ) ≤ ∑ n ∈ V with n ∉ A, (n : ℝ)⁻¹ := by
  classical
  let D := V.filter fun n ↦ n ∉ A
  let w (e : IntegerPackingTriple) (n : ℕ) := if n ∈ e.vertices then e.weight else 0
  have hit (e) (he : e ∈ E) : ∃ n ∈ D, n ∈ e.vertices := by
    obtain ⟨hp, hr, hsub⟩ := hE e he
    have hmem (i) (hi : i ∈ e.vertices) (h : i ∉ A) : ∃ n ∈ D, n ∈ e.vertices :=
      ⟨i, mem_filter.mpr ⟨hsub hi, h⟩, hi⟩
    by_cases h₀ : e.first ∈ A
    · by_cases h₁ : e.first*e.ratio ∈ A
      · apply hmem (e.first*e.ratio*e.ratio) (by simp [IntegerPackingTriple.vertices])
        intro h₂
        exact ha h₀ h₁ h₂ (by simpa only [mul_one] using Nat.mul_lt_mul_of_pos_left hr hp)
          (by simpa only [mul_one] using Nat.mul_lt_mul_of_pos_left hr (mul_pos hp (by omega : 0 < e.ratio))) (by ring) (fun _ ↦ dvd_mul_right ..)
      · exact hmem _ (by simp [IntegerPackingTriple.vertices]) h₁
    · exact hmem _ (by simp [IntegerPackingTriple.vertices]) h₀
  have hle : ∑ e ∈ E, e.weight ≤ ∑ n ∈ D, integerPackingLoad E n := by
    calc
      _ ≤ ∑ e ∈ E, ∑ n ∈ D, w e n := by
        refine sum_le_sum fun e he ↦ ?_
        obtain ⟨n, hn, hv⟩ := hit e he
        simpa only [w, if_pos hv] using (single_le_sum (f := w e) (fun i _ ↦ Nat.zero_le _) hn)
      _ = _ := sum_comm
  have hs' : (0:ℝ) < scale := Nat.cast_pos.mpr hs
  calc
    _ ≤ ((∑ n ∈ D, integerPackingLoad E n : ℕ) : ℝ) / scale :=
      div_le_div_of_nonneg_right (Nat.cast_le.mpr hle) hs'.le
    _ = ∑ n ∈ D, (integerPackingLoad E n : ℝ) / scale := by rw [Nat.cast_sum, sum_div]
    _ ≤ _ := by
      apply sum_le_sum
      intro n hn
      obtain ⟨hp, hcap⟩ := hV n (mem_filter.mp hn).1
      rw [← one_div]
      apply (div_le_div_iff₀ hs' (Nat.cast_pos.mpr hp)).mpr
      rw [one_mul, mul_comm]
      exact_mod_cast hcap

private theorem smooth_reciprocal_add_omitted_le {Y : ℕ} {A : Set ℕ}
    (hA : A ⊆ Nat.smoothNumbers (Y+1)) (D : Finset ℕ)
    (hD : ∀ n ∈ D, n ∈ Nat.smoothNumbers (Y+1) ∧ n ∉ A) :
    (∑' a : A, (a.val:ℝ)⁻¹) + ∑ n ∈ D, (n:ℝ)⁻¹ ≤ (integerSmoothDensityFactor Y)⁻¹ := by
  classical
  let w (n : ℕ) := (n:ℝ)⁻¹
  let S := Nat.smoothNumbers (Y+1)
  have hS : Summable (S.indicator w) := summable_subtype_iff_indicator.mp (summable_reciprocal_smoothNumbers Y)
  have ha : Summable (A.indicator w) := by
    apply hS.of_nonneg_of_le (fun n ↦ Set.indicator_nonneg (fun _ _ ↦ inv_nonneg.mpr (Nat.cast_nonneg _)) _)
    intro n
    by_cases h : n ∈ A
    · simp [h,hA h,S,w]
    · simp [h, Set.indicator_nonneg (s := S) (f := w) (fun _ _ ↦ by dsimp [w]; positivity)]
  have hd : Summable ((D:Set ℕ).indicator w) :=
    summable_of_ne_finset_zero (s := D) fun n hn ↦ Set.indicator_of_notMem hn _
  have hle (n : ℕ) : A.indicator w n + (D:Set ℕ).indicator w n ≤ S.indicator w n := by
    by_cases hn : n ∈ D
    · obtain ⟨hs, hx⟩ := hD n hn
      simp [S,hn,hx,hs]
    · by_cases hx : n ∈ A
      · simp [S,hn,hx,hA hx]
      · simp [hn,hx, Set.indicator_nonneg (s := S) (f := w) (fun _ _ ↦ by dsimp [w]; positivity)]
  have h := (ha.add hd).tsum_le_tsum hle hS
  rw [ha.tsum_add hd, ← _root_.tsum_subtype A w, ← _root_.tsum_subtype (D:Set ℕ) w,
    ← _root_.tsum_subtype S w] at h
  change (∑' a : A, w a.val) + (∑' n : ↥D, w n.val) ≤ ∑' x : S, w x.val at h
  rw [Finset.tsum_subtype D w] at h
  simpa only [w, S, (hasSum_reciprocal_smoothNumbers Y).tsum_eq] using h

/-- A verified fractional packing bounds the full lower smooth optimization
for either ratio convention. -/
theorem integerSmoothLowerOptimization_le_of_packing (integral : Bool) (Y : ℕ)
    (E : Finset IntegerPackingTriple) (V : Finset ℕ) (scale : ℕ) (hs : 0 < scale)
    (hE : ∀ e ∈ E, 0 < e.first ∧ 1 < e.ratio ∧ e.vertices ⊆ V)
    (hV : ∀ n ∈ V, n ∈ Nat.smoothNumbers (Y+1) ∧ n * integerPackingLoad E n ≤ scale) :
    integerSmoothLowerOptimization integral Y ≤
      1 - integerSmoothDensityFactor Y * ((∑ e ∈ E, e.weight : ℕ) / (scale:ℝ)) := by
  classical
  let c := integerSmoothDensityFactor Y
  let P := ((∑ e ∈ E, e.weight : ℕ) / (scale : ℝ))
  have hc : 0 < c := integerSmoothDensityFactor_pos Y
  let weights := {w : ℝ | ∃ A : Set ℕ, A ⊆ Nat.smoothNumbers (Y+1) ∧
      IntegerPrefixAdmissible integral A ∧ w = ∑' a : A, (a.val:ℝ)⁻¹}
  have hw : weights.Nonempty := ⟨_, ∅, Set.empty_subset _, by intro a b c ha; exact ha.elim, rfl⟩
  have hbound : sSup weights ≤ c⁻¹-P := by
    apply csSup_le hw
    rintro _ ⟨A, hA, ha, rfl⟩
    have hm := omitted_packing_mass integral A ha E V scale hs hE (fun n hn ↦
      ⟨Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers (hV n hn).1), (hV n hn).2⟩)
    have hd := smooth_reciprocal_add_omitted_le hA (V.filter fun n ↦ n ∉ A)
      (fun n hn ↦ ⟨(hV n (mem_filter.mp hn).1).1, (mem_filter.mp hn).2⟩)
    dsimp [P,c]
    linarith only [hm, hd]
  have h := mul_le_mul_of_nonneg_left hbound hc.le
  rw [mul_sub, mul_inv_cancel₀ hc.ne'] at h
  exact h

end GRHArticle.ProgressionFree

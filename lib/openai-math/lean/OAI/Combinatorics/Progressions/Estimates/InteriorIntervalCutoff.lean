import OAI.Combinatorics.Progressions.Estimates.CyclicCutNeighborhood
import OAI.Combinatorics.Progressions.Estimates.LinearCutoff
import OAI.Combinatorics.Progressions.Fourier.RectangularGridCharacter

namespace OAI

section

namespace Erdos3

theorem abs_sub_le_of_circle_dist_on_interior {x y η δ : ℝ}
    (hx : η ≤ x ∧ x ≤ 1 - η) (hy : η ≤ y ∧ y ≤ 1 - η)
    (hδ : δ < 2 * η) (hdist : dist (x : CircleFourier.Circle) (y : CircleFourier.Circle) ≤ δ) :
    |x - y| ≤ δ := by
  rw [dist_eq_norm, ← QuotientAddGroup.mk_sub, UnitAddCircle.norm_eq] at hdist
  have hxy : |x - y| ≤ 1 - 2 * η := abs_le.mpr ⟨by linarith, by linarith⟩
  have hz : |(round (x - y) : ℝ)| ≤ |x - y - (round (x - y) : ℝ)| + |x - y| := by
    calc
      _ = |((round (x - y) : ℝ) - (x - y)) + (x - y)| := by ring_nf
      _ ≤ |(round (x - y) : ℝ) - (x - y)| + |x - y| := abs_add_le _ _
      _ = _ := by rw [abs_sub_comm (round (x - y) : ℝ) (x - y)]
  have hzlt : |(round (x - y) : ℝ)| < 1 := by linarith
  have hzlo : (-1 : ℤ) < round (x - y) := by exact_mod_cast (abs_lt.mp hzlt).1
  have hzhi : round (x - y) < (1 : ℤ) := by exact_mod_cast (abs_lt.mp hzlt).2
  have hz0 : round (x - y) = 0 := by omega
  simpa only [hz0, Int.cast_zero, sub_zero] using hdist

theorem same_side_of_cut_of_small_displacement {x y c ρ : ℝ}
    (hxy : |x - y| ≤ ρ) (hgap : ρ < |x - c|) : (c ≤ x ↔ c ≤ y) := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hxy
  by_cases hcx : c ≤ x
  · rw [abs_of_nonneg (sub_nonneg.mpr hcx)] at hgap
    have hcy : c ≤ y := by linarith
    simp only [hcx, hcy]
  · rw [abs_of_neg (sub_neg.mpr (lt_of_not_ge hcx))] at hgap
    have hcy : ¬c ≤ y := by linarith
    simp only [hcx, hcy]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem abs_sub_positive_sum_le {A : Type*} [Fintype A]
    (w c : A → ℝ) (t error : ℝ) (hw : ∀ a, 0 ≤ w a) (hsum : ∑ a, w a = 1)
    (herr : ∀ a, 0 < w a → |t - c a| ≤ error) :
    |t - ∑ a, w a * c a| ≤ error := by
  have hid : t - ∑ a, w a * c a = ∑ a, w a * (t - c a) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]
  rw [hid]
  calc
    _ ≤ ∑ a, |w a * (t - c a)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, w a * error := by
      apply Finset.sum_le_sum
      intro a _
      rw [abs_mul, abs_of_nonneg (hw a)]
      rcases (hw a).eq_or_lt with ha | ha
      · rw [← ha, zero_mul, zero_mul]
      · exact mul_le_mul_of_nonneg_left (herr a ha) (hw a)
    _ = error := by rw [← Finset.sum_mul, hsum, one_mul]

theorem sum_pair_partition_weights {I J : Type*} [Fintype I] [Fintype J]
    (a : I → ℝ) (b : J → ℝ) (ha : ∑ i, a i = 1) (hb : ∑ j, b j = 1) :
    (∑ ij : I × J, a ij.1 * b ij.2) = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, hb, mul_one]
  exact ha

end Erdos3

end

section

namespace Erdos3

theorem abs_sub_le_of_circle_dist_from_interior_center {x c δ : ℝ}
    (hx : 0 ≤ x ∧ x ≤ 1) (hc : δ < c ∧ c < 1 - δ)
    (hdist : dist (x : UnitAddCircle) (c : UnitAddCircle) ≤ δ) :
    |x - c| ≤ δ := by
  rw [dist_eq_norm, ← QuotientAddGroup.mk_sub, UnitAddCircle.norm_eq] at hdist
  have hxc : |x - c| < 1 - δ := abs_lt.mpr ⟨by linarith, by linarith⟩
  have hz : |(round (x - c) : ℝ)| ≤ |x - c - (round (x - c) : ℝ)| + |x - c| := by
    calc
      _ = |((round (x - c) : ℝ) - (x - c)) + (x - c)| := by ring_nf
      _ ≤ |(round (x - c) : ℝ) - (x - c)| + |x - c| := abs_add_le _ _
      _ = _ := by rw [abs_sub_comm (round (x - c) : ℝ) (x - c)]
  have hzlt : |(round (x - c) : ℝ)| < 1 := by linarith
  have hzlo : (-1 : ℤ) < round (x - c) := by exact_mod_cast (abs_lt.mp hzlt).1
  have hzhi : round (x - c) < (1 : ℤ) := by exact_mod_cast (abs_lt.mp hzlt).2
  have hz0 : round (x - c) = 0 := by omega
  simpa only [hz0, Int.cast_zero, sub_zero] using hdist

theorem residue_fraction_mem_unit_interval {N : ℕ} [NeZero N] (x : ZMod N) :
    0 ≤ (x.val : ℝ) / N ∧ (x.val : ℝ) / N ≤ 1 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  exact ⟨by positivity, (div_le_one hN).mpr (by exact_mod_cast x.val_lt.le)⟩

theorem residue_fraction_close_to_interior_center {N : ℕ} [NeZero N]
    (x : ZMod N) {c δ : ℝ} (hc : δ < c ∧ c < 1 - δ)
    (hdist : dist (ZMod.toAddCircle x) (c : UnitAddCircle) ≤ δ) :
    |(x.val : ℝ) / N - c| ≤ δ := by
  rw [ZMod.toAddCircle_apply] at hdist
  exact abs_sub_le_of_circle_dist_from_interior_center (residue_fraction_mem_unit_interval x) hc hdist

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

def frozenRealSection {Z Ξ : Type*} (F : Z → Ξ → ℝ) (a : Option Ξ) (z : Z) : ℝ :=
  a.elim 0 (F z)

theorem frozenRealSection_unit_interval {Z Ξ : Type*} (F : Z → Ξ → ℝ)
    (hF : ∀ z a, 0 ≤ F z a ∧ F z a ≤ 1) (a : Option Ξ) (z : Z) :
    0 ≤ frozenRealSection F a z ∧ frozenRealSection F a z ≤ 1 := by
  cases a with
  | none => simp [frozenRealSection]
  | some a => exact hF z a

noncomputable def positiveCellParameter {A X Ξ : Type*}
    (w : A → X → ℝ) (E : Set X) (xi : X → Ξ) (a : A) : Option Ξ := by
  classical
  exact if h : ∃ x, x ∉ E ∧ 0 < w a x then some (xi h.choose) else none

theorem positiveCellParameter_of_empty {A X Ξ : Type*}
    (w : A → X → ℝ) (E : Set X) (xi : X → Ξ) (a : A)
    (h : ¬∃ x, x ∉ E ∧ 0 < w a x) : positiveCellParameter w E xi a = none := by
  simp [positiveCellParameter, h]

theorem positiveCellParameter_of_positive {A X Ξ : Type*}
    (w : A → X → ℝ) (E : Set X) (xi : X → Ξ) (a : A)
    {x : X} (hx : x ∉ E) (hpos : 0 < w a x) :
    ∃ y, y ∉ E ∧ 0 < w a y ∧ positiveCellParameter w E xi a = some (xi y) := by
  classical
  unfold positiveCellParameter
  split_ifs with h
  · exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2, rfl⟩
  · exact (h ⟨x, hx, hpos⟩).elim

theorem positive_discretization_error {A X Z Ξ : Type*} [Fintype A] [PseudoMetricSpace Ξ]
    (w : A → X → ℝ) (E : Set X) (z : X → Z) (xi : X → Ξ)
    (F : Z → Ξ → ℝ) (T : X → ℝ) {L : ℝ≥0} {rho : ℝ}
    (hw : ∀ a x, 0 ≤ w a x) (hsum : ∀ x, ∑ a, w a x = 1)
    (hT : ∀ x, x ∉ E → T x = F (z x) (xi x))
    (hLip : ∀ q, LipschitzWith L (F q))
    (hdiam : ∀ a x y, x ∉ E → y ∉ E → 0 < w a x → 0 < w a y →
      dist (xi x) (xi y) ≤ rho) (x : X) (hx : x ∉ E) :
    |T x - ∑ a, w a x * frozenRealSection F (positiveCellParameter w E xi a) (z x)| ≤ L * rho := by
  apply abs_sub_positive_sum_le (fun a => w a x) _ _ _ (fun a => hw a x) (hsum x)
  intro a ha
  obtain ⟨y, hy, hwy, heq⟩ := positiveCellParameter_of_positive w E xi a hx ha
  rw [heq, hT x hx]
  change |F (z x) (xi x) - F (z x) (xi y)| ≤ (L : ℝ) * rho
  simpa only [Real.dist_eq] using (hLip (z x)).dist_le_mul_of_le (hdiam a x y hx hy ha hwy)

theorem exists_positive_shift_discretization
    {I J G Ξ : Type*} [Fintype I] [Fintype J] [Add G] [PseudoMetricSpace Ξ]
    {Z : G → Type*}
    (A : I → G → ℝ) (B : J → G → ℝ) (E : G → Set G)
    (z : ∀ h, G → Z h) (xi : G → G → Ξ) (F : ∀ h, Z h → Ξ → ℝ) (T : G → G → ℝ)
    {L : ℝ≥0} {rho : ℝ}
    (hA : ∀ i n, 0 ≤ A i n) (hB : ∀ j n, 0 ≤ B j n)
    (hAsum : ∀ n, ∑ i, A i n = 1) (hBsum : ∀ n, ∑ j, B j n = 1)
    (hT : ∀ h n, n ∉ E h → T h n = F h (z h n) (xi h n))
    (hLip : ∀ h q, LipschitzWith L (F h q))
    (hdiam : ∀ i j h n n', n ∉ E h → n' ∉ E h →
      0 < A i n * B j (n + h) → 0 < A i n' * B j (n' + h) →
      dist (xi h n) (xi h n') ≤ rho) :
    ∃ a : I → J → G → Option Ξ,
      (∀ i j h, (¬∃ n, n ∉ E h ∧ 0 < A i n * B j (n + h)) → a i j h = none) ∧
      ∀ h n, n ∉ E h →
        |T h n - ∑ i, ∑ j, A i n * B j (n + h) * frozenRealSection (F h) (a i j h) (z h n)|
          ≤ L * rho := by
  classical
  let w : G → I × J → G → ℝ := fun h ij n => A ij.1 n * B ij.2 (n + h)
  let a : I → J → G → Option Ξ := fun i j h => positiveCellParameter (w h) (E h) (xi h) (i, j)
  refine ⟨a, ?_, ?_⟩
  · intro i j h hempty
    exact positiveCellParameter_of_empty (w h) (E h) (xi h) (i, j) hempty
  · intro h n hn
    have he := positive_discretization_error (w h) (E h) (z h) (xi h) (F h) (T h)
      (fun ij n => mul_nonneg (hA ij.1 n) (hB ij.2 (n + h)))
      (fun n => sum_pair_partition_weights (fun i => A i n) (fun j => B j (n + h))
        (hAsum n) (hBsum (n + h))) (hT h) (hLip h)
      (fun ij n n' => hdiam ij.1 ij.2 h n n') n hn
    simpa only [Fintype.sum_prod_type, w, a] using he

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem positive_partition_sum_unit_interval {I : Type*} [Fintype I]
    (w c : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hc : ∀ i, 0 ≤ c i ∧ c i ≤ 1) :
    0 ≤ ∑ i, w i * c i ∧ ∑ i, w i * c i ≤ 1 := by
  refine ⟨Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (hc i).1), ?_⟩
  calc
    _ ≤ ∑ i, w i := Finset.sum_le_sum (fun i _ => mul_le_of_le_one_right (hw i) (hc i).2)
    _ = 1 := hsum

theorem expect_abs_le_of_exceptional_set {X : Type*} [Fintype X] [Nonempty X]
    (E : Finset X) (f : X → ℝ) {M ε : ℝ} (hε : 0 ≤ ε)
    (hcap : ∀ x, |f x| ≤ M) (hgood : ∀ x, x ∉ E → |f x| ≤ ε) :
    (𝔼 x, |f x|) ≤ ε + M * (E.card : ℝ) / Fintype.card X := by
  classical
  have hbound (x : X) : |f x| ≤ ε + if x ∈ E then M else 0 := by
    by_cases hx : x ∈ E
    · simp only [hx, ↓reduceIte]
      exact (hcap x).trans (le_add_of_nonneg_left hε)
    · simpa only [hx, ↓reduceIte, add_zero] using hgood x hx
  calc
    _ ≤ (𝔼 x : X, (ε + if x ∈ E then M else 0)) := Finset.expect_le_expect (fun x _ => hbound x)
    _ = ε + M * (E.card : ℝ) / Fintype.card X := by
      rw [Finset.expect_add_distrib, Fintype.expect_const]
      congr 1
      simp [Fintype.expect_eq_sum_div_card, Finset.sum_ite_mem, mul_comm]

theorem positive_partition_approximation_mean_error {I X : Type*}
    [Fintype I] [Fintype X] [Nonempty X]
    (E : Finset X) (w c : I → X → ℝ) (T : X → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hw : ∀ i x, 0 ≤ w i x) (hsum : ∀ x, ∑ i, w i x = 1)
    (hc : ∀ i x, 0 ≤ c i x ∧ c i x ≤ 1) (hT : ∀ x, 0 ≤ T x ∧ T x ≤ 1)
    (hgood : ∀ x, x ∉ E → |T x - ∑ i, w i x * c i x| ≤ ε) :
    (𝔼 x, |T x - ∑ i, w i x * c i x|) ≤ ε + (E.card : ℝ) / Fintype.card X := by
  have hcap (x : X) : |T x - ∑ i, w i x * c i x| ≤ 1 := by
    have hc' := positive_partition_sum_unit_interval (fun i => w i x) (fun i => c i x)
      (fun i => hw i x) (hsum x) (fun i => hc i x)
    exact abs_le.mpr ⟨by linarith [(hT x).1], by linarith [(hT x).2]⟩
  simpa only [one_mul] using expect_abs_le_of_exceptional_set E _ hε hcap hgood

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem cellwise_positive_discretization_error {A X Z Ξ : Type*} [Fintype A] [PseudoMetricSpace Ξ]
    (w : A → X → ℝ) (E : Set X) (z : X → Z) (xi : X → Ξ)
    (F : A → Z → Ξ → ℝ) (T : X → ℝ) {L : ℝ≥0} {rho delta : ℝ}
    (hw : ∀ a x, 0 ≤ w a x) (hsum : ∀ x, ∑ a, w a x = 1)
    (hT : ∀ a x, x ∉ E → 0 < w a x → |T x - F a (z x) (xi x)| ≤ delta)
    (hLip : ∀ a q, LipschitzWith L (F a q))
    (hdiam : ∀ a x y, x ∉ E → y ∉ E → 0 < w a x → 0 < w a y →
      dist (xi x) (xi y) ≤ rho) (x : X) (hx : x ∉ E) :
    |T x - ∑ a, w a x * frozenRealSection (F a) (positiveCellParameter w E xi a) (z x)| ≤
      delta + L * rho := by
  apply abs_sub_positive_sum_le (fun a => w a x) _ _ _ (fun a => hw a x) (hsum x)
  intro a ha
  obtain ⟨y, hy, hwy, heq⟩ := positiveCellParameter_of_positive w E xi a hx ha
  rw [heq]
  change |T x - F a (z x) (xi y)| ≤ delta + (L : ℝ) * rho
  apply (abs_sub_le (T x) (F a (z x) (xi x)) (F a (z x) (xi y))).trans
  apply add_le_add (hT a x hx ha)
  simpa only [Real.dist_eq] using (hLip a (z x)).dist_le_mul_of_le (hdiam a x y hx hy ha hwy)

theorem exists_cellwise_positive_shift_discretization
    {I J G Ξ : Type*} [Fintype I] [Fintype J] [Add G] [PseudoMetricSpace Ξ]
    {Z : G → Type*} (A : I → G → ℝ) (B : J → G → ℝ) (E : G → Set G)
    (z : ∀ h, G → Z h) (xi : G → G → Ξ) (F : I → ∀ h, Z h → Ξ → ℝ) (T : G → G → ℝ)
    {L : ℝ≥0} {rho delta : ℝ}
    (hA : ∀ i n, 0 ≤ A i n) (hB : ∀ j n, 0 ≤ B j n)
    (hAsum : ∀ n, ∑ i, A i n = 1) (hBsum : ∀ n, ∑ j, B j n = 1)
    (hT : ∀ i h n, n ∉ E h → 0 < A i n → |T h n - F i h (z h n) (xi h n)| ≤ delta)
    (hLip : ∀ i h q, LipschitzWith L (F i h q))
    (hdiam : ∀ i j h n n', n ∉ E h → n' ∉ E h →
      0 < A i n * B j (n + h) → 0 < A i n' * B j (n' + h) →
      dist (xi h n) (xi h n') ≤ rho) :
    ∃ a : I → J → G → Option Ξ,
      (∀ i j h, (¬∃ n, n ∉ E h ∧ 0 < A i n * B j (n + h)) → a i j h = none) ∧
      ∀ h n, n ∉ E h →
        |T h n - ∑ i, ∑ j, A i n * B j (n + h) * frozenRealSection (F i h) (a i j h) (z h n)| ≤
          delta + L * rho := by
  classical
  let w : G → I × J → G → ℝ := fun h ij n => A ij.1 n * B ij.2 (n + h)
  let a : I → J → G → Option Ξ := fun i j h => positiveCellParameter (w h) (E h) (xi h) (i, j)
  refine ⟨a, ?_, ?_⟩
  · intro i j h hempty
    exact positiveCellParameter_of_empty (w h) (E h) (xi h) (i, j) hempty
  · intro h n hn
    have herror (ij : I × J) (x : G) (hx : x ∉ E h) (hpos : 0 < w h ij x) :
        |T h x - F ij.1 h (z h x) (xi h x)| ≤ delta := by
      apply hT ij.1 h x hx
      by_contra hnot
      exact not_le_of_gt hpos (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hnot) (hB ij.2 (x + h)))
    have he := cellwise_positive_discretization_error (w h) (E h) (z h) (xi h)
      (fun ij => F ij.1 h) (T h)
      (fun ij n => mul_nonneg (hA ij.1 n) (hB ij.2 (n + h)))
      (fun n => sum_pair_partition_weights (fun i => A i n) (fun j => B j (n + h))
        (hAsum n) (hBsum (n + h))) herror (fun ij => hLip ij.1 h)
      (fun ij n n' => hdiam ij.1 ij.2 h n n') n hn
    simpa only [Fintype.sum_prod_type, w, a] using he

end Erdos3

end

section

namespace Erdos3

noncomputable def cyclicWrapExceptional {N : ℕ} [NeZero N] (h : ZMod N) (ρ : ℝ) : Finset (ZMod N) :=
  cyclicCutNeighborhood N 0 (N * ρ) ∪ cyclicCutNeighborhood N N (N * ρ) ∪
    cyclicCutNeighborhood N ((N - h.val : ℕ) : ℤ) (N * ρ)

theorem cyclicWrapExceptional_card_le {N : ℕ} [NeZero N] (h : ZMod N)
    {ρ : ℝ} (hρ : 0 ≤ ρ) : ((cyclicWrapExceptional h ρ).card : ℝ) ≤ 6 * N * ρ + 3 := by
  have hδ : 0 ≤ (N : ℝ) * ρ := mul_nonneg (Nat.cast_nonneg _) hρ
  have h0 := cyclicCutNeighborhood_card_le N 0 hδ
  have hN := cyclicCutNeighborhood_card_le N N hδ
  have hw := cyclicCutNeighborhood_card_le N ((N - h.val : ℕ) : ℤ) hδ
  have hu := Finset.card_union_le (cyclicCutNeighborhood N 0 (N * ρ))
    (cyclicCutNeighborhood N N (N * ρ))
  have hv := Finset.card_union_le
    (cyclicCutNeighborhood N 0 (N * ρ) ∪ cyclicCutNeighborhood N N (N * ρ))
    (cyclicCutNeighborhood N ((N - h.val : ℕ) : ℤ) (N * ρ))
  have hu' : ((cyclicCutNeighborhood N 0 (N * ρ) ∪ cyclicCutNeighborhood N N (N * ρ)).card : ℝ) ≤
      (cyclicCutNeighborhood N 0 (N * ρ)).card + (cyclicCutNeighborhood N N (N * ρ)).card := by
    exact_mod_cast hu
  have hv' : ((cyclicWrapExceptional h ρ).card : ℝ) ≤
      (cyclicCutNeighborhood N 0 (N * ρ) ∪ cyclicCutNeighborhood N N (N * ρ)).card +
        (cyclicCutNeighborhood N ((N - h.val : ℕ) : ℤ) (N * ρ)).card := by
    exact_mod_cast hv
  linarith

theorem cyclicWrapExceptional_density_le {N : ℕ} [NeZero N] (h : ZMod N)
    {ρ : ℝ} (hρ : 0 ≤ ρ) : ((cyclicWrapExceptional h ρ).card : ℝ) / N ≤ 6 * ρ + 3 / N := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  calc
    _ ≤ (6 * (N : ℝ) * ρ + 3) / N :=
      div_le_div_of_nonneg_right (cyclicWrapExceptional_card_le h hρ) (Nat.cast_nonneg _)
    _ = _ := by field_simp

theorem outside_cyclicWrapExceptional {N : ℕ} [NeZero N] (h x : ZMod N) {ρ : ℝ}
    (hx : x ∉ cyclicWrapExceptional h ρ) :
    ρ < (x.val : ℝ) / N ∧ (x.val : ℝ) / N < 1 - ρ ∧
      (N : ℝ) * ρ < |(x.val : ℝ) - ((N - h.val : ℕ) : ℝ)| := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hxN : (x.val : ℝ) < N := Nat.cast_lt.mpr x.val_lt
  simp only [cyclicWrapExceptional, Finset.mem_union, not_or, mem_cyclicCutNeighborhood] at hx
  have h0 : (N : ℝ) * ρ < (x.val : ℝ) := by
    simpa only [Int.cast_zero, sub_zero,
      abs_of_nonneg (show (0 : ℝ) ≤ x.val from Nat.cast_nonneg _)] using lt_of_not_ge hx.1.1
  have h1 : (N : ℝ) * ρ < (N : ℝ) - x.val := by
    simpa only [Int.cast_natCast, abs_of_neg (sub_neg.mpr hxN), neg_sub] using lt_of_not_ge hx.1.2
  refine ⟨(lt_div_iff₀ hN).mpr (by nlinarith), (div_lt_iff₀ hN).mpr (by nlinarith), ?_⟩
  simpa only [Int.cast_natCast] using lt_of_not_ge hx.2

end Erdos3

end

section

namespace Erdos3

theorem good_circle_observations_control_representatives {N : ℕ} [NeZero N]
    (h x y : ZMod N) {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∉ cyclicWrapExceptional h ρ) (hy : y ∉ cyclicWrapExceptional h ρ)
    (hdist : dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ) :
    |(x.val : ℝ) / N - (y.val : ℝ) / N| ≤ ρ := by
  have hx' := outside_cyclicWrapExceptional h x hx
  have hy' := outside_cyclicWrapExceptional h y hy
  apply abs_sub_le_of_circle_dist_on_interior ⟨hx'.1.le, hx'.2.1.le⟩ ⟨hy'.1.le, hy'.2.1.le⟩
    (by linarith)
  simpa only [ZMod.toAddCircle_apply] using hdist

theorem cyclic_wrap_branch_eq_of_good_circle {N : ℕ} [NeZero N]
    (h x y : ZMod N) {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∉ cyclicWrapExceptional h ρ) (hy : y ∉ cyclicWrapExceptional h ρ)
    (hdist : dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ) :
    (N - h.val ≤ x.val ↔ N - h.val ≤ y.val) := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hd := good_circle_observations_control_representatives h x y hρ hx hy hdist
  rw [← sub_div, abs_div, abs_of_pos hN] at hd
  have hdiff : |(x.val : ℝ) - y.val| ≤ (N : ℝ) * ρ := by
    have h := (div_le_iff₀ hN).mp hd
    nlinarith
  have hgap := (outside_cyclicWrapExceptional h x hx).2.2
  have hb := same_side_of_cut_of_small_displacement hdiff hgap
  exact_mod_cast hb

theorem cyclic_representative_difference_of_good_circle {N : ℕ} [NeZero N]
    (h x y : ZMod N) {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∉ cyclicWrapExceptional h ρ) (hy : y ∉ cyclicWrapExceptional h ρ)
    (hdist : dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ) :
    ((h + x).val : ℤ) - ((h + y).val : ℤ) = (x.val : ℤ) - (y.val : ℤ) := by
  have hb := cyclic_wrap_branch_eq_of_good_circle h x y hρ hx hy hdist
  rw [cyclic_representative_add h x, cyclic_representative_add h y]
  simp only [← hb]
  ring

end Erdos3

end

section

namespace Erdos3

theorem cyclicCutNeighborhood_mono (N : ℕ) [NeZero N] (a : ℤ)
    {ρ δ : ℝ} (h : ρ ≤ δ) : cyclicCutNeighborhood N a ρ ⊆ cyclicCutNeighborhood N a δ := by
  intro x hx
  exact (mem_cyclicCutNeighborhood N a δ x).mpr
    (((mem_cyclicCutNeighborhood N a ρ x).mp hx).trans h)

theorem cyclicWrapExceptional_mono {N : ℕ} [NeZero N] (h : ZMod N)
    {ρ δ : ℝ} (hscale : ρ ≤ δ) : cyclicWrapExceptional h ρ ⊆ cyclicWrapExceptional h δ := by
  have hmul := mul_le_mul_of_nonneg_left hscale (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  exact Finset.union_subset_union
    (Finset.union_subset_union (cyclicCutNeighborhood_mono N 0 hmul)
      (cyclicCutNeighborhood_mono N N hmul))
    (cyclicCutNeighborhood_mono N ((N - h.val : ℕ) : ℤ) hmul)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def interiorIntervalCutoff (eta : ℝ≥0) (x : ℝ) : ℝ :=
  linearCutoff (1 / 2 - 2 * eta) eta |x - 1 / 2|

theorem interiorIntervalCutoff_range (eta : ℝ≥0) (x : ℝ) :
    0 ≤ interiorIntervalCutoff eta x ∧ interiorIntervalCutoff eta x ≤ 1 :=
  linearCutoff_range _ _ _

theorem interiorIntervalCutoff_one (eta : ℝ≥0) (heta : 0 < eta) {x : ℝ}
    (hx : 2 * (eta : ℝ) ≤ x ∧ x ≤ 1 - 2 * eta) : interiorIntervalCutoff eta x = 1 := by
  apply linearCutoff_eq_one _ _ heta
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem interiorIntervalCutoff_support (eta : ℝ≥0) {x : ℝ}
    (hx : interiorIntervalCutoff eta x ≠ 0) : (eta : ℝ) < x ∧ x < 1 - eta := by
  have h : |x - 1 / 2| < 1 / 2 - eta := by
    by_contra h
    apply hx
    exact linearCutoff_eq_zero _ _ (by linarith [le_of_not_gt h])
  exact ⟨by linarith [(abs_lt.mp h).1], by linarith [(abs_lt.mp h).2]⟩

theorem interiorIntervalCutoff_lipschitz (eta : ℝ≥0) (heta : 0 < eta) :
    LipschitzWith eta⁻¹ (interiorIntervalCutoff eta) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply ((linearCutoff_lipschitz _ eta heta).dist_le_mul _ _).trans
  apply mul_le_mul_of_nonneg_left _ (NNReal.coe_nonneg _)
  rw [Real.dist_eq]
  exact (abs_abs_sub_abs_le_abs_sub _ _).trans_eq (by rw [sub_sub_sub_cancel_right]; rfl)

theorem interiorIntervalCutoff_cyclic_loss {N : ℕ} [NeZero N]
    (eta : ℝ≥0) (heta : 0 < eta) :
    (𝔼 x : ZMod N, |1 - interiorIntervalCutoff eta ((x.val : ℝ) / N)|) ≤
      12 * (eta : ℝ) + 3 / N := by
  let E := cyclicWrapExceptional (0 : ZMod N) (2 * eta)
  have hcap (x : ZMod N) : |1 - interiorIntervalCutoff eta ((x.val : ℝ) / N)| ≤ 1 := by
    have h := interiorIntervalCutoff_range eta ((x.val : ℝ) / N)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hgood (x : ZMod N) (hx : x ∉ E) :
      |1 - interiorIntervalCutoff eta ((x.val : ℝ) / N)| ≤ 0 := by
    obtain ⟨h0, h1, _⟩ := outside_cyclicWrapExceptional (0 : ZMod N) x hx
    rw [interiorIntervalCutoff_one eta heta ⟨h0.le, h1.le⟩]
    norm_num
  have h := expect_abs_le_of_exceptional_set E _ (by norm_num : (0 : ℝ) ≤ 0) hcap hgood
  simp only [zero_add, one_mul, ZMod.card] at h
  apply h.trans
  calc
    _ ≤ 6 * (2 * (eta : ℝ)) + 3 / N :=
      cyclicWrapExceptional_density_le (0 : ZMod N) (show 0 ≤ 2 * (eta : ℝ) by positivity)
    _ = _ := by ring

end Erdos3

end

end OAI

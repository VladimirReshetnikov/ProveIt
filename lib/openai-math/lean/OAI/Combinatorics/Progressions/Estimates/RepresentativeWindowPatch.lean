import OAI.Combinatorics.Progressions.Geometry.QuantitativeMetricPartition
import OAI.Combinatorics.Progressions.Probability.IntervalDivisorProbability
import OAI.Combinatorics.Progressions.Sampling.CyclicInteriorScore
import OAI.Combinatorics.Progressions.Sampling.PositivePartitionScore

namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {X I : Type*} [PseudoMetricSpace X] [Fintype I]

noncomputable def regularizedTentPartition (c : I → X) (r : ℝ) (i : I) (x : X) : ℝ :=
  metricTent (c i) r x / max r (metricTentSum c r x)

theorem regularizedTentPartition_range (c : I → X) {r : ℝ} (hr : 0 < r) (i : I) (x : X) :
    0 ≤ regularizedTentPartition c r i x ∧ regularizedTentPartition c r i x ≤ 1 := by
  have hd : 0 < max r (metricTentSum c r x) := hr.trans_le (le_max_left _ _)
  refine ⟨div_nonneg (metricTent_nonneg _ _ _) hd.le, (div_le_one hd).mpr ?_⟩
  exact (Finset.single_le_sum (fun j _ => metricTent_nonneg (c j) r x)
    (Finset.mem_univ i)).trans (le_max_right _ _)

theorem regularizedTentPartition_sum (c : I → X) {r : ℝ} (hr : 0 < r) (x : X)
    (hx : ∃ i, dist x (c i) ≤ r) : ∑ i, regularizedTentPartition c r i x = 1 := by
  obtain ⟨i, hi⟩ := hx
  have hs : r ≤ metricTentSum c r x := by
    calc
      r ≤ metricTent (c i) r x := (by linarith : r ≤ 2 * r - dist x (c i)).trans (le_max_right _ _)
      _ ≤ metricTentSum c r x := Finset.single_le_sum (fun j _ => metricTent_nonneg (c j) r x) (Finset.mem_univ i)
  simp only [regularizedTentPartition, ← Finset.sum_div, max_eq_right hs]
  exact div_self (hr.trans_le hs).ne'

theorem regularizedTentPartition_zero (c : I → X) (r : ℝ) (i : I) (x : X)
    (hx : 2 * r ≤ dist x (c i)) : regularizedTentPartition c r i x = 0 := by
  simp only [regularizedTentPartition, metricTent_zero_of_far (c i) x hx, zero_div]

theorem regularizedTentPartition_lipschitz (c : I → X) {r : ℝ≥0} (hr : 0 < r) (i : I) :
    LipschitzWith ((2 * Fintype.card I + 1) / r) (regularizedTentPartition c r i) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hd : |max (r : ℝ) (metricTentSum c r x) - max (r : ℝ) (metricTentSum c r y)| ≤
      Fintype.card I * dist x y := by
    rw [max_comm (r : ℝ), max_comm (r : ℝ)]
    exact (abs_max_sub_max_le_abs _ _ _).trans (abs_metricTentSum_sub_le c r x y)
  have hb : |metricTent (c i) (r : ℝ) y| ≤ 2 * (r : ℝ) := by
    rw [abs_of_nonneg (metricTent_nonneg _ _ _)]
    exact metricTent_le (c i) r.coe_nonneg y
  have h := abs_div_sub_div_bound (show (0 : ℝ) < r from hr)
    (le_max_left _ _) (le_max_left _ _) dist_nonneg
    (by positivity : (0 : ℝ) ≤ 2 * r) (by positivity : (0 : ℝ) ≤ Fintype.card I * dist x y)
    (abs_metricTent_sub_le (c i) r x y) hb hd
  rw [Real.dist_eq]
  apply h.trans_eq
  push_cast
  field_simp
  ring

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

noncomputable def intervalSiteCount (B r : ℝ) : ℕ := boxCoverMeshCount B 1 r + 1

noncomputable def intervalSiteCenter (B r : ℝ) (i : Fin (intervalSiteCount B r)) : ℝ :=
  uniformIntervalGrid B (boxCoverMeshCount B 1 r) i

noncomputable def intervalSiteWeight (B r : ℝ) : Fin (intervalSiteCount B r) → ℝ → ℝ :=
  regularizedTentPartition (intervalSiteCenter B r) r

theorem intervalSiteCenter_bound {B r : ℝ} (hB : 0 ≤ B) (i : Fin (intervalSiteCount B r)) :
    |intervalSiteCenter B r i| ≤ B :=
  uniformIntervalGrid_mem hB (boxCoverMeshCount_pos _ _ _) i

theorem intervalSiteWeight_range (B : ℝ) {r : ℝ} (hr : 0 < r)
    (i : Fin (intervalSiteCount B r)) (x : ℝ) :
    0 ≤ intervalSiteWeight B r i x ∧ intervalSiteWeight B r i x ≤ 1 :=
  regularizedTentPartition_range _ hr i x

theorem intervalSiteWeight_sum {B r : ℝ} (hB : 0 < B) (hr : 0 < r) (x : ℝ) (hx : |x| ≤ B) :
    ∑ i, intervalSiteWeight B r i x = 1 := by
  apply regularizedTentPartition_sum _ hr
  obtain ⟨i, hi⟩ := exists_uniformIntervalGrid_approx hB (boxCoverMeshCount_pos B 1 r) x hx
  refine ⟨i, ?_⟩
  have he := boxCoverMeshCount_error (1 : ℝ≥0) hr (B := B)
  simp only [NNReal.coe_one, one_mul] at he
  exact (show dist x (intervalSiteCenter B r i) ≤ 2 * B / boxCoverMeshCount B 1 r from hi).trans he

theorem intervalSiteWeight_near (B r : ℝ) (i : Fin (intervalSiteCount B r)) (x : ℝ)
    (hx : 0 < intervalSiteWeight B r i x) : dist x (intervalSiteCenter B r i) < 2 * r := by
  by_contra! hn
  exact hx.ne' (regularizedTentPartition_zero _ _ i x hn)

theorem intervalSiteWeight_lipschitz (B : ℝ) {r : ℝ≥0} (hr : 0 < r)
    (i : Fin (intervalSiteCount B r)) :
    LipschitzWith ((2 * intervalSiteCount B r + 1) / r) (intervalSiteWeight B r i) := by
  have h := regularizedTentPartition_lipschitz (intervalSiteCenter B r) hr i
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (regularizedTentPartition (intervalSiteCenter B r) r i x)
    (regularizedTentPartition (intervalSiteCenter B r) r i y) ≤ _
  simpa only [Fintype.card_fin] using h.dist_le_mul x y

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

variable {X I : Type*} [PseudoMetricSpace X] [Fintype I]

theorem regularizedTentPartition_sum_le (c : I → X) {r : ℝ} (hr : 0 < r) (x : X) :
    (∑ i, regularizedTentPartition c r i x) ≤ 1 := by
  simp only [regularizedTentPartition, ← Finset.sum_div]
  apply (div_le_one (hr.trans_le (le_max_left _ _))).mpr
  exact le_max_right _ _

theorem regularizedTentPartition_approx (c : I → X) {r : ℝ} (hr : 0 < r)
    (f : X → ℝ) {L : ℝ≥0} (hf : LipschitzWith L f)
    (hcover : ∀ x, f x ≠ 0 → ∃ i, dist x (c i) ≤ r) (x : X) :
    |f x - ∑ i, regularizedTentPartition c r i x * f (c i)| ≤ 2 * L * r := by
  let w : I → ℝ := fun i => regularizedTentPartition c r i x
  have hw (i) : 0 ≤ w i := (regularizedTentPartition_range c hr i x).1
  have hsum : (∑ i, w i) ≤ 1 := regularizedTentPartition_sum_le c hr x
  have hidentity : f x = (∑ i, w i) * f x := by
    by_cases hx : f x = 0
    · simp only [hx, mul_zero]
    · rw [show (∑ i, w i) = 1 from regularizedTentPartition_sum c hr x (hcover x hx), one_mul]
  have hdiff : f x - ∑ i, w i * f (c i) = ∑ i, w i * (f x - f (c i)) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← hidentity]
  change |f x - ∑ i, w i * f (c i)| ≤ _
  rw [hdiff]
  calc
    _ ≤ ∑ i, |w i * (f x - f (c i))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, w i * (2 * L * r) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (hw i)]
      by_cases hi : w i = 0
      · simp only [hi, zero_mul, le_refl]
      · have hnear : dist x (c i) < 2 * r := by
          by_contra! hfar
          exact hi (regularizedTentPartition_zero c r i x hfar)
        apply mul_le_mul_of_nonneg_left _ (hw i)
        calc
          |f x - f (c i)| ≤ (L : ℝ) * dist x (c i) := hf.dist_le_mul x (c i)
          _ ≤ (L : ℝ) * (2 * r) := mul_le_mul_of_nonneg_left hnear.le L.coe_nonneg
          _ = _ := by ring
    _ = (∑ i, w i) * (2 * L * r) := (Finset.sum_mul _ _ _).symm
    _ ≤ 2 * L * r := mul_le_of_le_one_left (by positivity) hsum

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)

theorem norm_complexMean_cutoff_error (b : X → ℝ) (F : X → ℂ)
    (hb : ∀ x, b x ∈ Set.Icc (0 : ℝ) 1) (hF : ∀ x, ‖F x‖ ≤ 1) :
    ‖p.complexMean F - p.complexMean (fun x => (b x : ℂ) * F x)‖ ≤
      p.mean (fun x => 1 - b x) := by
  apply p.norm_complexMean_sub_le
  intro x _
  rw [← one_sub_mul, norm_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.mpr (hb x).2)]
  exact mul_le_of_le_one_right (sub_nonneg.mpr (hb x).2) (hF x)

theorem cutoff_bias_lower (b : X → ℝ) (F : X → ℂ)
    (hb : ∀ x, b x ∈ Set.Icc (0 : ℝ) 1) (hF : ∀ x, ‖F x‖ ≤ 1)
    {ζ ε : ℝ} (hbias : ζ ≤ ‖p.complexMean F‖)
    (hloss : p.mean (fun x => 1 - b x) ≤ ε) :
    ζ - ε ≤ ‖p.complexMean (fun x => (b x : ℂ) * F x)‖ := by
  have he := (p.norm_complexMean_cutoff_error b F hb hF).trans hloss
  have ht := norm_le_norm_sub_add (p.complexMean F)
    (p.complexMean (fun x => (b x : ℂ) * F x))
  linarith

theorem mean_one_sub (b : X → ℝ) :
    p.mean (fun x => 1 - b x) = 1 - p.mean b := by
  simp only [mean, mul_sub, mul_one, Finset.sum_sub_distrib, p.total]

theorem pi_cutoff_loss {J : Type*} [Fintype J] [DecidableEq J]
    {Ω : J → Type*} [∀ j, Fintype (Ω j)]
    (q : ∀ j, FiniteProbabilityWeights (Ω j)) (b : ∀ j, Ω j → ℝ)
    (hb : ∀ j x, b j x ∈ Set.Icc (0 : ℝ) 1) :
    (pi q).mean (fun x => 1 - ∏ j, b j (x j)) ≤
      ∑ j, (q j).mean (fun x => 1 - b j x) := by
  rw [mean_one_sub, mean_pi_product]
  simp_rw [mean_one_sub]
  apply product_cutoff_loss_le
  intro j
  exact ⟨(q j).mean_nonneg (fun x => (hb j x).1),
    ((q j).mean_mono (fun x => (hb j x).2)).trans_eq ((q j).mean_const 1)⟩

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped NNReal

theorem bounded_weight_cutoff_lipschitz {E : Type*} [PseudoMetricSpace E]
    (w b : E → ℝ) {B K Q : ℝ≥0} (hw : ∀ x, |w x| ≤ B)
    (hb : ∀ x, |b x| ≤ 1) (hwl : LipschitzWith K w) (hbl : LipschitzWith Q b) :
    LipschitzWith (K + B * Q) (fun x => w x * b x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  have hwxy := hwl.dist_le_mul x y
  have hbxy := hbl.dist_le_mul x y
  rw [Real.dist_eq] at hwxy hbxy
  calc
    _ = |(w x - w y) * b x + w y * (b x - b y)| := by congr 1; ring
    _ ≤ |(w x - w y) * b x| + |w y * (b x - b y)| := abs_add_le _ _
    _ ≤ (K : ℝ) * dist x y * 1 + B * ((Q : ℝ) * dist x y) := by
      simp only [abs_mul]
      exact add_le_add (mul_le_mul hwxy (hb x) (abs_nonneg _) (by positivity))
        (mul_le_mul (hw y) hbxy (abs_nonneg _) B.coe_nonneg)
    _ = _ := by simp only [NNReal.coe_add, NNReal.coe_mul]; ring

namespace FiniteProbabilityWeights

theorem norm_complexMean_weighted_cutoff_error {X : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (b w : X → ℝ) (F : X → ℂ) {B : ℝ}
    (hb : ∀ x, b x ∈ Set.Icc (0 : ℝ) 1) (hw : ∀ x, |w x| ≤ B)
    (hF : ∀ x, ‖F x‖ ≤ 1) :
    ‖p.complexMean (fun x => (w x : ℂ) * F x) -
      p.complexMean (fun x => ((w x * b x : ℝ) : ℂ) * F x)‖ ≤
      B * p.mean (fun x => 1 - b x) := by
  rw [← p.mean_const_mul]
  apply p.norm_complexMean_sub_le
  intro x _
  have heq : (w x : ℂ) * F x - ((w x * b x : ℝ) : ℂ) * F x =
      ((1 - b x : ℝ) : ℂ) * ((w x : ℂ) * F x) := by push_cast; ring
  rw [heq, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real]
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (sub_nonneg.mpr (hb x).2)]
  have hweight := (mul_le_of_le_one_right (abs_nonneg (w x)) (hF x)).trans (hw x)
  exact (mul_le_mul_of_nonneg_left hweight (sub_nonneg.mpr (hb x).2)).trans_eq (mul_comm _ _)

theorem weighted_cutoff_bias_lower {X : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (b w : X → ℝ) (F : X → ℂ) {B ζ ε : ℝ}
    (hB : 0 ≤ B) (hb : ∀ x, b x ∈ Set.Icc (0 : ℝ) 1) (hw : ∀ x, |w x| ≤ B)
    (hF : ∀ x, ‖F x‖ ≤ 1)
    (hbias : ζ ≤ ‖p.complexMean (fun x => (w x : ℂ) * F x)‖)
    (hloss : p.mean (fun x => 1 - b x) ≤ ε) :
    ζ - B * ε ≤ ‖p.complexMean (fun x => ((w x * b x : ℝ) : ℂ) * F x)‖ := by
  have he := (p.norm_complexMean_weighted_cutoff_error b w F hb hw hF).trans
    (mul_le_mul_of_nonneg_left hloss hB)
  have ht := norm_le_norm_sub_add (p.complexMean (fun x => (w x : ℂ) * F x))
    (p.complexMean (fun x => ((w x * b x : ℝ) : ℂ) * F x))
  linarith

end FiniteProbabilityWeights

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

theorem pi_bad_event_mass_le {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]
    (p : ∀ j, FiniteProbabilityWeights (X j)) (G : ∀ j, Finset (X j)) :
    (pi p).mass (Finset.univ.filter (fun x => ∃ j, x j ∈ G j)) ≤ ∑ j, (p j).mass (G j) := by
  let b := fun j (x : X j) => if x ∈ G j then (0 : ℝ) else 1
  have hb : ∀ j x, b j x ∈ Set.Icc (0 : ℝ) 1 := by
    intro j x
    dsimp only [b]
    split_ifs <;> constructor <;> norm_num
  have hid (x : ∀ j, X j) :
      (if ∃ j, x j ∈ G j then (1 : ℝ) else 0) = 1 - ∏ j, b j (x j) := by
    by_cases h : ∃ j, x j ∈ G j
    · obtain ⟨j, hj⟩ := h
      have hz : (∏ j, b j (x j)) = 0 := Finset.prod_eq_zero (Finset.mem_univ j) (by simp [b, hj])
      simp only [show ∃ j, x j ∈ G j from ⟨j, hj⟩, ite_true, hz, sub_zero]
    · have hn : ∀ j, x j ∉ G j := fun j hj => h ⟨j, hj⟩
      simp [b, hn]
  rw [← mean_indicator]
  have he : (fun x : ∀ j, X j => if x ∈ Finset.univ.filter (fun x => ∃ j, x j ∈ G j) then (1 : ℝ) else 0) =
      (fun x => 1 - ∏ j, b j (x j)) := by
    funext x
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hid x
  rw [he]
  apply (pi_cutoff_loss p b hb).trans_eq
  apply Finset.sum_congr rfl
  intro j _
  rw [← (p j).mean_indicator (G j)]
  apply congrArg (p j).mean
  funext x
  by_cases h : x ∈ G j <;> simp [b, h]

theorem pi_remove_bad_event_error {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]
    (p : ∀ j, FiniteProbabilityWeights (X j)) (G : ∀ j, Finset (X j))
    (f : (∀ j, X j) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ‖(pi p).complexMean f -
      (pi p).complexMean (fun x => if ∃ j, x j ∈ G j then 0 else f x)‖ ≤ ∑ j, (p j).mass (G j) := by
  have h := (pi p).norm_complexMean_remove_set_le_mass
    (Finset.univ.filter (fun x => ∃ j, x j ∈ G j)) f hf
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
  exact h.trans (pi_bad_event_mass_le p G)

theorem pi_lowWeightFibers_mass {J : Type*} [Fintype J] [DecidableEq J]
    {X R : J → Type*} [∀ j, Fintype (X j)] [∀ j, Fintype (R j)] [∀ j, DecidableEq (X j)]
    (p : ∀ j, FiniteProbabilityWeights (X j)) (F : ∀ j, X j → R j)
    (w : ∀ j, X j → ℝ) (hw : ∀ j x, 0 ≤ w j x) (hm : ∀ j, 0 < (p j).mean (w j))
    (η : J → ℝ) (hη : ∀ j, 0 ≤ η j) :
    (pi (fun j => (p j).reweightPositive (w j) (hw j) (hm j))).mass
      (Finset.univ.filter (fun x => ∃ j, F j (x j) ∈ (p j).lowWeightFibers (F j) (w j) (η j))) ≤
        ∑ j, η j / (p j).mean (w j) := by
  have h := pi_bad_event_mass_le (fun j => (p j).reweightPositive (w j) (hw j) (hm j))
    (fun j => Finset.univ.filter (fun x => F j x ∈ (p j).lowWeightFibers (F j) (w j) (η j)))
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
  exact h.trans (Finset.sum_le_sum (fun j _ => (p j).reweightPositive_lowWeightFibers_mass (F j) (w j) (hw j) (hm j) (hη j)))

theorem pi_remove_lowWeightFibers_error {J : Type*} [Fintype J] [DecidableEq J]
    {X R : J → Type*} [∀ j, Fintype (X j)] [∀ j, Fintype (R j)] [∀ j, DecidableEq (X j)]
    (p : ∀ j, FiniteProbabilityWeights (X j)) (F : ∀ j, X j → R j)
    (w : ∀ j, X j → ℝ) (hw : ∀ j x, 0 ≤ w j x) (hm : ∀ j, 0 < (p j).mean (w j))
    (η : J → ℝ) (hη : ∀ j, 0 ≤ η j) (f : (∀ j, X j) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    let q := pi (fun j => (p j).reweightPositive (w j) (hw j) (hm j))
    ‖q.complexMean f - q.complexMean
      (fun x => if ∃ j, F j (x j) ∈ (p j).lowWeightFibers (F j) (w j) (η j) then 0 else f x)‖ ≤
        ∑ j, η j / (p j).mean (w j) := by
  dsimp only
  have h := (pi (fun j => (p j).reweightPositive (w j) (hw j) (hm j))).norm_complexMean_remove_set_le_mass
    (Finset.univ.filter (fun x => ∃ j, F j (x j) ∈ (p j).lowWeightFibers (F j) (w j) (η j))) f hf
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
  exact h.trans (pi_lowWeightFibers_mass p F w hw hm η hη)

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators NNReal

structure RepresentativeWindow where
  center : ℝ
  value : ℝ → ℝ
  lip : ℝ≥0
  nonneg : ∀ x, 0 ≤ value x
  le_one : ∀ x, value x ≤ 1
  interior : ∀ x, value x ≠ 0 → 0 < x ∧ x < 1
  small : ∀ x, value x ≠ 0 → |x - center| < 1 / 4
  lipschitz : LipschitzWith lip value

noncomputable def representativeWindowCount : ℕ := intervalSiteCount 1 (1 / 16)

theorem representativeWindowCount_pos : 0 < representativeWindowCount := by
  unfold representativeWindowCount intervalSiteCount
  omega

noncomputable def representativeWindowPartitionLip : ℝ≥0 :=
  (2 * representativeWindowCount + 1) / (1 / 16)

noncomputable def localizedRepresentativeWindow (eta : ℝ≥0) (heta : 0 < eta)
    (i : Fin representativeWindowCount) : RepresentativeWindow where
  center := intervalSiteCenter 1 (1 / 16) i
  value x := interiorIntervalCutoff eta x * intervalSiteWeight 1 (1 / 16) i x
  lip := eta⁻¹ + representativeWindowPartitionLip
  nonneg x := mul_nonneg (interiorIntervalCutoff_range eta x).1
    (intervalSiteWeight_range 1 (by norm_num : (0 : ℝ) < 1 / 16) i x).1
  le_one x := (mul_le_of_le_one_right (interiorIntervalCutoff_range eta x).1
    (intervalSiteWeight_range 1 (by norm_num : (0 : ℝ) < 1 / 16) i x).2).trans
      (interiorIntervalCutoff_range eta x).2
  interior x hx := by
    have h := interiorIntervalCutoff_support eta (mul_ne_zero_iff.mp hx).1
    exact ⟨lt_trans (show (0 : ℝ) < eta from heta) h.1, by linarith [eta.coe_nonneg]⟩
  small x hx := by
    have hi : 0 < intervalSiteWeight 1 (1 / 16) i x :=
      lt_of_le_of_ne (intervalSiteWeight_range 1 (by norm_num : (0 : ℝ) < 1 / 16) i x).1
        (Ne.symm (mul_ne_zero_iff.mp hx).2)
    have h := intervalSiteWeight_near 1 (1 / 16) i x hi
    rw [Real.dist_eq] at h
    linarith
  lipschitz := by
    have h := bounded_weight_cutoff_lipschitz (interiorIntervalCutoff eta)
      (intervalSiteWeight 1 (1 / 16) i) (B := 1)
      (fun x => by rw [abs_of_nonneg (interiorIntervalCutoff_range eta x).1]
                   exact (interiorIntervalCutoff_range eta x).2)
      (fun x => by rw [abs_of_nonneg (intervalSiteWeight_range 1 (by norm_num : (0 : ℝ) < 1 / 16) i x).1]
                   exact (intervalSiteWeight_range 1 (by norm_num : (0 : ℝ) < 1 / 16) i x).2)
      (interiorIntervalCutoff_lipschitz eta heta)
      (intervalSiteWeight_lipschitz 1 (by norm_num : (0 : ℝ≥0) < 1 / 16) i)
    simpa only [one_mul, representativeWindowPartitionLip, representativeWindowCount,
      NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using h

theorem localizedRepresentativeWindow_sum (eta : ℝ≥0) (heta : 0 < eta)
    {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 1) :
    (∑ i : Fin representativeWindowCount, (localizedRepresentativeWindow eta heta i).value x) =
      interiorIntervalCutoff eta x := by
  change (∑ i, interiorIntervalCutoff eta x * intervalSiteWeight 1 (1 / 16) i x) = _
  rw [← Finset.mul_sum, intervalSiteWeight_sum (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 1 / 16) x (by rw [abs_of_nonneg hx.1]; exact hx.2), mul_one]

theorem exists_localizedRepresentativeWindow_score {N : ℕ} [NeZero N]
    (f : ZMod N → ℝ) {M sigma : ℝ} (hM : 0 < M) (hsigma : 0 < sigma)
    (hf : ∀ x, |f x| ≤ M) (hscore : sigma ≤ 𝔼 x, f x)
    (eta : ℝ≥0) (heta : 0 < eta) (hwidth : (eta : ℝ) ≤ sigma / (100 * M))
    (hN : 1 / (N : ℝ) ≤ sigma / (100 * M)) :
    ∃ i : Fin representativeWindowCount, 3 * sigma / (4 * representativeWindowCount) ≤
      𝔼 x, f x * (localizedRepresentativeWindow eta heta i).value ((x.val : ℝ) / N) := by
  let : Nonempty (Fin representativeWindowCount) := ⟨⟨0, representativeWindowCount_pos⟩⟩
  have hs := interiorIntervalCutoff_score f hM hsigma hf hscore eta heta hwidth hN
  have hsum (x : ZMod N) : (∑ i : Fin representativeWindowCount,
      intervalSiteWeight 1 (1 / 16) i ((x.val : ℝ) / N)) = 1 :=
    intervalSiteWeight_sum (by norm_num) (by norm_num) _
      (by rw [abs_of_nonneg (residue_fraction_mem_unit_interval x).1]
          exact (residue_fraction_mem_unit_interval x).2)
  obtain ⟨i, hi⟩ := exists_weighted_partition_score (ι := Fin representativeWindowCount)
    (fun x : ZMod N => f x * interiorIntervalCutoff eta ((x.val : ℝ) / N))
    (fun i x => intervalSiteWeight 1 (1 / 16) i ((x.val : ℝ) / N)) hsum hs
  refine ⟨i, ?_⟩
  simpa only [Fintype.card_fin, div_div, mul_assoc, localizedRepresentativeWindow] using hi

end Erdos3

end

section

namespace Erdos3

open MvPolynomial
open scoped NNReal

namespace RepresentativeWindow

noncomputable def kernel (w : RepresentativeWindow) : PatchKernel 1 where
  value r := w.value (w.center - r 0)
  nonneg r := w.nonneg _
  le_one r := w.le_one _
  support r hr i := by
    have h := w.small _ hr
    have he : w.center - r 0 - w.center = -r 0 := by ring
    rw [he, abs_neg] at h
    fin_cases i
    exact h.le
  lip := w.lip
  lipschitz := by
    apply LipschitzWith.of_dist_le_mul
    intro r t
    apply (w.lipschitz.dist_le_mul _ _).trans
    rw [dist_sub_left]
    exact mul_le_mul_of_nonneg_left (dist_le_pi_dist r t 0) w.lip.coe_nonneg

noncomputable def patch {σ : Type*} (w : RepresentativeWindow) (s : ℕ) (hs : 1 ≤ s)
    (P : MvPolynomial σ ℝ) (hP : P ∈ weightedSupportLE (fun _ => 1) 1) :
    PolynomialPatch σ s 1 :=
  PolynomialPatch.ofCoordinates (fun _ => 1) (fun _ => le_rfl) (fun _ => hs)
    (fun _ _ _ => le_rfl) (fun _ => P - C w.center)
    (fun _ => (weightedSupportLE _ _).sub_mem hP (weightedSupportLE_C _ _ _)) w.kernel

theorem patch_term {σ : Type*} (w : RepresentativeWindow) (s : ℕ) (hs : 1 ≤ s)
    (P : MvPolynomial σ ℝ) (hP : P ∈ weightedSupportLE (fun _ => 1) 1)
    (t : σ → ℝ) (b : Fin 1 → ℤ) :
    (w.patch s hs P hP).kernel.value (((w.patch s hs P hP).form.slots t).residual b) =
      w.value (aeval t P - (b 0 : ℝ)) := by
  simp only [patch, PolynomialPatch.ofCoordinates, kernel, TriangularSlots.residual,
    PolynomialSlots.ofCoordinates_center, map_sub, aeval_C, Algebra.algebraMap_self_apply]
  congr 1
  ring

theorem patch_value {σ : Type*} (w : RepresentativeWindow) (s : ℕ) (hs : 1 ≤ s)
    (P : MvPolynomial σ ℝ) (hP : P ∈ weightedSupportLE (fun _ => 1) 1) (t : σ → ℝ) :
    (w.patch s hs P hP).value t = w.value (Int.fract (aeval t P)) := by
  change (∑' b : Fin 1 → ℤ, (w.patch s hs P hP).kernel.value
    (((w.patch s hs P hP).form.slots t).residual b)) = _
  simp_rw [w.patch_term s hs P hP t]
  rw [tsum_eq_single (fun _ : Fin 1 => ⌊aeval t P⌋)]
  · rfl
  · intro b hb
    by_contra h
    obtain ⟨h0, h1⟩ := w.interior _ h
    have hfloor : ⌊aeval t P⌋ = b 0 := Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩
    apply hb
    funext i
    fin_cases i
    exact hfloor.symm

theorem patch_contributing_lift {σ : Type*} (w : RepresentativeWindow) (s : ℕ) (hs : 1 ≤ s)
    (P : MvPolynomial σ ℝ) (hP : P ∈ weightedSupportLE (fun _ => 1) 1)
    (t : σ → ℝ) (b : Fin 1 → ℤ)
    (hb : (w.patch s hs P hP).kernel.value
      (((w.patch s hs P hP).form.slots t).residual b) ≠ 0) :
    b 0 = ⌊aeval t P⌋ := by
  rw [w.patch_term s hs P hP t] at hb
  obtain ⟨h0, h1⟩ := w.interior _ hb
  exact (Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩).symm

@[simp] theorem patch_lip {σ : Type*} (w : RepresentativeWindow) (s : ℕ) (hs : 1 ≤ s)
    (P : MvPolynomial σ ℝ) (hP : P ∈ weightedSupportLE (fun _ => 1) 1) :
    (w.patch s hs P hP).kernel.lip = w.lip := rfl

end RepresentativeWindow
end Erdos3

end

end OAI

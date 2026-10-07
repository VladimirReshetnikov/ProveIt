import OAI.Combinatorics.Progressions.Estimates.FiniteWindowWeightError
import OAI.Combinatorics.Progressions.Estimates.PhysicalAmbientVolumeRatio

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem mem_rectangular_zero_radius_iff {I : Type*} [Fintype I]
    (H : I → ℝ) (R : ℝ) (v : I → ℤ) :
    v ∈ rectangularWeightIndices 0 H R ↔ ∀ i, |(v i : ℝ)| ≤ H i * R := by
  classical
  constructor
  · intro hv i
    have h := sampledWeightIndices_mem_bound (Fintype.mem_piFinset.mp hv i)
    simpa only [Pi.zero_apply, sub_zero] using h
  · intro hv
    apply Fintype.mem_piFinset.mpr
    intro i
    change v i ∈ sampledWeightIndices 0 (H i) R
    simp only [sampledWeightIndices, zero_sub, zero_add, Finset.mem_Icc]
    exact ⟨Int.ceil_le.mpr (abs_le.mp (hv i)).1, Int.le_floor.mpr (abs_le.mp (hv i)).2⟩

noncomputable def commonSpatialWindow {X α : Type*} [Fintype X] [Fintype α]
    (H : X → ℝ) : Finset (X → (Unit ⊕ α) → ℤ) := by
  classical
  exact (Fintype.piFinset (fun d => rectangularWeightIndices 0 (fun _ : Unit ⊕ α => H d) 3)).image
    (fun w d => spatialUnstar (w d))

theorem mem_commonSpatialWindow_iff {X α : Type*} [Fintype X] [Fintype α]
    (H : X → ℝ) (v : X → (Unit ⊕ α) → ℤ) :
    v ∈ commonSpatialWindow H ↔ ∀ d i, |((spatialStar (v d) i : ℤ) : ℝ)| ≤ H d * 3 := by
  classical
  constructor
  · intro hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    intro d i
    have h := (mem_rectangular_zero_radius_iff (fun _ : Unit ⊕ α => H d) 3 (w d)).mp
      (Fintype.mem_piFinset.mp hw d) i
    simpa only [spatialStar_unstar] using h
  · intro hv
    apply Finset.mem_image.mpr
    refine ⟨fun d => spatialStar (v d), ?_, ?_⟩
    · apply Fintype.mem_piFinset.mpr
      intro d
      exact (mem_rectangular_zero_radius_iff (fun _ : Unit ⊕ α => H d) 3 _).mpr (hv d)
    · funext d
      exact spatialUnstar_star (v d)

theorem mem_commonSpatialWindow_scaled_iff {X α : Type*} [Fintype X] [Fintype α]
    (H : X → ℝ) (hH : ∀ d, 0 < H d) (v : X → (Unit ⊕ α) → ℤ) :
    v ∈ commonSpatialWindow H ↔ ∀ d i, |((spatialStar (v d) i : ℤ) : ℝ) / H d| ≤ 3 := by
  rw [mem_commonSpatialWindow_iff]
  simp only [abs_div, abs_of_pos (hH _), div_le_iff₀ (hH _), mul_comm]

theorem commonSpatialWindow_card {X α : Type*} [Fintype X] [Fintype α]
    (H T : X → ℝ) {W L : ℝ} (hH : ∀ d, 1 ≤ H d)
    (hL : L ≠ 0) (hscale : ∀ d, H d = (1 + W) * T d) :
    ((commonSpatialWindow (α := α) H).card : ℝ) ≤
      (7 ^ Fintype.card (X × (Unit ⊕ α)) * (((1 + W) / L) ^ Fintype.card α) ^ Fintype.card X) *
        ∏ d, ∏ i, physicalSpatialOutputScale α (H d) (T d) L i := by
  apply spatialStarWindow_card_anisotropic _ H T hH hL hscale
  intro v hv
  exact (mem_commonSpatialWindow_scaled_iff H (fun d => zero_lt_one.trans_le (hH d)) v).mp hv

theorem centeredPhysicalCubeWindow_subset_common {K X α : Type*}
    [Fintype K] [Fintype X] [Fintype α]
    (root : K → ℤ) (D : Matrix α K ℤ) (Q : Option K × X → ℝ) (H T : X → ℝ)
    {W : ℝ} (hW : 0 ≤ W) (hH : ∀ d, 0 < H d) (hT : ∀ d, 0 ≤ T d)
    (hscale : ∀ d, H d = (1 + W) * T d)
    (hQ : ∀ d, (fun k => Q (k, d)) = physicalSpatialInputScale K (H d) (T d))
    (hroot : (∑ k, |(root k : ℝ)|) ≤ W)
    (hD : ∀ i, (∑ k, |(D i k : ℝ)|) ≤ W) :
    centeredPhysicalCubeWindow root D Q ⊆ commonSpatialWindow H := by
  intro v hv
  exact (mem_commonSpatialWindow_scaled_iff H hH v).mpr
    (centeredPhysicalCubeWindow_star_bound root D Q H T hW hH hT hscale hQ hroot hD v hv)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

theorem spatialStar_add {I R : Type*} [AddCommMonoid R]
    (v w : (Unit ⊕ I) → R) : spatialStar (v + w) = spatialStar v + spatialStar w := by
  funext i
  cases i with
  | inl i => rfl
  | inr i => simp only [spatialStar, Sum.elim_inr, Pi.add_apply]; abel

namespace BooleanCubeKernel

open scoped BigOperators

noncomputable def spatialWindow {X α : Type*} [Fintype X] [Fintype α]
    (H : X → ℝ) (b : ℝ) : Finset (X → (Unit ⊕ α) → ℤ) := by
  classical
  exact (Fintype.piFinset (fun d => rectangularWeightIndices 0 (fun _ : Unit ⊕ α => H d) b)).image
    (fun w d => spatialUnstar (w d))

theorem spatialWindow_three {X α : Type*} [Fintype X] [Fintype α] (H : X → ℝ) :
    spatialWindow (α := α) H 3 = commonSpatialWindow H := rfl

theorem mem_spatialWindow_iff {X α : Type*} [Fintype X] [Fintype α]
    (H : X → ℝ) (b : ℝ) (v : X → (Unit ⊕ α) → ℤ) :
    v ∈ spatialWindow H b ↔ ∀ d i, |((spatialStar (v d) i : ℤ) : ℝ)| ≤ H d * b := by
  classical
  constructor
  · intro hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    intro d i
    have h := (mem_rectangular_zero_radius_iff (fun _ : Unit ⊕ α => H d) b (w d)).mp
      (Fintype.mem_piFinset.mp hw d) i
    simpa only [spatialStar_unstar] using h
  · intro hv
    apply Finset.mem_image.mpr
    refine ⟨fun d => spatialStar (v d), ?_, ?_⟩
    · apply Fintype.mem_piFinset.mpr
      intro d
      exact (mem_rectangular_zero_radius_iff (fun _ : Unit ⊕ α => H d) b _).mpr (hv d)
    · funext d
      exact spatialUnstar_star (v d)

theorem mem_spatialWindow_scaled_iff {X α : Type*} [Fintype X] [Fintype α]
    (H : X → ℝ) (hH : ∀ d, 0 < H d) (b : ℝ) (v : X → (Unit ⊕ α) → ℤ) :
    v ∈ spatialWindow H b ↔ ∀ d i, |((spatialStar (v d) i : ℤ) : ℝ) / H d| ≤ b := by
  rw [mem_spatialWindow_iff]
  simp only [abs_div, abs_of_pos (hH _), div_le_iff₀ (hH _), mul_comm]

theorem spatialWindow_add {X α : Type*} [Fintype X] [Fintype α]
    (H : X → ℝ) {a b : ℝ} {v s : X → (Unit ⊕ α) → ℤ}
    (hv : v ∈ spatialWindow H a) (hs : s ∈ spatialWindow H b) :
    v + s ∈ spatialWindow H (a + b) := by
  apply (mem_spatialWindow_iff H (a+b) _).mpr
  intro d i
  change |((spatialStar (v d + s d) i : ℤ) : ℝ)| ≤ _
  rw [spatialStar_add, Pi.add_apply, Int.cast_add]
  calc
    _ ≤ |((spatialStar (v d) i : ℤ) : ℝ)| + |((spatialStar (s d) i : ℤ) : ℝ)| := abs_add_le _ _
    _ ≤ H d * a + H d * b := add_le_add
      ((mem_spatialWindow_iff H a v).mp hv d i) ((mem_spatialWindow_iff H b s).mp hs d i)
    _ = _ := (mul_add _ _ _).symm

theorem spatialWindow_of_coordinate_bound {X α : Type*} [Fintype X] [Fintype α]
    (H : X → ℝ) (hH : ∀ d, 0 ≤ H d) {t : ℝ} (ht : 0 ≤ t)
    (s : X → (Unit ⊕ α) → ℤ) (hs : ∀ d i, |(s d i : ℝ)| ≤ H d * t) :
    s ∈ spatialWindow H (2*t) := by
  apply (mem_spatialWindow_iff H (2*t) s).mpr
  intro d i
  cases i with
  | inl i =>
    change |(s d (.inl ()) : ℝ)| ≤ _
    nlinarith [hs d (.inl ()), mul_nonneg (hH d) ht]
  | inr i =>
    change |((s d (.inl ()) + s d (.inr i) : ℤ) : ℝ)| ≤ _
    rw [Int.cast_add]
    exact (abs_add_le _ _).trans (by nlinarith [hs d (.inl ()), hs d (.inr i)])

theorem spatialWindow_card {X α : Type*} [Fintype X] [Fintype α]
    (H : X → ℝ) (hH : ∀ d, 1 ≤ H d) {b : ℝ} (hb : 0 ≤ b) :
    ((spatialWindow (α := α) H b).card : ℝ) ≤
      (2*b+1) ^ Fintype.card (X × (Unit ⊕ α)) * (∏ d, ∏ _i : Unit ⊕ α, H d) := by
  classical
  let F : (X → (Unit ⊕ α) → ℤ) → (X × (Unit ⊕ α) → ℤ) :=
    fun v z => spatialStar (v z.1) z.2
  have hinj : Function.Injective F := by
    intro v w h
    funext d
    have he : spatialStar (v d) = spatialStar (w d) := funext (fun i => congrFun h (d, i))
    have hu := congrArg spatialUnstar he
    simpa only [spatialUnstar_star] using hu
  have hinto : (spatialWindow H b).image F ⊆
      rectangularWeightIndices 0 (fun z : X × (Unit ⊕ α) => H z.1) b := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    apply (mem_rectangular_zero_radius_iff _ b _).mpr
    intro z
    exact (mem_spatialWindow_iff H b v).mp hv z.1 z.2
  have hc : (spatialWindow (α := α) H b).card ≤
      (rectangularWeightIndices 0 (fun z : X × (Unit ⊕ α) => H z.1) b).card := by
    rw [← Finset.card_image_of_injective _ hinj]
    exact Finset.card_le_card hinto
  apply (Nat.cast_le.mpr hc).trans
  simpa only [Fintype.prod_prod_type] using
    rectangularWeightIndices_card_le (0 : X × (Unit ⊕ α) → ℝ)
      (fun z => H z.1) (fun z => hH z.1) hb

theorem spatialWindow_card_anisotropic {X α : Type*} [Fintype X] [Fintype α]
    (H T : X → ℝ) {W L b : ℝ} (hH : ∀ d, 1 ≤ H d) (hb : 0 ≤ b)
    (hL : L ≠ 0) (hscale : ∀ d, H d = (1 + W) * T d) :
    ((spatialWindow (α := α) H b).card : ℝ) ≤
      ((2*b+1) ^ Fintype.card (X × (Unit ⊕ α)) *
        (((1+W)/L) ^ Fintype.card α) ^ Fintype.card X) *
      ∏ d, ∏ i, physicalSpatialOutputScale α (H d) (T d) L i := by
  have h := spatialWindow_card (α := α) H hH hb
  rw [physicalSpatial_uniform_volume H T hL hscale, ← mul_assoc] at h
  exact h

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3

theorem spatialStar_neg {I R : Type*} [AddCommGroup R] (v : (Unit ⊕ I) → R) :
    spatialStar (-v) = -spatialStar v := by
  funext i
  cases i with
  | inl i => rfl
  | inr i => simp only [spatialStar, Sum.elim_inr, Pi.neg_apply, neg_add]

namespace BooleanCubeKernel

variable {X I : Type*} [Fintype X] [Fintype I]

theorem spatialWindow_radius_mono (H : X → ℝ) (hH : ∀ x, 0 ≤ H x) {a b : ℝ} (hab : a ≤ b) :
    spatialWindow (α := I) H a ⊆ spatialWindow H b := by
  intro v hv
  apply (mem_spatialWindow_iff H b v).2
  intro x i
  exact ((mem_spatialWindow_iff H a v).1 hv x i).trans (mul_le_mul_of_nonneg_left hab (hH x))

theorem spatialWindow_neg (H : X → ℝ) (a : ℝ) (v : X → (Unit ⊕ I) → ℤ)
    (hv : v ∈ spatialWindow H a) : -v ∈ spatialWindow H a := by
  apply (mem_spatialWindow_iff H a (-v)).2
  intro x i
  change |((spatialStar (-(v x)) i : ℤ) : ℝ)| ≤ _
  rw [spatialStar_neg, Pi.neg_apply, Int.cast_neg, abs_neg]
  exact (mem_spatialWindow_iff H a v).1 hv x i

theorem spatialWeight_shift_global (H : X → ℝ) (hH : ∀ x, 0 ≤ H x)
    (f : (X → (Unit ⊕ I) → ℤ) → ℂ) {a b e E : ℝ} (he : 0 ≤ e) (hE : 0 ≤ E)
    (hab : a + e ≤ b)
    (hf : ∀ v, v ∉ spatialWindow H a → f v = 0)
    (s : X → (Unit ⊕ I) → ℤ) (hs : s ∈ spatialWindow H e)
    (hoverlap : ∀ v, v ∈ spatialWindow H b → v + s ∈ spatialWindow H b → ‖f (v + s) - f v‖ ≤ E) :
    ∀ v, ‖f (v + s) - f v‖ ≤ E := by
  have hab' : a ≤ b := le_trans (le_add_of_nonneg_right he) hab
  have hsmall := spatialWindow_radius_mono (I := I) H hH hab'
  have hlarge := spatialWindow_radius_mono (I := I) H hH hab
  intro v
  by_cases hv : v ∈ spatialWindow H b
  · by_cases hvs : v + s ∈ spatialWindow H b
    · exact hoverlap v hv hvs
    · have hzero₁ : f (v + s) = 0 := hf _ (fun h => hvs (hsmall h))
      have hzero₀ : f v = 0 := hf _ (fun h => hvs (hlarge (spatialWindow_add H h hs)))
      rw [hzero₁, hzero₀, sub_self, norm_zero]
      exact hE
  · have hzero₀ : f v = 0 := hf _ (fun h => hv (hsmall h))
    have hzero₁ : f (v + s) = 0 := by
      apply hf
      intro h
      have hback := hlarge (spatialWindow_add H h (spatialWindow_neg H e s hs))
      have hid : v + s + -s = v := by abel
      rw [hid] at hback
      exact hv hback
    rw [hzero₁, hzero₀, sub_self, norm_zero]
    exact hE

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem finite_window_sum_eq_of_support {V : Type*} (s t : Finset V) (f : V → ℂ)
    (hs : ∀ v ∈ s, v ∉ t → f v = 0) (ht : ∀ v ∈ t, v ∉ s → f v = 0) :
    (∑ v ∈ s, f v) = ∑ v ∈ t, f v := by
  have hleft : (∑ v ∈ s ∩ t, f v) = ∑ v ∈ s, f v :=
    Finset.sum_subset Finset.inter_subset_left (fun v hv hn => hs v hv
      (fun h => hn (Finset.mem_inter.mpr ⟨hv, h⟩)))
  have hright : (∑ v ∈ s ∩ t, f v) = ∑ v ∈ t, f v :=
    Finset.sum_subset Finset.inter_subset_right (fun v hv hn => ht v hv
      (fun h => hn (Finset.mem_inter.mpr ⟨h, hv⟩)))
  exact hleft.symm.trans hright

namespace BooleanCubeKernel

variable {X I : Type*} [Fintype X] [Fintype I]

theorem spatialWeight_shifted_window_eq (H : X → ℝ) (hH : ∀ x, 0 ≤ H x)
    (f φ : (X → (Unit ⊕ I) → ℤ) → ℂ) {a b e : ℝ} (he : 0 ≤ e) (hab : a + e ≤ b)
    (hf : ∀ v, v ∉ spatialWindow H a → f v = 0)
    (s : X → (Unit ⊕ I) → ℤ) (hs : s ∈ spatialWindow H e) :
    (∑ v ∈ (spatialWindow H b).image (fun w => w + s), f (v - s) * φ v) =
      ∑ v ∈ spatialWindow H b, f (v - s) * φ v := by
  have hsmall := spatialWindow_radius_mono (I := I) H hH
    (le_trans (le_add_of_nonneg_right he) hab)
  have hlarge := spatialWindow_radius_mono (I := I) H hH hab
  apply finite_window_sum_eq_of_support
  · intro v _ hn
    have hz : f (v - s) = 0 := by
      apply hf
      intro h
      have hmem := hlarge (spatialWindow_add H h hs)
      rw [sub_add_cancel] at hmem
      exact hn hmem
    rw [hz, zero_mul]
  · intro v _ hn
    have hz : f (v - s) = 0 := by
      apply hf
      intro h
      exact hn (Finset.mem_image.mpr ⟨v - s, hsmall h, sub_add_cancel v s⟩)
    rw [hz, zero_mul]

theorem spatialWeight_shifted_window_error (H : X → ℝ) (hH : ∀ x, 0 ≤ H x)
    (f φ : (X → (Unit ⊕ I) → ℤ) → ℂ) {a b e E : ℝ} (he : 0 ≤ e) (hab : a + e ≤ b)
    (hf : ∀ v, v ∉ spatialWindow H a → f v = 0)
    (s : X → (Unit ⊕ I) → ℤ) (hs : s ∈ spatialWindow H e)
    (hshift : ∀ v, ‖f (v + s) - f v‖ ≤ E) :
    ‖(∑ v ∈ (spatialWindow H b).image (fun w => w + s), f (v - s) * φ v) -
      ∑ v ∈ spatialWindow H b, f v * φ v‖ ≤ E * ∑ v ∈ spatialWindow H b, ‖φ v‖ := by
  rw [spatialWeight_shifted_window_eq H hH f φ he hab hf s hs, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro v _
  rw [← sub_mul, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  simpa only [sub_add_cancel, norm_sub_rev] using hshift (v - s)

theorem spatialWeight_mean_shifted_window_error {Ω : Type*} [Fintype Ω]
    (p : FiniteProbabilityWeights Ω) (H : X → ℝ) (hH : ∀ x, 0 ≤ H x)
    (f φ : Ω → (X → (Unit ⊕ I) → ℤ) → ℂ) {a b e E Z : ℝ}
    (he : 0 ≤ e) (hab : a + e ≤ b) (hZ : 0 < Z)
    (hf : ∀ y, p.weight y ≠ 0 → ∀ v, v ∉ spatialWindow H a → f y v = 0)
    (s : Ω → X → (Unit ⊕ I) → ℤ)
    (hs : ∀ y, p.weight y ≠ 0 → s y ∈ spatialWindow H e)
    (hshift : ∀ y, p.weight y ≠ 0 → ∀ v, ‖f y (v + s y) - f y v‖ ≤ E) :
    ‖p.complexMean (fun y => ∑ v ∈ (spatialWindow H b).image (fun w => w + s y),
        f y (v - s y) * φ y v) / (Z : ℂ) -
      p.complexMean (fun y => ∑ v ∈ spatialWindow H b, f y v * φ y v) / (Z : ℂ)‖ ≤
      E * p.mean (fun y => ∑ v ∈ spatialWindow H b, ‖φ y v‖) / Z := by
  rw [← sub_div, norm_div, Complex.norm_real, Real.norm_of_nonneg hZ.le]
  apply div_le_div_of_nonneg_right _ hZ.le
  have h := p.norm_complexMean_sub_le _ _ _ (fun y hy =>
    spatialWeight_shifted_window_error H hH (f y) (φ y) he hab (hf y hy) (s y) (hs y hy) (hshift y hy))
  simpa only [FiniteProbabilityWeights.mean_const_mul] using h

end BooleanCubeKernel
end Erdos3

end

end OAI

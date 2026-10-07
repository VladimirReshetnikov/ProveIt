import OAI.Combinatorics.Progressions.Geometry.PhysicalSpatialScales

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Matrix

def centeredPhysicalCubeMap {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (z : Option K × X → ℤ) : X → (Unit ⊕ α) → ℤ :=
  fun d => physicalCubeCoefficient root D *ᵥ (fun k => z (k, d))

theorem centeredPhysicalCubeMap_eq {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) :
    centeredPhysicalCubeMap (X := X) root D = physicalCubeRootDifferences root D 0 := by
  funext z d i
  cases i <;> simp only [centeredPhysicalCubeMap, physicalCubeRootDifferences,
    physicalCubeOffset, Pi.zero_apply, zero_add, Matrix.mulVec, dotProduct]

noncomputable def centeredPhysicalCubeWindow {K X α : Type*}
    [Fintype K] [Fintype X] [Fintype α]
    (root : K → ℤ) (D : Matrix α K ℤ) (Q : Option K × X → ℝ) : Finset (X → (Unit ⊕ α) → ℤ) :=
  (rectangularWeightIndices 0 Q 1).image (centeredPhysicalCubeMap root D)

theorem centeredPhysicalCubeMap_mem_window {K X α : Type*}
    [Fintype K] [Fintype X] [Fintype α]
    (root : K → ℤ) (D : Matrix α K ℤ) (Q : Option K × X → ℝ)
    (z : Option K × X → ℤ) (hz : z ∈ rectangularWeightIndices 0 Q 1) :
    centeredPhysicalCubeMap root D z ∈ centeredPhysicalCubeWindow root D Q := by
  classical
  exact Finset.mem_image.mpr ⟨z, hz, rfl⟩

theorem spatialStarVertex_root_sum {K α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) {W : ℝ} (hW : 0 ≤ W)
    (hroot : (∑ k, |(root k : ℝ)|) ≤ W)
    (hD : ∀ i, (∑ k, |(D i k : ℝ)|) ≤ W) (i : Unit ⊕ α) :
    (∑ k, |(integerAffineCube root D (spatialStarVertex i) k : ℝ)|) ≤ 2 * W := by
  cases i with
  | inl i =>
    simpa only [spatialStarVertex, Sum.elim_inl, integerAffineCube, Finset.sum_empty,
      add_zero] using hroot.trans (by linarith : W ≤ 2 * W)
  | inr i =>
    simp only [spatialStarVertex, Sum.elim_inr, integerAffineCube, Finset.sum_singleton, Int.cast_add]
    calc
      _ ≤ ∑ k, (|(root k : ℝ)| + |(D i k : ℝ)|) :=
        Finset.sum_le_sum (fun _ _ => abs_add_le _ _)
      _ = (∑ k, |(root k : ℝ)|) + ∑ k, |(D i k : ℝ)| := Finset.sum_add_distrib
      _ ≤ 2 * W := by linarith [hD i]

theorem centeredPhysicalCubeWindow_star_bound {K X α : Type*}
    [Fintype K] [Fintype X] [Fintype α]
    (root : K → ℤ) (D : Matrix α K ℤ) (Q : Option K × X → ℝ) (H T : X → ℝ)
    {W : ℝ} (hW : 0 ≤ W) (hH : ∀ d, 0 < H d) (hT : ∀ d, 0 ≤ T d)
    (hscale : ∀ d, H d = (1 + W) * T d)
    (hQ : ∀ d, (fun k => Q (k, d)) = physicalSpatialInputScale K (H d) (T d))
    (hroot : (∑ k, |(root k : ℝ)|) ≤ W)
    (hD : ∀ i, (∑ k, |(D i k : ℝ)|) ≤ W)
    (v : X → (Unit ⊕ α) → ℤ) (hv : v ∈ centeredPhysicalCubeWindow root D Q) :
    ∀ d i, |((spatialStar (v d) i : ℤ) : ℝ) / H d| ≤ 3 := by
  classical
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hv
  intro d i
  have hb := integerPhysicalSite_abs_bound (integerAffineCube root D (spatialStarVertex i)) Q z
    (rectangularWeightIndices_zero_bound Q hz) d
  have hq0 : Q (none, d) = H d := congrFun (hQ d) none
  have hqs (k : K) : Q (some k, d) = T d := congrFun (hQ d) (some k)
  simp only [physicalSiteWidth, hq0, hqs, ← Finset.sum_mul] at hb
  have hs := mul_le_mul_of_nonneg_right (spatialStarVertex_root_sum root D hW hroot hD i) (hT d)
  have hbound : |(integerPhysicalSite (integerAffineCube root D (spatialStarVertex i)) z d : ℝ)| ≤
      3 * H d := by nlinarith [hscale d, hT d]
  rw [centeredPhysicalCubeMap_eq, physicalCubeRootDifferences_star]
  simpa only [jointIntegerPhysicalSite, zero_add, abs_div, abs_of_pos (hH d)] using
    (div_le_iff₀ (hH d)).mpr hbound

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem spatialStarWindow_card {X α : Type*} [Fintype X] [Fintype α]
    (S : Finset (X → (Unit ⊕ α) → ℤ)) (H : X → ℝ) (hH : ∀ d, 1 ≤ H d)
    (hs : ∀ v ∈ S, ∀ d i, |((spatialStar (v d) i : ℤ) : ℝ) / H d| ≤ 3) :
    (S.card : ℝ) ≤ 7 ^ Fintype.card (X × (Unit ⊕ α)) * (∏ d, ∏ _i : Unit ⊕ α, H d) := by
  classical
  let : DecidableEq (X × (Unit ⊕ α)) := Classical.decEq _
  let F : (X → (Unit ⊕ α) → ℤ) → (X × (Unit ⊕ α) → ℤ) :=
    fun v z => spatialStar (v z.1) z.2
  have hinj : Function.Injective F := by
    intro v w h
    funext d
    have he : spatialStar (v d) = spatialStar (w d) := funext (fun i => congrFun h (d, i))
    have hu := congrArg spatialUnstar he
    simpa only [spatialUnstar_star] using hu
  have hinto : S.image F ⊆ rectangularWeightIndices 0 (fun z : X × (Unit ⊕ α) => H z.1) 3 := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    apply Fintype.mem_piFinset.mpr
    intro z
    have hp : 0 < H z.1 := zero_lt_one.trans_le (hH z.1)
    have hb : |((F v z : ℤ) : ℝ)| ≤ H z.1 * 3 := by
      have h := hs v hv z.1 z.2
      rw [abs_div, abs_of_pos hp, div_le_iff₀ hp] at h
      simpa only [F, mul_comm] using h
    change F v z ∈ sampledWeightIndices 0 (H z.1) 3
    simp only [sampledWeightIndices, zero_sub, zero_add, Finset.mem_Icc]
    exact ⟨Int.ceil_le.mpr (abs_le.mp hb).1, Int.le_floor.mpr (abs_le.mp hb).2⟩
  have hc : S.card ≤ (rectangularWeightIndices 0 (fun z : X × (Unit ⊕ α) => H z.1) 3).card := by
    rw [← Finset.card_image_of_injective S hinj]
    exact Finset.card_le_card hinto
  apply (Nat.cast_le.mpr hc).trans
  simpa only [show 2 * (3 : ℝ) + 1 = 7 by norm_num, Fintype.prod_prod_type] using
    rectangularWeightIndices_card_le (0 : X × (Unit ⊕ α) → ℝ)
      (fun z => H z.1) (fun z => hH z.1) (by norm_num : (0 : ℝ) ≤ 3)

theorem physicalSpatial_uniform_volume {X α : Type*} [Fintype X] [Fintype α]
    (H T : X → ℝ) {W L : ℝ} (hL : L ≠ 0) (hscale : ∀ d, H d = (1 + W) * T d) :
    (∏ d, ∏ _i : Unit ⊕ α, H d) =
      (((1 + W) / L) ^ Fintype.card α) ^ Fintype.card X *
        ∏ d, ∏ i, physicalSpatialOutputScale α (H d) (T d) L i := by
  have hrow (d) : (∏ _i : Unit ⊕ α, H d) =
      ((1 + W) / L) ^ Fintype.card α * ∏ i, physicalSpatialOutputScale α (H d) (T d) L i := by
    simp only [Fintype.prod_sum_type, physicalSpatialOutputScale, Sum.elim_inl, Sum.elim_inr,
      Finset.prod_const, Finset.card_univ, Fintype.card_unique, pow_one]
    have he : (1 + W) / L * (L * T d) = H d := by rw [hscale d]; field_simp
    rw [mul_left_comm _ (H d), ← mul_pow, he]
    simp only [Fintype.card_sum, Fintype.card_unique, pow_add, pow_one]
  simp_rw [hrow]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ]

theorem spatialStarWindow_card_anisotropic {X α : Type*} [Fintype X] [Fintype α]
    (S : Finset (X → (Unit ⊕ α) → ℤ)) (H T : X → ℝ) {W L : ℝ}
    (hH : ∀ d, 1 ≤ H d) (hL : L ≠ 0) (hscale : ∀ d, H d = (1 + W) * T d)
    (hs : ∀ v ∈ S, ∀ d i, |((spatialStar (v d) i : ℤ) : ℝ) / H d| ≤ 3) :
    (S.card : ℝ) ≤
      (7 ^ Fintype.card (X × (Unit ⊕ α)) * (((1 + W) / L) ^ Fintype.card α) ^ Fintype.card X) *
        ∏ d, ∏ i, physicalSpatialOutputScale α (H d) (T d) L i := by
  have h := spatialStarWindow_card S H hH hs
  rw [physicalSpatial_uniform_volume H T hL hscale, ← mul_assoc] at h
  exact h

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

theorem physicalSpatial_ambient_volume_ratio {X : Type*} [Fintype X]
    (dim : ℕ) (N H T : X → ℝ) {W L : ℝ}
    (hL : 0 < L) (hH : ∀ x, 0 < H x) (hT : ∀ x, 0 < T x)
    (hscale : ∀ x, H x = (1 + W) * T x) :
    (∏ x, N x) ^ (dim + 1) /
        (∏ x, ∏ i, physicalSpatialOutputScale (Fin dim) (H x) (T x) L i) =
      (∏ x, (N x / H x) ^ (dim + 1)) * (((1 + W) / L) ^ dim) ^ Fintype.card X := by
  have hvolume : 0 < ∏ x, ∏ i, physicalSpatialOutputScale (Fin dim) (H x) (T x) L i :=
    Finset.prod_pos (fun x _ => Finset.prod_pos (fun i _ => physicalSpatialOutputScale_pos
      (Fin dim) (hH x) (hT x) hL i))
  have hbase : (∏ x, H x) ^ (dim + 1) ≠ 0 :=
    (pow_pos (Finset.prod_pos (fun x _ => hH x)) _).ne'
  have hvol := physicalSpatial_uniform_volume (α := Fin dim) H T hL.ne' hscale
  have hvol' : (∏ x, H x) ^ (dim + 1) =
      (((1 + W) / L) ^ dim) ^ Fintype.card X *
        (∏ x, ∏ i, physicalSpatialOutputScale (Fin dim) (H x) (T x) L i) := by
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_sum, Fintype.card_unique,
      Fintype.card_fin, Nat.add_comm 1 dim, ← Finset.prod_pow] using hvol
  have hratio : (∏ x, (N x / H x) ^ (dim + 1)) =
      (∏ x, N x) ^ (dim + 1) / (∏ x, H x) ^ (dim + 1) := by
    rw [Finset.prod_pow, Finset.prod_div_distrib, div_pow]
  rw [hratio]
  apply (div_eq_iff hvolume.ne').2
  rw [mul_assoc, ← hvol', div_mul_cancel₀ _ hbase]

theorem trimmedSpatial_ambient_volume_ratio {X : Type*} [Fintype X]
    (dim : ℕ) (N q : X → ℕ) {W τ L : ℝ}
    (hW : 0 ≤ W) (hτ : 0 < τ) (hL : 0 < L) (hN : ∀ x, 0 < N x) (hq : ∀ x, 0 < q x) :
    (∏ x, (N x : ℝ)) ^ (dim + 1) /
        (∏ x, ∏ i, physicalSpatialOutputScale (Fin dim) (trimmedSpatialRootScale τ N q x)
          (trimmedSpatialSlopeScale W τ N q x) L i) =
      (∏ x, (8 * (q x : ℝ) / τ) ^ (dim + 1)) * (((1 + W) / L) ^ dim) ^ Fintype.card X := by
  have hscales (x : X) := trimmedSpatial_scales_pos hW hτ N q x (hN x) (hq x)
  rw [physicalSpatial_ambient_volume_ratio dim (fun x => (N x : ℝ))
    (trimmedSpatialRootScale τ N q) (trimmedSpatialSlopeScale W τ N q) hL
    (fun x => (hscales x).1) (fun x => (hscales x).2) (trimmedSpatial_scale_ratio (τ := τ) hW N q)]
  congr 1
  apply Finset.prod_congr rfl
  intro x _
  congr 1
  have hn : (N x : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hN x).ne'
  have hq' : (q x : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hq x).ne'
  unfold trimmedSpatialRootScale
  field_simp [hn, hq', hτ.ne']

end Erdos3.BooleanCubeKernel

end

end OAI

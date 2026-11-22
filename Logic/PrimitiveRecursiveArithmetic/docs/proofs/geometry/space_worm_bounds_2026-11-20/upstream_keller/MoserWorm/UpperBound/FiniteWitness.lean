import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Convex.Between
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import MoserWorm.Common.Defs

/-!
# Finite witnesses for a compact cover

The placement compactness argument uses the closed unit ball of real continuous
linear endomorphisms of the plane.  It does not approximate the witness, perturb
its vertices, or change the covering set.
-/

open Set Metric

noncomputable section

namespace MoserWorm.UpperBound

/-- Set coverage, using exactly the rigid motions in `MoserWorm.Covers`. -/
def CoversSet (K S : Set Plane) : Prop :=
  ∃ g : Plane ≃ᵢ Plane, g '' S ⊆ K

theorem coversSet_trace_iff (K : Set Plane) (γ : ℝ → Plane) :
    CoversSet K (trace γ) ↔ Covers K γ := Iff.rfl

theorem CoversSet.mono {K S T : Set Plane} (h : CoversSet K T) (hST : S ⊆ T) :
    CoversSet K S := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g, (image_mono hST).trans hg⟩

theorem coversSet_convexHull_iff {K S : Set Plane} (hK : Convex ℝ K) :
    CoversSet K (convexHull ℝ S) ↔ CoversSet K S := by
  constructor
  · exact fun h => h.mono (subset_convexHull ℝ S)
  · rintro ⟨g, hg⟩
    refine ⟨g, ?_⟩
    have he := g.toRealAffineIsometryEquiv.toAffineEquiv.toAffineMap.image_convexHull S
    change g '' convexHull ℝ S = convexHull ℝ (g '' S) at he
    rw [he]
    exact convexHull_min hg hK

private abbrev MotionParameter := (Plane →L[ℝ] Plane) × Plane

private def motionSpace (K : Set Plane) : Set MotionParameter :=
  (closedBall 0 1 ×ˢ K) ∩ {p | ∀ x : Plane, ‖p.1 x‖ = ‖x‖}

private theorem motionSpace_compact {K : Set Plane} (hK : IsCompact K) :
    IsCompact (motionSpace K) := by
  apply ((isCompact_closedBall (0 : Plane →L[ℝ] Plane) 1).prod hK).inter_right
  have hclosed : ∀ x : Plane,
      IsClosed {p : MotionParameter | ‖p.1 x‖ = ‖x‖} := fun x =>
    isClosed_eq (by fun_prop) continuous_const
  simpa only [ofPred_forall] using isClosed_iInter hclosed

private def parameterIsometry (p : MotionParameter)
    (hp : ∀ x : Plane, ‖p.1 x‖ = ‖x‖) (x₀ : Plane) : Plane ≃ᵢ Plane :=
  let L : Plane →ₗᵢ[ℝ] Plane := ⟨p.1.toLinearMap, hp⟩
  let e := LinearIsometryEquiv.ofSurjective L
    (LinearMap.surjective_of_injective L.injective)
  ((IsometryEquiv.addRight (-x₀)).trans e.toIsometryEquiv).trans
    (IsometryEquiv.addRight p.2)

private theorem parameterIsometry_apply (p : MotionParameter)
    (hp : ∀ x : Plane, ‖p.1 x‖ = ‖x‖) (x₀ x : Plane) :
    parameterIsometry p hp x₀ x = p.1 (x - x₀) + p.2 := by
  rfl

/-- Compact placement: if every finite subset can be placed, so can the set.
No continuity or compactness assumption on the set being placed is needed. -/
theorem coversSet_of_finite_subsets {K S : Set Plane} (hK : IsCompact K)
    (hfin : ∀ F : Finset Plane, (F : Set Plane) ⊆ S → CoversSet K F) :
    CoversSet K S := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact ⟨IsometryEquiv.refl Plane, by simp⟩
  let T : S → Set MotionParameter := fun x => {p | p.1 (x - x₀) + p.2 ∈ K}
  have hT : ∀ x, IsClosed (T x) := fun x => hK.isClosed.preimage (by fun_prop)
  have hfinite : ∀ u : Finset S, (motionSpace K ∩ ⋂ x ∈ u, T x).Nonempty := by
    intro u
    let F : Finset Plane := insert x₀ (u.image Subtype.val)
    have hFS : (F : Set Plane) ⊆ S := by
      intro x hx
      simp only [F, Finset.mem_coe, Finset.mem_insert, Finset.mem_image] at hx
      rcases hx with rfl | ⟨y, _, rfl⟩
      · exact hx₀
      · exact y.property
    obtain ⟨g, hg⟩ := hfin F hFS
    let L : Plane →L[ℝ] Plane :=
      g.toRealLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap
    let p : MotionParameter := (L, g x₀)
    have hnorm : ∀ x : Plane, ‖L x‖ = ‖x‖ :=
      g.toRealLinearIsometryEquiv.norm_map
    have happly (x : Plane) : L (x - x₀) + g x₀ = g x := by
      change g.toRealLinearIsometryEquiv (x - x₀) + g x₀ = g x
      rw [map_sub, g.toRealLinearIsometryEquiv_apply,
        g.toRealLinearIsometryEquiv_apply]
      abel
    refine ⟨p, ⟨⟨?_, ?_⟩, hnorm⟩, ?_⟩
    · change dist L 0 ≤ 1
      rw [dist_zero_right]
      exact L.opNorm_le_bound (by norm_num) (fun x => by rw [hnorm]; simp)
    · exact hg ⟨x₀, by simp [F], rfl⟩
    · simp only [mem_iInter]
      intro x hx
      change L (x - x₀) + g x₀ ∈ K
      rw [happly]
      exact hg ⟨x, by simp [F, hx], rfl⟩
  obtain ⟨p, hp, hpT⟩ :=
    (motionSpace_compact hK).inter_iInter_nonempty T hT hfinite
  refine ⟨parameterIsometry p hp.2 x₀, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [parameterIsometry_apply]
  exact mem_iInter.mp hpT ⟨x, hx⟩

/-- An uncovered set has an uncovered finite subset, without any perturbation. -/
theorem exists_finite_uncovered {K S : Set Plane} (hK : IsCompact K)
    (hmiss : ¬ CoversSet K S) :
    ∃ F : Finset Plane, (F : Set Plane) ⊆ S ∧ ¬ CoversSet K F := by
  classical
  by_contra! h
  exact hmiss (coversSet_of_finite_subsets hK h)

/-- The finite-hull part of the paper's witness reduction, over the common arc
and covering definitions. -/
theorem exists_finite_uncovered_hull {K : Set Plane} (hK : IsCompact K)
    {γ : ℝ → Plane} (hmiss : ¬ Covers K γ) :
    ∃ F : Finset Plane, (F : Set Plane) ⊆ trace γ ∧
      ¬ CoversSet K (convexHull ℝ (F : Set Plane)) := by
  obtain ⟨F, hF, hmissF⟩ := exists_finite_uncovered hK hmiss
  exact ⟨F, hF, fun h => hmissF (h.mono (subset_convexHull ℝ _))⟩

/-- Extend a nonempty finite enumeration constantly after its final vertex. -/
def natExt {k : ℕ} (v : Fin (k + 1) → Plane) (i : ℕ) : Plane :=
  v ⟨min i k, by omega⟩

theorem natExt_of_le {k : ℕ} (v : Fin (k + 1) → Plane) {i : ℕ} (hi : i ≤ k) :
    natExt v i = v ⟨i, by omega⟩ := by simp [natExt, Nat.min_eq_left hi]

/-- The open Hamiltonian path length; there is no closing edge. -/
def pathLen (w : ℕ → Plane) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, dist (w i) (w (i + 1))

def permChain {k : ℕ} (v : Fin (k + 1) → Plane)
    (σ : Equiv.Perm (Fin (k + 1))) : ℕ → Plane := natExt (v ∘ σ)

theorem pathLen_congr {w w' : ℕ → Plane} {k : ℕ}
    (h : ∀ i ≤ k, w i = w' i) : pathLen w k = pathLen w' k := by
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  rw [h i (by omega), h (i + 1) (by omega)]

theorem pathLen_natExt {k : ℕ} (v : Fin (k + 1) → Plane) :
    pathLen (natExt v) k =
      ∑ j : Fin k, dist (v j.castSucc) (v j.succ) := by
  rw [pathLen, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  rw [natExt_of_le v (by omega), natExt_of_le v (by omega)]
  rfl

/-- A finite chord sum is bounded by the shared total-variation length. -/
theorem chord_sum_le_one {γ : ℝ → Plane} (hlen : arcLength γ = 1) {k : ℕ}
    (τ : Fin (k + 1) → ℝ) (hτ : Monotone τ) (hin : ∀ i, τ i ∈ I01) :
    ∑ j : Fin k, dist (γ (τ j.castSucc)) (γ (τ j.succ)) ≤ 1 := by
  let u : ℕ → ℝ := fun i => τ ⟨min i k, by omega⟩
  have humono : Monotone u := fun a b hab => hτ (by
    change min a k ≤ min b k
    exact min_le_min_right k hab)
  have hsum := eVariationOn.sum_le (f := γ) (s := I01) (n := k) humono
    (fun i => hin ⟨min i k, by omega⟩)
  change _ ≤ arcLength γ at hsum
  rw [hlen] at hsum
  have hconv :
      (∑ i ∈ Finset.range k, edist (γ (u (i + 1))) (γ (u i))) =
      ENNReal.ofReal (∑ i ∈ Finset.range k, dist (γ (u (i + 1))) (γ (u i))) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => dist_nonneg)]
    exact Finset.sum_congr rfl fun i _ => edist_dist _ _
  rw [hconv] at hsum
  have hreal := ENNReal.ofReal_le_one.mp hsum
  calc
    (∑ j : Fin k, dist (γ (τ j.castSucc)) (γ (τ j.succ))) =
        ∑ i ∈ Finset.range k, dist (γ (u (i + 1))) (γ (u i)) := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j _
      simp only [u, Nat.min_eq_left (by omega : (j : ℕ) + 1 ≤ k),
        Nat.min_eq_left (by omega : (j : ℕ) ≤ k)]
      exact dist_comm _ _
    _ ≤ 1 := hreal

/-- Choose one visit to each point, then enumerate the chosen parameters in
increasing order. Multiple visits by the curve cause no ambiguity. -/
theorem exists_parameter_enumeration {γ : ℝ → Plane} (V : Finset Plane)
    (hV : (V : Set Plane) ⊆ trace γ) (hne : V.Nonempty) :
    ∃ (k : ℕ) (τ : Fin (k + 1) → ℝ), Monotone τ ∧
      (∀ i, τ i ∈ I01) ∧ Function.Injective (γ ∘ τ) ∧
      Set.range (γ ∘ τ) = (V : Set Plane) := by
  classical
  have hsel : ∀ w : {x // x ∈ V}, ∃ t, t ∈ I01 ∧ γ t = (w : Plane) := by
    rintro ⟨w, hw⟩
    exact hV hw
  choose tsel htsel₁ htsel₂ using hsel
  have htinj : Function.Injective tsel := by
    intro w w' h
    apply Subtype.ext
    rw [← htsel₂ w, ← htsel₂ w', h]
  have hTcard : (V.attach.image tsel).card = V.card := by
    rw [Finset.card_image_of_injective _ htinj, Finset.card_attach]
  let k := V.card - 1
  have hpos := Finset.card_pos.mpr hne
  have hkcard : (V.attach.image tsel).card = k + 1 := by omega
  let ι := (V.attach.image tsel).orderIsoOfFin hkcard
  have hval : ∀ l : Fin (k + 1), ∃ w : {x // x ∈ V},
      tsel w = (ι l : ℝ) ∧ γ (ι l : ℝ) = (w : Plane) := by
    intro l
    obtain ⟨w, _, hw⟩ := Finset.mem_image.mp (ι l).2
    exact ⟨w, hw, by rw [← hw]; exact htsel₂ w⟩
  have hinj : Function.Injective (γ ∘ fun l : Fin (k + 1) => (ι l : ℝ)) := by
    intro l l' h
    obtain ⟨w, hw, hvl⟩ := hval l
    obtain ⟨w', hw', hvl'⟩ := hval l'
    have hww : w = w' := Subtype.ext (by rw [← hvl, ← hvl']; exact h)
    subst hww
    exact ι.injective (Subtype.ext (by rw [← hw, ← hw']))
  refine ⟨k, fun l => (ι l : ℝ), ?_, ?_, hinj, ?_⟩
  · intro a b hab
    exact ι.monotone hab
  · intro l
    change (ι l : ℝ) ∈ I01
    obtain ⟨w, hw, _⟩ := hval l
    rw [← hw]
    exact htsel₁ w
  · apply Set.eq_of_subset_of_ncard_le
    · rintro x ⟨l, rfl⟩
      obtain ⟨w, _, hw⟩ := hval l
      change γ (ι l : ℝ) ∈ V
      rw [hw]
      exact w.property
    · rw [Set.ncard_coe_finset, Set.ncard_range_of_injective hinj]
      simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
      omega
    · exact V.finite_toSet

/-- A shortest path visits every member exactly once. Minimality quantifies
over actual permutations, not over a preselected order class. -/
structure ShortestVertexPath (V : Set Plane) where
  edges : ℕ
  vertex : Fin (edges + 1) → Plane
  injective : Function.Injective vertex
  range_eq : Set.range vertex = V
  minimal : ∀ σ : Equiv.Perm (Fin (edges + 1)),
    pathLen (natExt vertex) edges ≤ pathLen (permChain vertex σ) edges

/-- A finite nonempty set of visited points has a shortest Hamiltonian path
whose length is at most the original unit curve's length. -/
theorem exists_shortest_vertex_path {γ : ℝ → Plane} (hγ : IsUnitArc γ)
    (V : Finset Plane) (hV : (V : Set Plane) ⊆ trace γ) (hne : V.Nonempty) :
    ∃ P : ShortestVertexPath (V : Set Plane), pathLen (natExt P.vertex) P.edges ≤ 1 := by
  classical
  obtain ⟨k, τ, hτ, hin, hinj, hrange⟩ := exists_parameter_enumeration V hV hne
  let v := γ ∘ τ
  obtain ⟨σ, _, hmin⟩ := Finset.exists_min_image Finset.univ
    (fun σ : Equiv.Perm (Fin (k + 1)) => pathLen (permChain v σ) k)
    Finset.univ_nonempty
  let P : ShortestVertexPath (V : Set Plane) :=
    { edges := k
      vertex := v ∘ σ
      injective := hinj.comp σ.injective
      range_eq := by
        rw [Set.range_comp, σ.surjective.range_eq, Set.image_univ]
        exact hrange
      minimal := fun ρ => by
        have h := hmin (σ * ρ) (Finset.mem_univ _)
        exact h }
  refine ⟨P, ?_⟩
  have hm := hmin (1 : Equiv.Perm (Fin (k + 1))) (Finset.mem_univ _)
  change pathLen (permChain v σ) k ≤ 1
  refine hm.trans ?_
  change pathLen (natExt v) k ≤ 1
  rw [pathLen_natExt]
  exact chord_sum_le_one hγ.2 τ hτ hin

/-- Extreme vertices of a finite convex hull are a subset of its generating
set and generate exactly the same hull. -/
theorem finite_hull_extreme_vertices (F : Finset Plane) :
    ∃ V : Finset Plane,
      (V : Set Plane) = extremePoints ℝ (convexHull ℝ (F : Set Plane)) ∧
      (V : Set Plane) ⊆ F ∧ convexHull ℝ (V : Set Plane) = convexHull ℝ (F : Set Plane) := by
  classical
  have hfinite := F.finite_toSet.subset
    (extremePoints_convexHull_subset (𝕜 := ℝ) (A := (F : Set Plane)))
  refine ⟨hfinite.toFinset, hfinite.coe_toFinset, ?_, ?_⟩
  · rw [hfinite.coe_toFinset]
    exact extremePoints_convexHull_subset
  · rw [hfinite.coe_toFinset]
    have he := closure_convexHull_extremePoints
      (F.finite_toSet.isCompact_convexHull ℝ) (convex_convexHull ℝ (F : Set Plane))
    rwa [(hfinite.isCompact_convexHull ℝ).isClosed.closure_eq] at he

/-- The finite extreme-vertex witness and its minimizing path. -/
theorem finite_witness {K : Set Plane} (hK : IsCompact K)
    {γ : ℝ → Plane} (hγ : IsUnitArc γ) (hmiss : ¬ Covers K γ) :
    ∃ V : Finset Plane, (V : Set Plane) ⊆ trace γ ∧
      (V : Set Plane) = extremePoints ℝ (convexHull ℝ (V : Set Plane)) ∧
      ¬ CoversSet K (convexHull ℝ (V : Set Plane)) ∧
      ∃ P : ShortestVertexPath (V : Set Plane), pathLen (natExt P.vertex) P.edges ≤ 1 := by
  obtain ⟨F, hF, hm⟩ := exists_finite_uncovered_hull hK hmiss
  obtain ⟨V, hVE, hVF, hHull⟩ := finite_hull_extreme_vertices F
  have hmV : ¬ CoversSet K (convexHull ℝ (V : Set Plane)) := by rwa [hHull]
  have hne : V.Nonempty := by
    by_contra hn
    have he : V = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    apply hmV
    refine ⟨IsometryEquiv.refl Plane, ?_⟩
    simp [he]
  refine ⟨V, hVF.trans hF, ?_, hmV,
    exists_shortest_vertex_path hγ V (hVF.trans hF) hne⟩
  rw [hHull]
  exact hVE

/-- Equal-distance pairs in the plane are related by an actual rigid motion. -/
theorem exists_isometry_map_pair {a b A B : Plane} (hd : dist a b = dist A B) :
    ∃ g : Plane ≃ᵢ Plane, g a = A ∧ g b = B := by
  by_cases hab : a = b
  · subst b
    have hAB : A = B := dist_eq_zero.mp (by simpa using hd.symm)
    subst B
    refine ⟨IsometryEquiv.addRight (A - a), ?_, ?_⟩ <;>
      change a + (A - a) = A <;> abel
  · have hz : b - a ≠ 0 := sub_ne_zero.mpr (fun h => hab h.symm)
    have hn : ‖(B - A) / (b - a)‖ = 1 := by
      rw [norm_div]
      have he : ‖B - A‖ = ‖b - a‖ := by
        simpa only [dist_eq_norm, norm_sub_rev] using hd.symm
      rw [he, div_self (norm_ne_zero_iff.mpr hz)]
    let u : Circle := ⟨(B - A) / (b - a), by
      simpa [Submonoid.unitSphere, Metric.mem_sphere, dist_zero_right] using hn⟩
    let g := ((IsometryEquiv.addRight (-a)).trans (rotation u).toIsometryEquiv).trans
      (IsometryEquiv.addRight A)
    refine ⟨g, ?_, ?_⟩
    · change ((B - A) / (b - a)) * (a + -a) + A = A
      simp
    · change ((B - A) / (b - a)) * (b + -a) + A = B
      rw [← sub_eq_add_neg, div_mul_cancel₀ _ hz]
      ring

/-- The unit-segment input required to exclude collinear witnesses. -/
def ContainsUnitSegment (K : Set Plane) : Prop :=
  ∃ A B : Plane, dist A B = 1 ∧ segment ℝ A B ⊆ K

theorem containsUnitSegment_of_dist_ge_one {K : Set Plane} (hK : Convex ℝ K)
    {A B : Plane} (hA : A ∈ K) (hB : B ∈ K) (hd : 1 ≤ dist A B) :
    ContainsUnitSegment K := by
  let d := ‖B - A‖
  have hd' : 1 ≤ d := by simpa only [d, dist_eq_norm, norm_sub_rev] using hd
  let C := A + d⁻¹ • (B - A)
  have hC : C ∈ segment ℝ A B := by
    rw [segment_eq_image_lineMap]
    refine ⟨d⁻¹, ⟨inv_nonneg.mpr (by linarith), inv_le_one_of_one_le₀ hd'⟩, ?_⟩
    simp [AffineMap.lineMap_apply, C]
    module
  have hAC : dist A C = 1 := by
    rw [dist_comm, dist_eq_norm]
    change ‖(A + d⁻¹ • (B - A)) - A‖ = 1
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (by linarith : 0 ≤ d))]
    change d⁻¹ * d = 1
    exact inv_mul_cancel₀ (by linarith)
  exact ⟨A, C, hAC, hK.segment_subset hA ((hK.segment_subset hA hB) hC)⟩

theorem coversSet_pair_of_unit_segment {K : Set Plane} (hK : ContainsUnitSegment K)
    {a b : Plane} (hd : dist a b ≤ 1) : CoversSet K ({a, b} : Set Plane) := by
  obtain ⟨A, B, hAB, hseg⟩ := hK
  let d := ‖b - a‖
  have hd0 : 0 ≤ d := norm_nonneg _
  have hd1 : d ≤ 1 := by simpa only [d, dist_eq_norm, norm_sub_rev] using hd
  have hunit : ‖B - A‖ = 1 := by
    simpa only [dist_eq_norm, norm_sub_rev] using hAB
  let C := A + d • (B - A)
  have hC : C ∈ segment ℝ A B := by
    rw [segment_eq_image_lineMap]
    refine ⟨d, ⟨hd0, hd1⟩, ?_⟩
    simp [AffineMap.lineMap_apply, C]
    module
  have hAC : dist a b = dist A C := by
    rw [dist_comm A C, dist_eq_norm C A]
    change dist a b = ‖(A + d • (B - A)) - A‖
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hd0, hunit, mul_one]
    exact dist_eq_norm' _ _
  obtain ⟨g, hga, hgb⟩ := exists_isometry_map_pair hAC
  refine ⟨g, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  rcases hx with rfl | rfl
  · rw [hga]
    exact hseg (left_mem_segment ℝ A B)
  · rw [hgb]
    exact hseg hC

theorem trace_dist_le_one {γ : ℝ → Plane} (hγ : IsUnitArc γ)
    {a b : Plane} (ha : a ∈ trace γ) (hb : b ∈ trace γ) : dist a b ≤ 1 := by
  obtain ⟨s, hs, rfl⟩ := ha
  obtain ⟨t, ht, rfl⟩ := hb
  have h := eVariationOn.edist_le γ hs ht
  change edist (γ s) (γ t) ≤ arcLength γ at h
  rw [hγ.2, edist_dist] at h
  exact ENNReal.ofReal_le_one.mp h

theorem collinear_extreme_subset_pair {V Q : Set Plane}
    (hV : V ⊆ extremePoints ℝ Q) (hcol : Collinear ℝ V)
    {a b : Plane} (ha : a ∈ V) (hb : b ∈ V) (hab : a ≠ b) :
    V ⊆ ({a, b} : Set Plane) := by
  intro c hc
  by_contra hn
  have hca : c ≠ a := by intro h; exact hn (by simp [h])
  have hcb : c ≠ b := by intro h; exact hn (by simp [h])
  have ha' := mem_extremePoints_iff_forall_segment.mp (hV ha)
  have hb' := mem_extremePoints_iff_forall_segment.mp (hV hb)
  have hc' := mem_extremePoints_iff_forall_segment.mp (hV hc)
  have htr : Collinear ℝ ({a, b, c} : Set Plane) := hcol.subset (by
    intro x hx
    rcases hx with rfl | rfl | rfl <;> assumption)
  rcases htr.wbtw_or_wbtw_or_wbtw with h | h | h
  · rcases hb'.2 a ha'.1 c hc'.1 (mem_segment_iff_wbtw.mpr h) with h | h
    · exact hab h
    · exact hcb h
  · rcases hc'.2 b hb'.1 a ha'.1 (mem_segment_iff_wbtw.mpr h) with h | h
    · exact hcb h.symm
    · exact hca h.symm
  · rcases ha'.2 c hc'.1 b hb'.1 (mem_segment_iff_wbtw.mpr h) with h | h
    · exact hca h
    · exact hab h.symm

/-- Strengthened witness: the unit segment excludes every collinear finite
extreme-vertex hull. All geometric inputs are explicit. -/
theorem finite_witness_noncollinear {K : Set Plane} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hsegment : ContainsUnitSegment K)
    {γ : ℝ → Plane} (hγ : IsUnitArc γ) (hmiss : ¬ Covers K γ) :
    ∃ V : Finset Plane, (V : Set Plane) ⊆ trace γ ∧
      (V : Set Plane) = extremePoints ℝ (convexHull ℝ (V : Set Plane)) ∧
      ¬ Collinear ℝ (V : Set Plane) ∧
      ¬ CoversSet K (convexHull ℝ (V : Set Plane)) ∧
      ∃ P : ShortestVertexPath (V : Set Plane), pathLen (natExt P.vertex) P.edges ≤ 1 := by
  classical
  obtain ⟨V, htrace, hext, hmissV, P, hlen⟩ := finite_witness hK hγ hmiss
  refine ⟨V, htrace, hext, ?_, hmissV, P, hlen⟩
  intro hcol
  let a := P.vertex 0
  have ha : a ∈ (V : Set Plane) := P.range_eq.subset (mem_range_self 0)
  have hcover : CoversSet K (V : Set Plane) := by
    by_cases hb : ∃ b ∈ (V : Set Plane), b ≠ a
    · obtain ⟨b, hb, hba⟩ := hb
      have hsub := collinear_extreme_subset_pair hext.subset hcol ha hb hba.symm
      exact (coversSet_pair_of_unit_segment hsegment
        (trace_dist_le_one hγ (htrace ha) (htrace hb))).mono hsub
    · apply (coversSet_pair_of_unit_segment hsegment (a := a) (b := a)
        (by simp)).mono
      intro x hx
      have he : x = a := by by_contra hn; exact hb ⟨x, hx, hn⟩
      simp [he]
  exact hmissV ((coversSet_convexHull_iff hconv).mpr hcover)

/-- A rigid motion transports the minimizing path with its visiting ranks and
its exact length unchanged. -/
def ShortestVertexPath.mapIsometry {V : Set Plane} (P : ShortestVertexPath V)
    (g : Plane ≃ᵢ Plane) : ShortestVertexPath (g '' V) where
  edges := P.edges
  vertex := g ∘ P.vertex
  injective := g.injective.comp P.injective
  range_eq := by rw [Set.range_comp, P.range_eq]
  minimal := by
    intro σ
    simpa only [pathLen, natExt, permChain, Function.comp_apply, g.dist_eq] using P.minimal σ

@[simp] theorem ShortestVertexPath.mapIsometry_length {V : Set Plane} (P : ShortestVertexPath V)
    (g : Plane ≃ᵢ Plane) :
    pathLen (natExt (P.mapIsometry g).vertex) (P.mapIsometry g).edges =
      pathLen (natExt P.vertex) P.edges := by
  simp only [mapIsometry, pathLen, natExt, Function.comp_apply, g.dist_eq]

/-- Uncoveredness is invariant under the normalization isometry. -/
theorem coversSet_isometry_image_iff (K S : Set Plane) (g : Plane ≃ᵢ Plane) :
    CoversSet K (g '' S) ↔ CoversSet K S := by
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨g.trans h, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hh ⟨g x, mem_image_of_mem g hx, rfl⟩
  · rintro ⟨h, hh⟩
    refine ⟨g.symm.trans h, ?_⟩
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    apply hh
    exact ⟨x, hx, by simp⟩

end MoserWorm.UpperBound

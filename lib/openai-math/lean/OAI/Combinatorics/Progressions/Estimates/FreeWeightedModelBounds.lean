import OAI.Combinatorics.Progressions.Nilpotent.FreeWeightedNilpotentLieAlgebra

namespace OAI

section

namespace Erdos3.FreeWeightedNilpotentLieAlgebra

variable (X : Type*) [Fintype X] (s : ℕ) (w : X → ℕ)

noncomputable def layerGenerators (d : ℕ) : Finset (FreeWeightedNilpotentLieAlgebra X s w) := by
  classical
  exact (FreeNilpotentLieAlgebra.weightedLayerGenerators X s w d).image (mk X s w)

theorem layer_eq_span (hw : ∀ x, 0 < w x) (d : ℕ) :
    (filtration X s w hw).layer d = Submodule.span ℚ (layerGenerators X s w d : Set _) := by
  classical
  change (FreeNilpotentLieAlgebra.weightedLayer X s w d).map (mk X s w).toLinearMap = _
  rw [FreeNilpotentLieAlgebra.weightedLayer_eq_span, Submodule.map_span]
  simp only [layerGenerators, Finset.coe_image]
  rfl

theorem layerGenerators_mem (hw : ∀ x, 0 < w x) (d : ℕ)
    (x : FreeWeightedNilpotentLieAlgebra X s w) (hx : x ∈ layerGenerators X s w d) :
    x ∈ (filtration X s w hw).layer d := by
  rw [layer_eq_span]
  exact Submodule.subset_span hx

noncomputable def layerFamily (hw : ∀ x, 0 < w x) (d : ℕ)
    (x : layerGenerators X s w d) : (filtration X s w hw).layer d :=
  ⟨x.val, layerGenerators_mem X s w hw d x.val x.property⟩

theorem layerFamily_span (hw : ∀ x, 0 < w x) (d : ℕ) :
    Submodule.span ℚ (Set.range (layerFamily X s w hw d)) = ⊤ := by
  apply (Submodule.span_range_subtype_eq_top_iff _ _).mpr
  have hrange : Set.range (Subtype.val : layerGenerators X s w d →
      FreeWeightedNilpotentLieAlgebra X s w) = (layerGenerators X s w d : Set _) := by
    ext x
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  rw [hrange]
  exact (layer_eq_span X s w hw d).symm

theorem layerGenerators_card_le (d : ℕ) :
    (layerGenerators X s w d).card ≤ (Fintype.card X + 2) ^ (3 ^ s) := by
  classical
  exact Finset.card_image_le.trans (FreeNilpotentLieAlgebra.weightedLayerGenerators_card_le X s w d)

end Erdos3.FreeWeightedNilpotentLieAlgebra

end

section

namespace Erdos3

open Module
open scoped Matrix

theorem exists_bounded_free_weighted_quotient (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (X : Type*) [Fintype X] (w : X → ℕ) (p : ℝ),
      0 ≤ p → (Fintype.card X : ℝ) ≤ p →
      (finrank ℚ (FreeNilpotentLieAlgebra X s) : ℝ) ≤ (p + C) ^ C ∧
      ∃ e : Basis (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s))) ℚ (FreeNilpotentLieAlgebra X s),
        (∀ i, e i ∈ FreeNilpotentLieAlgebra.treeGenerators X s) ∧
        (∀ x ∈ FreeNilpotentLieAlgebra.treeGenerators X s, ∀ i,
          rationalLogHeight (e.repr x i) ≤ (p + C) ^ C) ∧
        ∃ d : ℕ, d ≤ finrank ℚ (FreeNilpotentLieAlgebra X s) ∧ (d : ℝ) ≤ (p + C) ^ C ∧
          ∃ b : Basis (Fin d) ℚ (FreeWeightedNilpotentLieAlgebra X s w),
            ∃ D : Matrix (Fin d) (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s))) ℚ,
              ∃ S : Matrix (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s))) (Fin d) ℚ,
                LinearMap.toMatrix e b (FreeWeightedNilpotentLieAlgebra.mk X s w).toLinearMap = D ∧
                D * S = 1 ∧
                (∀ i j, rationalLogHeight (D i j) ≤ (p + C) ^ C) ∧
                (∀ i j, rationalLogHeight (S i j) ≤ (p + C) ^ C) ∧
                ∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ (p + C) ^ C := by
  obtain ⟨a, _, hsource⟩ := exists_free_nilpotent_source_basis s
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + (Q + 3) ^ 51)
  refine ⟨C, hC, ?_⟩
  intro X _ w p hp hX
  classical
  let B := (p + a) ^ a
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hsum : B + (B + 3) ^ 51 ≤ (p + C) ^ C := by
    simpa [Q, B, Polynomial.eval₂_pow] using hbudget p hp
  have hBC : B ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ (B + 3) ^ 51)).trans hsum
  have h51 : (B + 3) ^ 51 ≤ (p + C) ^ C := (le_add_of_nonneg_left hB).trans hsum
  have hsmall (k : ℕ) (hk : k ≤ 51) : (B + 1 + 2) ^ k ≤ (p + C) ^ C := by
    rw [show B + 1 + 2 = B + 3 by ring]
    exact (pow_le_pow_right₀ (by linarith only [hB]) hk).trans h51
  obtain ⟨hdim, hcount, e, he, hstructure, hgen⟩ := hsource X p hp hX
  let T := FreeNilpotentLieAlgebra.weightedLayerGenerators X s w (s + 1)
  let I := FreeNilpotentLieAlgebra.weightedLayerIdeal X s w (s + 1)
  let v : T → FreeNilpotentLieAlgebra X s := Subtype.val
  have hrange : Set.range v = (T : Set (FreeNilpotentLieAlgebra X s)) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hspan : Submodule.span ℚ (Set.range v) = I.toSubmodule := by
    rw [hrange]
    exact (FreeNilpotentLieAlgebra.weightedLayer_eq_span X s w (s + 1)).symm
  have hcountT : (Fintype.card T : ℝ) ≤ B := by
    have hsub := Finset.card_le_card (FreeNilpotentLieAlgebra.weightedLayerGenerators_subset X s w (s + 1))
    exact (Nat.cast_le.mpr (by simpa only [T, Fintype.card_coe] using hsub)).trans hcount
  obtain ⟨d, hd, b, D, S, hmatrix, hDS, hD, hS, hbracket⟩ :=
    exists_lie_quotient_basis_exp_height e I v hspan (one_le_ceil_exp B)
      (fun i j => rationalHeightLE_ceil_exp (hgen j.val
        (FreeNilpotentLieAlgebra.weightedLayerGenerators_subset X s w (s + 1) j.property) i))
      (fun i j k => rationalHeightLE_ceil_exp (hstructure i j k))
      (show 0 ≤ B + 1 by linarith only [hB])
      (by simpa only [Fintype.card_fin] using hdim.trans (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)))
      (hcountT.trans (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)))
      (ceil_exp_le_exp_add_one hB)
  have hd' : d ≤ finrank ℚ (FreeNilpotentLieAlgebra X s) := by simpa only [Fintype.card_fin] using hd
  refine ⟨hdim.trans hBC, e, he, fun x hx i => (hgen x hx i).trans hBC,
    d, hd', (Nat.cast_le.mpr hd').trans (hdim.trans hBC), b, D, S, hmatrix, hDS, ?_, ?_, ?_⟩
  · intro i j
    exact ((rationalLogHeight_le_iff _ _).mpr (hD i j)).trans (hsmall 7 (by omega))
  · intro i j
    exact ((rationalLogHeight_le_iff _ _).mpr (hS i j)).trans (hsmall 45 (by omega))
  · intro i j k
    exact ((rationalLogHeight_le_iff _ _).mpr (hbracket i j k)).trans (hsmall 51 (by omega))

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

theorem exists_bounded_free_weighted_model (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (X : Type*) [Fintype X] (w : X → ℕ)
      (hw : ∀ x, 0 < w x) (p : ℝ), 0 ≤ p → (Fintype.card X : ℝ) ≤ p →
      (finrank ℚ (FreeWeightedNilpotentLieAlgebra X s w) : ℝ) ≤ (p + C) ^ C ∧
      ∃ (b : Basis (Fin (finrank ℚ (FreeWeightedNilpotentLieAlgebra X s w))) ℚ
          (FreeWeightedNilpotentLieAlgebra X s w))
        (u : Fin (finrank ℚ (FreeWeightedNilpotentLieAlgebra X s w)) → ℕ),
        Monotone u ∧ (∀ j, u j ≤ s + 1) ∧ IsCentralLieBasis b ∧
        (∀ d, (FreeWeightedNilpotentLieAlgebra.filtration X s w hw).layer d =
          Submodule.span ℚ (b '' {j | d ≤ u j})) ∧
        (∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ (p + C) ^ C) ∧
        (∀ x ∈ FreeNilpotentLieAlgebra.treeGenerators X s, ∀ i,
          rationalLogHeight (b.repr (FreeWeightedNilpotentLieAlgebra.mk X s w x) i) ≤ (p + C) ^ C) ∧
        ∃ e : Basis (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s))) ℚ
            (FreeNilpotentLieAlgebra X s),
          (∀ i, e i ∈ FreeNilpotentLieAlgebra.treeGenerators X s) ∧
          (finrank ℚ (FreeNilpotentLieAlgebra X s) : ℝ) ≤ (p + C) ^ C ∧
          ∃ S : Matrix (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s)))
              (Fin (finrank ℚ (FreeWeightedNilpotentLieAlgebra X s w))) ℚ,
            LinearMap.toMatrix e b (FreeWeightedNilpotentLieAlgebra.mk X s w).toLinearMap * S = 1 ∧
            ∀ i j, rationalLogHeight (S i j) ≤ (p + C) ^ C := by
  obtain ⟨a, _, hquotient⟩ := exists_bounded_free_weighted_quotient s
  let B₀ : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let P₀ := (B₀ + 2) ^ 4
  let Q₀ := P₀ + (P₀ + 3) ^ 5
  let R₀ := (Q₀ + 2) ^ 4 + (P₀ + 3) ^ 11 + B₀
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R₀ + (R₀ + 3) ^ 5)
  refine ⟨C, hC, ?_⟩
  intro X _ w hw p hp hX
  classical
  let B := (p + a) ^ a
  let P := (B + 2) ^ 4
  let Q := P + (P + 3) ^ 5
  let R := (Q + 2) ^ 4 + (P + 3) ^ 11 + B
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hBP : B ≤ P := le_power_budget hB (by norm_num : 1 ≤ (4 : ℕ))
  have hPQ : P ≤ Q := le_add_of_nonneg_right (by positivity)
  have hIQ : (P + 3) ^ 5 ≤ Q := le_add_of_nonneg_left hP
  have hBR : B ≤ R := le_add_of_nonneg_left (by positivity)
  have hR : 0 ≤ R := hB.trans hBR
  have hprojectionR : (Q + 2) ^ 4 ≤ R :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ (P + 3) ^ 11)).trans
      (le_add_of_nonneg_right hB)
  have hstructureR : (P + 3) ^ 11 ≤ R :=
    (le_add_of_nonneg_left (by positivity : 0 ≤ (Q + 2) ^ 4)).trans
      (le_add_of_nonneg_right hB)
  have hsum : R + (R + 3) ^ 5 ≤ (p + C) ^ C := by
    simpa [B₀, P₀, Q₀, R₀, B, P, Q, R, Polynomial.eval₂_pow] using hbudget p hp
  have hRC : R ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ (R + 3) ^ 5)).trans hsum
  have hSC : (R + 3) ^ 5 ≤ (p + C) ^ C := (le_add_of_nonneg_left hR).trans hsum
  obtain ⟨hdim, e, he, hgen, d, hd, hdimq, q, D, _, hmatrix, _, hD, _, hc⟩ :=
    hquotient X w p hp hX
  have hdimq' : (finrank ℚ (FreeWeightedNilpotentLieAlgebra X s w) : ℝ) ≤ B := by
    simpa only [finrank_eq_card_basis q, Fintype.card_fin] using hdimq
  have htree (x : FreeNilpotentLieAlgebra X s)
      (hx : x ∈ FreeNilpotentLieAlgebra.treeGenerators X s) (j : Fin d) :
      rationalLogHeight (q.repr (FreeWeightedNilpotentLieAlgebra.mk X s w x) j) ≤ P := by
    apply linearMap_coordinate_logHeight e q
      (FreeWeightedNilpotentLieAlgebra.mk X s w).toLinearMap hB
      (by simpa only [Fintype.card_fin] using hdim) ?_ x (hgen x hx)
    intro i j
    have h := hD j i
    rw [← hmatrix, LinearMap.toMatrix_apply] at h
    exact h
  let F := FreeWeightedNilpotentLieAlgebra.filtration X s w hw
  let v (i : Fin (s + 1)) := FreeWeightedNilpotentLieAlgebra.layerFamily X s w hw (i.val + 1)
  have hv (i : Fin (s + 1)) (x : FreeWeightedNilpotentLieAlgebra.layerGenerators X s w (i.val + 1))
      (j : Fin d) : rationalLogHeight (q.repr (v i x : FreeWeightedNilpotentLieAlgebra X s w) j) ≤ P := by
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp x.property
    change rationalLogHeight (q.repr x.val j) ≤ P
    rw [← hxy]
    exact htree y (FreeNilpotentLieAlgebra.weightedLayerGenerators_subset X s w (i.val + 1) hy) j
  obtain ⟨b, u, hu, hub, hcentral, hlayer, _, hinverse, hstructure⟩ :=
    F.exists_bounded_sorted_adapted_basis_logHeight q v
      (fun i => FreeWeightedNilpotentLieAlgebra.layerFamily_span X s w hw (i.val + 1))
      hP (by simpa only [Fintype.card_fin] using hdimq.trans hBP) hv
      (fun i j k => (hc i j k).trans hBP)
  have htree' (x : FreeNilpotentLieAlgebra X s)
      (hx : x ∈ FreeNilpotentLieAlgebra.treeGenerators X s) (j) :
      rationalLogHeight (b.repr (FreeWeightedNilpotentLieAlgebra.mk X s w x) j) ≤ R := by
    apply le_trans _ hprojectionR
    exact linearMap_coordinate_logHeight q b (LinearMap.id) hQ
      (by simpa only [Fintype.card_fin] using hdimq.trans (hBP.trans hPQ))
      (fun i k => (hinverse i k).trans hIQ)
      (FreeWeightedNilpotentLieAlgebra.mk X s w x) (fun i => (htree x hx i).trans hPQ) j
  let A := LinearMap.toMatrix e b (FreeWeightedNilpotentLieAlgebra.mk X s w).toLinearMap
  have hA (i j) : rationalLogHeight (A i j) ≤ R := by
    dsimp only [A]
    rw [LinearMap.toMatrix_apply]
    exact htree' (e j) (he j) i
  obtain ⟨S, hAS, hS⟩ := exists_rational_section_exp_height A
    (basisMatrix_surjective e b (FreeWeightedNilpotentLieAlgebra.mk X s w).toLinearMap
      (FreeWeightedNilpotentLieAlgebra.mk_surjective X s w))
    (one_le_ceil_exp R) (fun i j => rationalHeightLE_ceil_exp (hA i j))
    (hR.trans (le_add_of_nonneg_right zero_le_one))
    (by simpa only [Fintype.card_fin] using (hdimq'.trans
      (hBR.trans (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)))))
    (ceil_exp_le_exp_add_one hR)
  refine ⟨hdimq'.trans (hBR.trans hRC), b, u, hu, hub, hcentral, hlayer,
    fun i j k => (hstructure i j k).trans (hstructureR.trans hRC),
    fun x hx j => (htree' x hx j).trans hRC, e, he, hdim.trans (hBR.trans hRC), S, hAS, ?_⟩
  intro i j
  apply le_trans ((rationalLogHeight_le_iff _ _).mpr (hS i j))
  simpa only [show R + 1 + 2 = R + 3 by ring] using hSC

end Erdos3

end

end OAI

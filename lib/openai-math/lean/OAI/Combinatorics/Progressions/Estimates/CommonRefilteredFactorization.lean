import OAI.Combinatorics.Progressions.Estimates.ControlledComparisonModel
import OAI.Combinatorics.Progressions.Linear.BoundedSpanningPadding
import OAI.Combinatorics.Progressions.Linear.MultiaffineTripleLayerBasis

namespace OAI

section

namespace Erdos3

open Module
open scoped BigOperators

theorem coordinate_spanning_range {ι κ V : Type*} [Fintype ι] [Fintype κ]
    [AddCommGroup V] [Module ℚ V] (b : Basis ι ℚ V) (v : κ → V) (U : Submodule ℚ V)
    (hv : Submodule.span ℚ (Set.range v) = U) :
    LinearMap.range (Matrix.mulVecLin (fun i k => b.equivFun (v k) i)) =
      U.map b.equivFun.toLinearMap := by
  rw [← hv, Submodule.map_span, ← Set.range_comp]
  exact (Matrix.range_mulVecLin _)

theorem exists_intersection_spanning_logHeight {ι κ J V : Type*}
    [Fintype ι] [Fintype κ] [Fintype J] [LieRing V] [LieAlgebra ℚ V]
    (b : Basis ι ℚ V) (U : J → LieSubalgebra ℚ V) (v : J → κ → V)
    (hv : ∀ j, Submodule.span ℚ (Set.range (v j)) = (U j).toSubmodule)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hJ : (Fintype.card J : ℝ) ≤ p)
    (hheight : ∀ j a i, rationalLogHeight (b.repr (v j a) i) ≤ p) :
    ∃ w : Fin (Fintype.card ι) → V,
      Submodule.span ℚ (Set.range w) = (⨅ j, U j).toSubmodule ∧
      ∀ a i, rationalLogHeight (b.repr (w a) i) ≤ ((p + 2) ^ 2 + 2) ^ 63 + 1 := by
  classical
  let A : J → Matrix ι κ ℚ := fun j i k => b.equivFun (v j k) i
  let W := ⨅ j, U j
  let Wc : Submodule ℚ (ι → ℚ) := ⨅ j, LinearMap.range (A j).mulVecLin
  have hA (j : J) : LinearMap.range (A j).mulVecLin = (U j).toSubmodule.map b.equivFun.toLinearMap :=
    coordinate_spanning_range b (v j) (U j).toSubmodule (hv j)
  have hmem (x : V) : b.equivFun x ∈ Wc ↔ x ∈ W := by
    constructor
    · intro hx
      simp only [Wc, Submodule.mem_iInf] at hx
      apply (lieSubalgebra_mem_iInf U x).mpr
      intro j
      have hxj := hx j
      rw [hA j] at hxj
      obtain ⟨y, hy, he⟩ := hxj
      have he' : y = x := b.equivFun.injective he
      exact he' ▸ hy
    · intro hx
      simp only [Wc, Submodule.mem_iInf]
      intro j
      rw [hA j]
      exact ⟨x, (lieSubalgebra_mem_iInf U x).mp hx j, rfl⟩
  let e : W ≃ₗ[ℚ] Wc :=
    { toFun := fun x => ⟨b.equivFun x, (hmem x).mpr x.property⟩
      invFun := fun x => ⟨b.equivFun.symm x, (hmem _).mp (by
        simpa only [LinearEquiv.apply_symm_apply] using x.property)⟩
      map_add' := fun x y => Subtype.ext (b.equivFun.map_add x y)
      map_smul' := fun c x => Subtype.ext (b.equivFun.map_smul c x)
      left_inv := fun x => Subtype.ext (b.equivFun.symm_apply_apply x)
      right_inv := fun x => Subtype.ext (b.equivFun.apply_symm_apply x) }
  let q := (p + 2) ^ 2
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; nlinarith [sq_nonneg p]
  have hp1q : p + 1 ≤ q := by dsimp [q]; nlinarith [sq_nonneg p]
  have hcols : ((∑ _j : J, Fintype.card κ : ℕ) : ℝ) ≤ q := by
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.cast_mul]
    have hprod := mul_le_mul hJ hκ (Nat.cast_nonneg _) hp
    dsimp [q]
    nlinarith
  obtain ⟨bc, hbc⟩ := exists_image_intersection_basis_exp_height A (one_le_ceil_exp p)
    (fun j i k => rationalHeightLE_ceil_exp (hheight j k i)) hq
    (hJ.trans hpq) (hι.trans hpq) hcols
    ((ceil_exp_le_exp_add_one hp).trans (Real.exp_le_exp.mpr hp1q))
  let bw := bc.map e.symm
  let H := ⌈Real.exp ((q + 2) ^ 63)⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp _
  have hbheight (a : Fin (finrank ℚ Wc)) (i : ι) : RationalHeightLE (b.repr (bw a : V) i) H := by
    have hb := rationalHeightLE_ceil_exp ((rationalLogHeight_le_iff _ _).mpr (hbc a i))
    change RationalHeightLE (b.repr (b.equivFun.symm (bc a : ι → ℚ)) i) H
    simpa only [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply] using hb
  obtain ⟨w, hw, hh⟩ := exists_bounded_ambient_spanning b W bw bw.span_eq hH hbheight
  refine ⟨w, hw, ?_⟩
  intro a i
  exact rationalLogHeight_le_of_height (hh a i) (ceil_exp_le_exp_add_one (by positivity))

end Erdos3

end

section

namespace Erdos3

open Module

theorem exists_binary_intersection_basis_logHeight
    {ι α β L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
    (e : Basis ι ℚ L) (U V : LieSubalgebra ℚ L)
    (bU : Basis α ℚ U) (bV : Basis β ℚ V)
    {p : ℝ} (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hU : ∀ a i, rationalLogHeight (e.repr (bU a : L) i) ≤ p)
    (hV : ∀ a i, rationalLogHeight (e.repr (bV a : L) i) ≤ p) :
    ∃ b : Basis (Fin (finrank ℚ (U ⊓ V : LieSubalgebra ℚ L))) ℚ
        (U ⊓ V : LieSubalgebra ℚ L),
      ∀ a i, rationalLogHeight (e.repr (b a : L) i) ≤ ((p + 4) ^ 2 + 2) ^ 63 + 2 := by
  classical
  obtain ⟨u, hu, hhu⟩ := exists_bounded_ambient_spanning e U bU bU.span_eq
    (one_le_ceil_exp p) (fun a i => rationalHeightLE_ceil_exp (hU a i))
  obtain ⟨v, hv, hhv⟩ := exists_bounded_ambient_spanning e V bV bV.span_eq
    (one_le_ceil_exp p) (fun a i => rationalHeightLE_ceil_exp (hV a i))
  let W : Bool → LieSubalgebra ℚ L := fun j => if j then U else V
  let z : Bool → Fin (Fintype.card ι) → L := fun j => if j then u else v
  have hz (j : Bool) : Submodule.span ℚ (Set.range (z j)) = (W j).toSubmodule := by
    cases j
    · exact hv
    · exact hu
  have hh (j : Bool) (a) (i) : rationalLogHeight (e.repr (z j a) i) ≤ p + 2 := by
    have hceil := ceil_exp_le_exp_add_one hp
    cases j
    · exact (rationalLogHeight_le_of_height (hhv a i) hceil).trans (by linarith)
    · exact (rationalLogHeight_le_of_height (hhu a i) hceil).trans (by linarith)
  obtain ⟨w, hw, hhw⟩ := exists_intersection_spanning_logHeight e W z hz
    (by linarith : 0 ≤ p + 2) (hd.trans (by linarith))
    (by simpa only [Fintype.card_fin] using hd.trans (show p ≤ p + 2 by linarith))
    (by simpa using (show (2 : ℝ) ≤ p + 2 by linarith)) hh
  have hW : (⨅ j, W j) = U ⊓ V := by
    ext x
    simp [lieSubalgebra_mem_iInf, W, Bool.forall_bool, and_comm]
  rw [hW] at hw
  obtain ⟨b, hb⟩ := exists_bounded_submodule_basis_from_spanning e
    (U ⊓ V).toSubmodule w hw (fun a i => rationalHeightLE_ceil_exp (hhw a i))
  refine ⟨b, fun a i => ?_⟩
  have h := rationalLogHeight_le_of_height (hb a i)
    (ceil_exp_le_exp_add_one (by positivity : 0 ≤ ((p + 2 + 2) ^ 2 + 2) ^ 63 + 1))
  simpa only [show p + 2 + 2 = p + 4 by ring, add_assoc, one_add_one_eq_two] using h

end Erdos3

end

section

namespace Erdos3

open Module

namespace MultidegreeLieFiltration

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def weightedLayerEquiv (c : σ → ℕ) (n : ℕ) (hn : 1 ≤ n) :
    (F.weightedFiltration c).layer n ≃ₗ[ℚ] F.weightedLayer c n where
  toFun x := ⟨x.val.val, (F.mem_weightedFiltration_layer c n hn x.val).mp x.property⟩
  invFun x := ⟨⟨x.val, F.weightedLayer_antitone c hn x.property⟩,
    (F.mem_weightedFiltration_layer c n hn _).mpr x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem exists_weighted_layer_coordinate_basis {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : σ → ℕ) (e : Basis ι ℚ L) (b : Basis κ ℚ (F.weightedSubalgebra c))
    (n : ℕ) (hn : 1 ≤ n)
    (a : Basis (Fin (finrank ℚ (F.weightedLayer c n))) ℚ (F.weightedLayer c n))
    {H : ℕ} (hH : 1 ≤ H)
    (hb : ∀ i k, RationalHeightLE (e.repr (b i : L) k) H)
    (ha : ∀ i k, RationalHeightLE (e.repr (a i : L) k) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p) :
    ∃ a' : Basis (Fin (finrank ℚ ((F.weightedFiltration c).layer n))) ℚ
        ((F.weightedFiltration c).layer n),
      ∀ i k, rationalLogHeight (b.repr (a' i : F.weightedSubalgebra c) k) ≤ (p + 2) ^ 8 := by
  let E := F.weightedLayerEquiv c n hn
  let a' := (a.map E.symm).reindex (finCongr E.finrank_eq.symm)
  have hval (i) : ((a' i : F.weightedSubalgebra c) : L) =
      (a ((finCongr E.finrank_eq.symm).symm i) : L) := by
    simp only [a', Basis.reindex_apply, Basis.map_apply, E, weightedLayerEquiv]
    rfl
  refine ⟨a', fun i k => ?_⟩
  apply rationalLogHeight_le_of_height
    (embedding_basis_coordinate_height b e (F.weightedSubalgebra c).incl.toLinearMap
      (fun _ _ h => Subtype.ext h) hH (fun k i => hb i k)
      (a' i : F.weightedSubalgebra c) (K := H) (fun k => by
        change RationalHeightLE (e.repr ((a' i : F.weightedSubalgebra c) : L) k) H
        rw [hval]
        exact ha _ k) k)
  exact embedding_coordinate_height_budget _ _ H H hp hι hκ hHp hHp

end MultidegreeLieFiltration

namespace RationalFilteredNilmanifold.MultidegreeStructure

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem exists_weighted_layer_basis (c : σ → ℕ) (n : ℕ) {H : ℕ}
    (hM : ∀ a i k, RationalHeightLE (D.basis.repr (M.basis a i : L) k) H) :
    ∃ b : Basis (Fin (finrank ℚ (M.filtration.weightedLayer c n))) ℚ
        (M.filtration.weightedLayer c n),
      ∀ i k, RationalHeightLE (D.basis.repr (b i : L) k) H := by
  apply exists_bounded_submodule_basis_from_spanning D.basis
    (M.filtration.weightedLayer c n).toSubmodule
    (fun a : Σ a : {a : ∀ i, Fin (bound i + 1) //
        n ≤ multidegreeWeight c (fun i => (a i).val)},
        Fin (finrank ℚ (M.filtration.layer (fun i => (a.val i).val))) =>
      (M.basis a.1.val a.2 : L)) (M.weightedLayer_span c n).symm
  exact fun a k => hM a.1.val a.2 k

end RationalFilteredNilmanifold.MultidegreeStructure

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem exists_coordinate_active_basis (i : σ) (hi : 1 ≤ bound i)
    (n : Fin (s + 1)) {p : ℝ} (hM : M.ComplexityLE p) :
    ∃ b : Basis (Fin (finrank ℚ (M.filtration.coordinateActiveLayer i (n.val + 1)))) ℚ
        (M.filtration.coordinateActiveLayer i (n.val + 1)),
      ∀ j k, rationalLogHeight (D.basis.repr (b j : L) k) ≤ ((p + 4) ^ 2 + 2) ^ 63 + 2 := by
  have hsingle : Pi.single i 1 ≤ bound := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa only [Pi.single_eq_same] using hi
    · simpa only [Pi.single_eq_of_ne hji] using Nat.zero_le (bound j)
  obtain ⟨a, ha⟩ := M.exists_layer_basis (Pi.single i 1) hsingle hM
  obtain ⟨b, hb⟩ := M.exists_ordinary_layer_basis n hM
  exact exists_binary_intersection_basis_logHeight D.basis
    (M.filtration.layerIdeal (Pi.single i 1)).toLieSubalgebra
    (M.filtration.ordinary.layerIdeal (n.val + 1)).toLieSubalgebra a b
    ((Nat.cast_nonneg d).trans hM.1.1)
    (by simpa only [Fintype.card_fin] using hM.1.1) ha hb

theorem le_triple_basis_budget {p : ℝ} (hp : 0 ≤ p) :
    p ≤ ((p + 4) ^ 2 + 2) ^ 63 := by
  have hb : 1 ≤ (p + 4) ^ 2 + 2 := by nlinarith [sq_nonneg (p + 4)]
  have hpow : (p + 4) ^ 2 + 2 ≤ ((p + 4) ^ 2 + 2) ^ 63 := by
    simpa only [pow_one] using pow_le_pow_right₀ hb (by decide : 1 ≤ 63)
  exact (show p ≤ (p + 4) ^ 2 + 2 by nlinarith [sq_nonneg p]).trans hpow

theorem exists_additiveTriple_layer_basis_logHeight (i : σ) (hi : 1 ≤ bound i)
    (c : σ → ℕ) (n : Fin (s + 1)) {p : ℝ} (hM : M.ComplexityLE p) :
    ∃ q : Basis (Fin (finrank ℚ (M.filtration.additiveTripleLayer i c (n.val + 1)))) ℚ
        (M.filtration.additiveTripleLayer i c (n.val + 1)),
      ∀ j k, rationalLogHeight (D.basis.repr (q j).val.1 k) ≤ ((p + 4) ^ 2 + 2) ^ 63 + 3 ∧
        rationalLogHeight (D.basis.repr (q j).val.2.1 k) ≤ ((p + 4) ^ 2 + 2) ^ 63 + 3 ∧
        rationalLogHeight (D.basis.repr (q j).val.2.2 k) ≤ ((p + 4) ^ 2 + 2) ^ 63 + 3 := by
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  let P := ((p + 4) ^ 2 + 2) ^ 63 + 2
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hpP : p + 1 ≤ P := add_le_add (le_triple_basis_budget hp) (by norm_num)
  obtain ⟨a, ha⟩ := M.exists_weighted_layer_basis c (n.val + 1)
    (fun a j k => rationalHeightLE_ceil_exp (hM.2 a j k))
  obtain ⟨b, hb⟩ := M.exists_coordinate_active_basis i hi n hM
  have ha' (j) (k) : RationalHeightLE (D.basis.repr (a j : L) k) ⌈Real.exp P⌉₊ :=
    rationalHeightLE_ceil_exp
      ((rationalLogHeight_le_of_height (ha j k) (ceil_exp_le_exp_add_one hp)).trans hpP)
  obtain ⟨q, hq⟩ := M.filtration.exists_additiveTriple_layer_basis D.basis i c (n.val + 1)
    a b (one_le_ceil_exp P) ha' (fun j k => rationalHeightLE_ceil_exp (hb j k))
  refine ⟨q, fun j k => ?_⟩
  have hceil : (⌈Real.exp P⌉₊ : ℝ) ≤ Real.exp (((p + 4) ^ 2 + 2) ^ 63 + 3) := by
    simpa only [P, add_assoc, show (2 : ℝ) + 1 = 3 by norm_num] using ceil_exp_le_exp_add_one hP
  exact ⟨rationalLogHeight_le_of_height (hq j k).1 hceil,
    rationalLogHeight_le_of_height (hq j k).2.1 hceil,
    rationalLogHeight_le_of_height (hq j k).2.2 hceil⟩

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem exists_weighted_model_of_bases (c : σ → ℕ)
    (b : Basis (Fin (finrank ℚ (M.filtration.weightedSubalgebra c))) ℚ
      (M.filtration.weightedSubalgebra c))
    {H : ℕ} (hH : 1 ≤ H)
    (hb : ∀ i k, RationalHeightLE (D.basis.repr (b i : L) k) H)
    (hlayers : ∀ n, 1 ≤ n →
      ∃ a : Basis (Fin (finrank ℚ (M.filtration.weightedLayer c n))) ℚ
        (M.filtration.weightedLayer c n),
        ∀ i k, RationalHeightLE (D.basis.repr (a i : L) k) H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H)
    {p : ℝ} (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hgrid : (D.grid : ℝ) ≤ Real.exp p) :
    ∃ E : RationalFilteredNilmanifold (M.filtration.weightedSubalgebra c)
        (multidegreeWeight c bound) (finrank ℚ (M.filtration.weightedSubalgebra c)),
      E.filtration = M.filtration.weightedFiltration c ∧ E.basis = b ∧
      E.lattice = D.lattice.comap
        (NilpotentLieBCHGroup.mapOfSteps (M.filtration.weightedSubalgebra c).incl) ∧
      E.GeometryComplexityLE ((p + 2) ^ 11) := by
  classical
  let K := M.filtration.weightedSubalgebra c
  let F := M.filtration.weightedFiltration c
  have hr : (finrank ℚ K : ℝ) ≤ p :=
    (Nat.cast_le.mpr (lie_subalgebra_finrank_le D.basis K)).trans
      (by simpa only [Fintype.card_fin] using hd)
  have hd' : (Fintype.card (Fin d) : ℝ) ≤ p := by simpa only [Fintype.card_fin] using hd
  have hr' : (Fintype.card (Fin (finrank ℚ K)) : ℝ) ≤ p := by
    simpa only [Fintype.card_fin] using hr
  have hmatrix : ∀ i j, RationalHeightLE (LinearMap.toMatrix b D.basis K.incl.toLinearMap i j) H := by
    intro i j
    rw [LinearMap.toMatrix_apply]
    change RationalHeightLE (D.basis.repr (b j : L) i) H
    exact hb j i
  obtain ⟨N, hN, hNb, hin, hout⟩ := exists_bchSubgroup_comap_grid_of_steps
    (hM := F.lowerCentralSeries_eq_bot) b D.basis K.incl
    (fun _ _ h => Subtype.ext h) D.lattice hH D.grid_pos hmatrix D.inner_grid D.outer_grid
    hp hd' hr' hHp hgrid
  obtain ⟨_, _, _, hbracket⟩ := exists_bounded_lie_embedding_retraction b D.basis K.incl
    (fun _ _ h => Subtype.ext h) hH hc hmatrix
  have hbracketBudget := rationalLieStructureHeight_inverse_budget d (finrank ℚ K) H hp hd hr hHp
  have hLayer : ∀ i : Fin (multidegreeWeight c bound + 1),
      ∃ a : Basis (Fin (finrank ℚ (F.layer (i.val + 1)))) ℚ (F.layer (i.val + 1)),
        ∀ j k, rationalLogHeight (b.repr (a j : K) k) ≤ (p + 2) ^ 8 := by
    intro i
    obtain ⟨a, ha⟩ := hlayers (i.val + 1) (Nat.le_add_left 1 _)
    exact M.filtration.exists_weighted_layer_coordinate_basis c D.basis b (i.val + 1)
      (Nat.le_add_left 1 _) a hH hb ha hp hd' hr' hHp
  choose a ha using hLayer
  let E : RationalFilteredNilmanifold K (multidegreeWeight c bound) (finrank ℚ K) :=
    { filtration := F
      basis := b
      layerBasis := a
      lattice := D.lattice.comap (NilpotentLieBCHGroup.mapOfSteps K.incl)
      grid := N
      grid_pos := hN
      inner_grid := hin
      outer_grid := hout }
  have hp1 : 1 ≤ p + 2 := by linarith
  have h9 : (p + 2) ^ 9 ≤ (p + 2) ^ 11 := pow_le_pow_right₀ hp1 (by decide)
  have h8 : (p + 2) ^ 8 ≤ (p + 2) ^ 11 := pow_le_pow_right₀ hp1 (by decide)
  refine ⟨E, rfl, rfl, rfl, hr.trans (le_power_budget hp (by decide)),
    hNb.trans (Real.exp_le_exp.mpr h9), ?_, ?_⟩
  · intro i j k
    apply rationalLogHeight_le_of_height (hbracket i j k)
    simpa only [Fintype.card_fin] using hbracketBudget
  · intro i j k
    exact (ha i j k).trans h8

theorem exists_weighted_model (c : σ → ℕ) {p : ℝ} (hM : M.ComplexityLE p) :
    ∃ E : RationalFilteredNilmanifold (M.filtration.weightedSubalgebra c)
        (multidegreeWeight c bound) (finrank ℚ (M.filtration.weightedSubalgebra c)),
      E.filtration = M.filtration.weightedFiltration c ∧
      E.lattice = D.lattice.comap
        (NilpotentLieBCHGroup.mapOfSteps (M.filtration.weightedSubalgebra c).incl) ∧
      E.GeometryComplexityLE ((p + 3) ^ 11) ∧
      ∀ i k, rationalLogHeight (D.basis.repr (E.basis i : L) k) ≤ p + 1 := by
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  let H := ⌈Real.exp p⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp p
  have hHp : (H : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have hheight : ∀ a i k, RationalHeightLE (D.basis.repr (M.basis a i : L) k) H :=
    fun a i k => rationalHeightLE_ceil_exp (hM.2 a i k)
  obtain ⟨b, hb⟩ := M.exists_weighted_layer_basis c 1 hheight
  obtain ⟨E, hEF, hEb, hElattice, hEgeom⟩ := M.exists_weighted_model_of_bases c b hH hb
    (fun n _ => M.exists_weighted_layer_basis c n hheight)
    (fun i j k => rationalHeightLE_ceil_exp (hM.1.2.2.1 i j k))
    (by linarith : 0 ≤ p + 1) (hM.1.1.trans (by linarith)) hHp
    (hM.1.2.1.trans (Real.exp_le_exp.mpr (by linarith)))
  refine ⟨E, hEF, hElattice, ?_, ?_⟩
  · convert hEgeom using 1
    ring
  · intro i k
    rw [hEb]
    exact rationalLogHeight_le_of_height (hb i k) hHp

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

noncomputable def additiveTripleLattice (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) :
    Subgroup (M.filtration.additiveTripleFiltration i hi c hc).Group :=
  (pi (fun _ : Fin 3 => D)).lattice.comap
    (NilpotentLieBCHGroup.mapOfSteps (M.filtration.additiveTripleToPi i hi c hc))

theorem additiveTripleLattice_mem (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1)
    (x : (M.filtration.additiveTripleFiltration i hi c hc).Group) :
    x ∈ M.additiveTripleLattice i hi c hc ↔
      (⟨x.coord.val.1⟩ : D.filtration.Group) ∈ D.lattice ∧
      (⟨x.coord.val.2.1⟩ : D.filtration.Group) ∈ D.lattice ∧
      (⟨x.coord.val.2.2⟩ : D.filtration.Group) ∈ D.lattice := by
  change (NilpotentLieBCHGroup.mapOfSteps (M.filtration.additiveTripleToPi i hi c hc) x) ∈
    piBCHSubgroup (fun _ : Fin 3 => D.filtration) (fun _ : Fin 3 => D.lattice) ↔ _
  rw [mem_piBCHSubgroup]
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2⟩
  · intro h j
    fin_cases j
    · exact h.1
    · exact h.2.1
    · exact h.2.2

theorem exists_additiveTriple_filtration_basis_logHeight (i : σ) (hi : bound i = 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (n : Fin (s + 1))
    {p : ℝ} (hM : M.ComplexityLE p) :
    ∃ a : Basis (Fin (finrank ℚ
        ((M.filtration.additiveTripleFiltration i hi.le c hc).layer (n.val + 1)))) ℚ
        ((M.filtration.additiveTripleFiltration i hi.le c hc).layer (n.val + 1)),
      ∀ j k, rationalLogHeight ((pi (fun _ : Fin 3 => D)).basis.repr
        (M.filtration.additiveTripleToPi i hi.le c hc (a j)) k) ≤
          ((p + 4) ^ 2 + 2) ^ 63 + 3 := by
  obtain ⟨q, hq⟩ := M.exists_additiveTriple_layer_basis_logHeight i hi.ge c n hM
  let e := M.filtration.additiveTripleFiltrationLayerEquiv i hi.le c hc
    (n.val + 1) (Nat.le_add_left 1 _)
  let a := (q.map e.symm).reindex (finCongr e.finrank_eq.symm)
  have hval (j) : ((a j : M.filtration.additiveTripleSubalgebra i hi.le c hc) : L × L × L) =
      (q ((finCongr e.finrank_eq.symm).symm j)).val := by
    simp only [a, Basis.reindex_apply, Basis.map_apply, e,
      MultidegreeLieFiltration.additiveTripleFiltrationLayerEquiv]
    rfl
  refine ⟨a, fun j k => ?_⟩
  change rationalLogHeight ((pi (fun _ : Fin 3 => D)).basis.repr
    (tripleToPi ((a j : M.filtration.additiveTripleSubalgebra i hi.le c hc) : L × L × L)) k) ≤ _
  rw [hval]
  exact D.triple_product_basis_logHeight _ (hq _) k

noncomputable def additiveTripleGeometryBudget (p : ℝ) : ℝ :=
  ((p + 6) ^ 2 + ((p + 4) ^ 2 + 2) ^ 63 + 6) ^ 11

theorem exists_additiveTriple_model (i : σ) (hi : bound i = 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) {p : ℝ} (hM : M.ComplexityLE p) :
    ∃ E : RationalFilteredNilmanifold (M.filtration.additiveTripleSubalgebra i hi.le c hc) s
        (finrank ℚ (M.filtration.additiveTripleSubalgebra i hi.le c hc)),
      E.filtration = M.filtration.additiveTripleFiltration i hi.le c hc ∧
      E.lattice = M.additiveTripleLattice i hi.le c hc ∧
      E.GeometryComplexityLE (additiveTripleGeometryBudget p) ∧
      finrank ℚ (M.filtration.additiveTripleSubalgebra i hi.le c hc) ≤ 3 * d ∧
      ∀ j k, rationalLogHeight (D.basis.repr (E.basis j).val.1 k) ≤ ((p + 4) ^ 2 + 2) ^ 63 + 3 ∧
        rationalLogHeight (D.basis.repr (E.basis j).val.2.1 k) ≤ ((p + 4) ^ 2 + 2) ^ 63 + 3 ∧
        rationalLogHeight (D.basis.repr (E.basis j).val.2.2 k) ≤ ((p + 4) ^ 2 + 2) ^ 63 + 3 := by
  let P := pi (fun _ : Fin 3 => D)
  let K := M.filtration.additiveTripleSubalgebra i hi.le c hc
  let F := M.filtration.additiveTripleFiltration i hi.le c hc
  let φ := M.filtration.additiveTripleToPi i hi.le c hc
  let C := ((p + 4) ^ 2 + 2) ^ 63
  let q := (p + 6) ^ 2 + C + 3
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hCq : C + 3 ≤ q := by
    have h : C + 3 ≤ (p + 6) ^ 2 + (C + 3) := le_add_of_nonneg_left (sq_nonneg (p + 6))
    simpa only [q, add_assoc] using h
  have hP : P.GeometryComplexityLE q := by
    have hh := pi_geometry (fun _ : Fin 3 => D) (by linarith : 0 ≤ p + 3)
      (by simpa using (show (3 : ℝ) ≤ p + 3 by linarith))
      (fun _ => hM.1.mono D (by linarith : p ≤ p + 3))
    apply hh.mono P
    have hsq : (p + 3 + 2) ^ 2 ≤ (p + 6) ^ 2 := by nlinarith only [hp]
    exact hsq.trans ((le_add_of_nonneg_right hC).trans (le_add_of_nonneg_right (by norm_num)))
  obtain ⟨b, hb⟩ := M.exists_additiveTriple_layer_basis_logHeight i hi.ge c
    (⟨0, Nat.succ_pos s⟩ : Fin (s + 1)) hM
  let bK : Basis (Fin (finrank ℚ K)) ℚ K := b
  have hb' (j) (k) : rationalLogHeight (P.basis.repr (φ (bK j)) k) ≤ q :=
    (D.triple_product_basis_logHeight _ (hb j) k).trans hCq
  have hlayers (n : Fin (s + 1)) :
      ∃ a : Basis (Fin (finrank ℚ (F.layer (n.val + 1)))) ℚ (F.layer (n.val + 1)),
        ∀ j k, rationalLogHeight (P.basis.repr (φ (a j)) k) ≤ q := by
    obtain ⟨a, ha⟩ := M.exists_additiveTriple_filtration_basis_logHeight i hi c hc n hM
    exact ⟨a, fun j k => (ha j k).trans hCq⟩
  have hφ := M.filtration.additiveTripleToPi_injective i hi.le c hc
  obtain ⟨E, hEF, hEb, hEL, hE⟩ := P.exists_model_of_embedding_logHeight F bK φ hφ hP hb' hlayers
  have hdim : finrank ℚ K ≤ 3 * d := by
    have hh := P.embedding_basis_card_le bK φ hφ
    simpa only [Fintype.card_sigma, Fintype.card_fin, Finset.sum_const,
      Finset.card_univ, smul_eq_mul] using hh
  refine ⟨E, hEF, hEL, ?_, hdim, ?_⟩
  · simpa only [q, C, additiveTripleGeometryBudget, add_assoc, show (3 : ℝ) + 3 = 6 by norm_num] using hE
  · intro j k
    rw [hEb]
    exact hb j k

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

theorem exists_common_refiltered_factorization (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι J L : Type*} [Fintype σ] [Fintype ι] [Fintype J]
      [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))
      (eta : J → L →ₗ[ℚ] ℚ) (p : ℝ), 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (Fintype.card J : ℝ) ≤ p →
      (∀ i j k, rationalLogHeight (b.repr ⁅b i, b j⁆ k) ≤ p) →
      ∀ T : σ → ℝ, (∀ i, Real.exp ((p + 2) ^ C) ≤ T i) →
      ∀ g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group,
      (∀ j, F.ControlledSymbolFactorization b w hF (eta j) T
        (F.realPolynomialSymbolHom b w hF (fun _ => 1) g) p) →
      ∃ (W : LieSubalgebra ℚ F.AssociatedGraded) (v : Fin (Fintype.card ι) → F.AssociatedGraded)
        (m : ℕ) (e₀ p₀ r₀ : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group),
        Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
        BasisGradedSubmodule (F.associatedGradedBasis b w hF) w W.toSubmodule ∧
        (∀ i k, rationalLogHeight ((F.associatedGradedBasis b w hF).repr (v i) k) ≤
          ((p + 2) ^ 2 + 2) ^ 63 + 1) ∧
        (∀ j x, x ∈ F.realGradedRefiltrationLayer W s → realifyFunctional (eta j) x = 0) ∧
        0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧ e₀ * p₀ * r₀ = g ∧
        (∀ t : σ → ℝ, eval₂ t (F.realGradedSymbolPolynomial b w hF (fun _ => 1)
          (F.realPolynomialSymbolHom b w hF (fun _ => 1) p₀).coord) ∈ realificationLieSubalgebra W) ∧
        (∀ α i, |(b.baseChange ℝ).repr
          (coefficients (e₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) i| ≤
            Real.exp ((p + 2) ^ C) / monomialScale T α) ∧
        ((fun z : (σ →₀ ℕ) × ι => (b.baseChange ℝ).repr
          (coefficients (r₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2) ∈ realDenominatorGrid m) ∧
        coefficients (e₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        coefficients (r₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        coefficients (p₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 =
          coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 ∧
        (coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 →
          ∀ t : σ → ℝ, eval₂ t (p₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∈
            realificationLieSubalgebra (F.gradedRefiltrationSubalgebra W)) := by
  obtain ⟨C, hC, hcommon⟩ := exists_common_polynomial_step_drop_factors s
  refine ⟨C, hC, ?_⟩
  intro σ ι J L _ _ _ _ _ F b w hF eta p hp hι hσ hJ hstructure T hT g hfactor
  obtain ⟨U, v, m, e₀, p₀, r₀, hv, hU, hheight, hfreq, hm, hmp, hepr,
      hmid, he, hr, he0, hr0, hp0⟩ :=
    hcommon F b w hF eta p hp hι hσ hJ hstructure T hT g hfactor
  let W := ⨅ j, U j
  obtain ⟨v₀, hv₀, hheight₀⟩ := exists_intersection_spanning_logHeight
    (F.associatedGradedBasis b w hF) U v hv hp hι hι hJ hheight
  have hW : BasisGradedSubmodule (F.associatedGradedBasis b w hF) w W.toSubmodule := by
    intro k x hx
    apply (lieSubalgebra_mem_iInf U _).mpr
    intro j
    exact hU j k x ((lieSubalgebra_mem_iInf U x).mp hx j)
  refine ⟨W, v₀, m, e₀, p₀, r₀, hv₀, hW, hheight₀, ?_, hm, hmp, hepr,
    hmid, he, hr, he0, hr0, hp0, ?_⟩
  · intro j
    exact F.real_frequency_zero_on_refiltered_top b w hF W (eta j) (hfreq j)
  · intro hzero
    exact F.pointwise_refiltered_values_mem b w hF (fun _ => 1) W (fun _ => Nat.zero_lt_one)
      p₀.coord (hp0.trans hzero) hmid

end Erdos3.NilpotentLieFiltration

end

end OAI

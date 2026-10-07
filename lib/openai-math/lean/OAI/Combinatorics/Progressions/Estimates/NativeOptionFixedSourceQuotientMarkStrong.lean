import OAI.Combinatorics.Progressions.Dynamics.AdaptedMapGeometryBudget
import OAI.Combinatorics.Progressions.Estimates.NativeOptionOriginalOrbit
import OAI.Combinatorics.Progressions.Estimates.RealifiedTopQuotient
import OAI.Combinatorics.Progressions.Nilpotent.NiltestVerticalBounds

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}

structure AdaptedModelData (D : RationalFilteredNilmanifold L s d) where
  basis : Basis (Fin (finrank ℚ L)) ℚ L
  weight : Fin (finrank ℚ L) → ℕ
  layers : ∀ j, D.filtration.layer j = Submodule.span ℚ (basis '' {i | j ≤ weight i})
  grid : ℕ
  grid_pos : 0 < grid
  inner : scaledIntegerGrid grid ⊆ bchSubgroupCoordinates basis D.lattice
  outer : bchSubgroupCoordinates basis D.lattice ⊆ denominatorGrid grid

namespace AdaptedModelData

variable {D : RationalFilteredNilmanifold L s d}

noncomputable def model (F : D.AdaptedModelData) : RationalFilteredNilmanifold L s (finrank ℚ L) :=
  D.filtration.ofAdaptedBasis F.basis F.weight F.layers D.lattice F.grid F.grid_pos F.inner F.outer

theorem model_layers (F : D.AdaptedModelData) (j : ℕ) :
    F.model.filtration.layer j = Submodule.span ℚ (F.model.basis '' {i | j ≤ F.weight i}) := F.layers j

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem original_dist_le (F : D.AdaptedModelData) (H : ℕ)
    (hH : ∀ i j, RationalHeightLE (D.basis.repr (F.basis i) j) H) (x y : D.Space) :
    @dist D.Space D.metricSpace.toDist x y ≤
      coordinateLipschitzBound d (finrank ℚ L) H * @dist F.model.Space F.model.metricSpace.toDist x y := by
  have hreal (j i) : |(D.basis.baseChange ℝ).repr ((F.basis.baseChange ℝ) i) j| ≤ (H : ℝ≥0) := by
    rw [Basis.baseChange_apply, Basis.baseChange_repr_tmul]
    simpa only [Rat.smul_def, mul_one, NNReal.coe_natCast] using (hH i j).abs_real_le
  have h := NilpotentLieBCHGroup.basisQuotientDist_change_le
    (F.basis.baseChange ℝ) (D.basis.baseChange ℝ) D.realLattice
    D.realLattice_closed_discrete.1 H hreal x y
  simp only [Fintype.card_fin] at h
  convert h using 1 <;> rfl

end AdaptedModelData

theorem exists_adapted_model_data (D : RationalFilteredNilmanifold L s d)
    {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) :
    ∃ F : D.AdaptedModelData, F.model.GeometryComplexityLE ((p + 3) ^ 11) ∧
      ∀ i j, rationalLogHeight (D.basis.repr (F.basis i) j) ≤ p + 1 := by
  obtain ⟨b, w, N, _, _, hlayers, hb, _, hc, hN, hNp, hin, hout⟩ :=
    D.exists_controlled_adapted_basis hp hD
  let F : D.AdaptedModelData := ⟨b, w, hlayers, N, hN, hin, hout⟩
  have hp1 : 1 ≤ p + 3 := by linarith
  have hpow : p ≤ (p + 3) ^ 11 := by
    calc
      p ≤ p + 3 := by linarith
      _ = (p + 3) ^ 1 := (pow_one _).symm
      _ ≤ (p + 3) ^ 11 := pow_le_pow_right₀ hp1 (by decide)
  have hdim : (finrank ℚ L : ℝ) ≤ (p + 3) ^ 11 := by
    simpa only [finrank_eq_card_basis D.basis, Fintype.card_fin] using hD.1.trans hpow
  refine ⟨F, ?_, hb⟩
  exact D.filtration.ofAdaptedBasis_geometry b w hlayers D.lattice N hN hin hout
    (by positivity) hdim
    (hNp.trans (Real.exp_le_exp.mpr (pow_le_pow_right₀ hp1 (by decide : 9 ≤ 11)))) hc

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

theorem exists_prescribed_adapted_model {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s d n : ℕ} (D : RationalFilteredNilmanifold L s d)
    (b : Basis (Fin n) ℚ L) (ω : Fin n → ℕ)
    (hF : ∀ k, D.filtration.layer k = Submodule.span ℚ (b '' {i | k ≤ ω i}))
    {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p)
    (hb : ∀ i j, rationalLogHeight (D.basis.repr (b i) j) ≤ p + 1) :
    ∃ (M : ℕ) (hM : 0 < M)
      (hin : scaledIntegerGrid M ⊆ bchSubgroupCoordinates b D.lattice)
      (hout : bchSubgroupCoordinates b D.lattice ⊆ denominatorGrid M),
      (D.filtration.ofAdaptedBasis b ω hF D.lattice M hM hin hout).GeometryComplexityLE
        ((p + 4) ^ 11) := by
  obtain ⟨hdim, _hinverse, hstructure⟩ := D.basis_geometry_of_forward_height b hp hD hb
  let H := ⌈Real.exp (p + 1)⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp (p + 1)
  have hHp : (H : ℝ) ≤ Real.exp (p + 2) := by
    simpa only [show p + 1 + 1 = p + 2 by ring] using
      ceil_exp_le_exp_add_one (by linarith : 0 ≤ p + 1)
  have hentries : ∀ i j, RationalHeightLE (D.basis.repr (b i) j) H :=
    fun i j => rationalHeightLE_ceil_exp (hb i j)
  have hd : (Fintype.card (Fin d) : ℝ) ≤ p + 2 := by
    simpa only [Fintype.card_fin] using hD.1.trans (show p ≤ p + 2 by linarith)
  obtain ⟨M, hM, hMp, hin, hout⟩ := exists_basis_change_grid_exp_bound D.basis b D.lattice
    hH D.grid_pos hentries D.inner_grid D.outer_grid (by linarith : 0 ≤ p + 2) hd
    (hdim.trans (by linarith)) hHp (hD.2.1.trans (Real.exp_le_exp.mpr (by linarith)))
  have hbase : 1 ≤ p + 4 := by linarith
  have hpbig : p ≤ (p + 4) ^ 11 := by
    apply (show p ≤ p + 4 by linarith).trans
    simpa only [pow_one] using pow_le_pow_right₀ hbase (by decide : 1 ≤ 11)
  have hgrid : (M : ℝ) ≤ Real.exp ((p + 4) ^ 11) := by
    have hsmall : (M : ℝ) ≤ Real.exp ((p + 4) ^ 9) := by
      simpa only [show p + 2 + 2 = p + 4 by ring] using hMp
    exact hsmall.trans (Real.exp_le_exp.mpr (pow_le_pow_right₀ hbase (by decide : 9 ≤ 11)))
  refine ⟨M, hM, hin, hout, ?_⟩
  exact D.filtration.ofAdaptedBasis_geometry b ω hF D.lattice M hM hin hout
    (by positivity) (by simpa only [Fintype.card_fin] using hdim.trans hpbig) hgrid hstructure

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t d e : ℕ}

structure AdaptedMapGeometryData (D : RationalFilteredNilmanifold L s d)
    (E : RationalFilteredNilmanifold M t e) (φ : L →ₗ⁅ℚ⁆ M) (p q : ℝ) where
  source : D.AdaptedModelData
  target : E.AdaptedModelData
  budget_nonneg : 0 ≤ q
  forward_budget : p + 1 ≤ q
  source_dimension : (finrank ℚ L : ℝ) ≤ p
  target_dimension : (finrank ℚ M : ℝ) ≤ p
  source_geometry : source.model.GeometryComplexityLE q
  target_geometry : target.model.GeometryComplexityLE q
  source_forward : ∀ i j, rationalLogHeight (D.basis.repr (source.basis i) j) ≤ p + 1
  target_forward : ∀ i j, rationalLogHeight (E.basis.repr (target.basis i) j) ≤ p + 1
  source_inverse : ∀ i j, rationalLogHeight (source.basis.repr (D.basis i) j) ≤ q
  target_inverse : ∀ i j, rationalLogHeight (target.basis.repr (E.basis i) j) ≤ q
  source_structure : ∀ i j k,
    rationalLogHeight (source.basis.repr ⁅source.basis i, source.basis j⁆ k) ≤ q
  target_structure : ∀ i j k,
    rationalLogHeight (target.basis.repr ⁅target.basis i, target.basis j⁆ k) ≤ q
  entries_height : ℕ
  entries_height_pos : 0 < entries_height
  entries_bound : (entries_height : ℝ) ≤ Real.exp q
  entries : ∀ i j,
    RationalHeightLE (target.basis.repr (φ (source.basis j)) i) entries_height
  entries_logHeight : ∀ i j,
    rationalLogHeight (target.basis.repr (φ (source.basis j)) i) ≤ q

theorem exists_native_adapted_map_geometry :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
        {s t d e : ℕ} (D : RationalFilteredNilmanifold L s d)
        (E : RationalFilteredNilmanifold M t e) (φ : L →ₗ⁅ℚ⁆ M) {p : ℝ},
        0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
        (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis i)) j) ≤ p) →
        Nonempty (D.AdaptedMapGeometryData E φ p ((p + 2) ^ C)) := by
  obtain ⟨C, hC, hbudget⟩ := exists_adaptedMapGeometryBudget_fixed_power
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ s t d e D E φ p hp hD hE hφ
  obtain ⟨source, hsource, hsourceForward⟩ := D.exists_adapted_model_data hp hD
  obtain ⟨target, htarget, htargetForward⟩ := E.exists_adapted_model_data hp hE
  obtain ⟨hsourceDim, hsourceInverse, _⟩ :=
    D.basis_geometry_of_forward_height source.basis hp hD hsourceForward
  obtain ⟨htargetDim, htargetInverse, _⟩ :=
    E.basis_geometry_of_forward_height target.basis hp hE htargetForward
  have hp1 : 0 ≤ p + 1 := by linarith
  have hmap := D.markedMap_basisChange_logHeight E source.basis target.basis φ.toLinearMap
    hp1 (hD.mono D (by linarith)) (hE.mono E (by linarith))
    hsourceForward htargetForward (fun i j => (hφ i j).trans (by linarith))
  let r := adaptedMapGeometryBudget p
  have hr : 0 ≤ r := adaptedMapGeometryBudget_nonneg hp
  have hgeomr : (p + 3) ^ 11 ≤ r := adaptedMapGeometryBudget_geometry hp
  have hinverser : (p + 4) ^ 5 ≤ r := by
    have hpow : (p + 4) ^ 5 ≤ (p + 4) ^ 11 :=
      pow_le_pow_right₀ (by linarith) (by decide)
    exact hpow.trans (adaptedMapGeometryBudget_inverse hp)
  have hmapr : adaptedMarkedMapHeightBudget (p + 1) ≤ r :=
    adaptedMapGeometryBudget_markedMap hp
  have hforwardr : p + 1 ≤ r := by
    exact (show p + 1 ≤ p + 2 by linarith).trans (adaptedMapGeometryBudget_parameter hp)
  have hrq : r ≤ (p + 2) ^ C := (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)).trans
    (hbudget p hp)
  have hsourceq := hsource.mono source.model (hgeomr.trans hrq)
  have htargetq := htarget.mono target.model (hgeomr.trans hrq)
  let H := ⌈Real.exp r⌉₊
  refine ⟨{
    source := source
    target := target
    budget_nonneg := hr.trans hrq
    forward_budget := hforwardr.trans hrq
    source_dimension := ?_
    target_dimension := ?_
    source_geometry := hsourceq
    target_geometry := htargetq
    source_forward := hsourceForward
    target_forward := htargetForward
    source_inverse := fun i j => (hsourceInverse i j).trans (hinverser.trans hrq)
    target_inverse := fun i j => (htargetInverse i j).trans (hinverser.trans hrq)
    source_structure := hsourceq.2.2.1
    target_structure := htargetq.2.2.1
    entries_height := H
    entries_height_pos := lt_of_lt_of_le Nat.zero_lt_one (one_le_ceil_exp r)
    entries_bound := (ceil_exp_le_exp_add_one hr).trans (Real.exp_le_exp.mpr (hbudget p hp))
    entries := fun i j => rationalHeightLE_ceil_exp ((hmap j i).trans hmapr)
    entries_logHeight := fun i j => (hmap j i).trans (hmapr.trans hrq)
  }⟩
  · simpa only [Fintype.card_fin] using hsourceDim
  · simpa only [Fintype.card_fin] using htargetDim

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold
open Module

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t d f : ℕ}

structure FixedSourceAdaptedMarkGeometryData
    (D : RationalFilteredNilmanifold L s d)
    (Fmark : RationalFilteredNilmanifold M t f)
    (source : D.AdaptedModelData) (φ : L →ₗ⁅ℚ⁆ M) (p q : ℝ) where
  target : Fmark.AdaptedModelData
  target_geometry : target.model.GeometryComplexityLE q
  target_dimension : (finrank ℚ M : ℝ) ≤ p
  target_forward : ∀ i j,
    rationalLogHeight (Fmark.basis.repr (target.basis i) j) ≤ p + 1
  target_inverse : ∀ i j,
    rationalLogHeight (target.basis.repr (Fmark.basis i) j) ≤ q
  target_structure : ∀ i j k,
    rationalLogHeight (target.basis.repr ⁅target.basis i, target.basis j⁆ k) ≤ q
  entries_height : ℕ
  entries_height_pos : 0 < entries_height
  entries_bound : (entries_height : ℝ) ≤ Real.exp q
  entries : ∀ i j,
    RationalHeightLE (target.basis.repr (φ (source.basis j)) i) entries_height
  entries_logHeight : ∀ i j,
    rationalLogHeight (target.basis.repr (φ (source.basis j)) i) ≤ q

theorem exists_native_fixedSource_adapted_mark_geometry :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
        {s t d f : ℕ} (D : RationalFilteredNilmanifold L s d)
        (Fmark : RationalFilteredNilmanifold M t f)
        (source : D.AdaptedModelData) (φ : L →ₗ⁅ℚ⁆ M) {p : ℝ},
        0 ≤ p → D.GeometryComplexityLE p → Fmark.GeometryComplexityLE p →
        (∀ i j, rationalLogHeight (D.basis.repr (source.basis i) j) ≤ p + 1) →
        (∀ i j, rationalLogHeight (Fmark.basis.repr (φ (D.basis i)) j) ≤ p) →
        Nonempty (D.FixedSourceAdaptedMarkGeometryData Fmark source φ p ((p + 2) ^ C)) := by
  obtain ⟨C, hC, hbudget⟩ := exists_adaptedMapGeometryBudget_fixed_power
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ s t d f D Fmark source φ p hp hD hF hsource hφ
  obtain ⟨target, htarget, htargetForward⟩ := Fmark.exists_adapted_model_data hp hF
  obtain ⟨htargetDim, htargetInverse, _⟩ :=
    Fmark.basis_geometry_of_forward_height target.basis hp hF htargetForward
  have hp1 : 0 ≤ p + 1 := by linarith
  have hmap := D.markedMap_basisChange_logHeight Fmark source.basis target.basis φ.toLinearMap
    hp1 (hD.mono D (by linarith)) (hF.mono Fmark (by linarith))
    hsource htargetForward (fun i j => (hφ i j).trans (by linarith))
  let r := adaptedMapGeometryBudget p
  have hr : 0 ≤ r := adaptedMapGeometryBudget_nonneg hp
  have hgeomr : (p + 3) ^ 11 ≤ r := adaptedMapGeometryBudget_geometry hp
  have hinverser : (p + 4) ^ 5 ≤ r :=
    (pow_le_pow_right₀ (by linarith : 1 ≤ p + 4) (by decide : (5 : ℕ) ≤ 11)).trans
      (adaptedMapGeometryBudget_inverse hp)
  have hmapr : adaptedMarkedMapHeightBudget (p + 1) ≤ r :=
    adaptedMapGeometryBudget_markedMap hp
  have hrq : r ≤ (p + 2) ^ C :=
    (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)).trans (hbudget p hp)
  have htargetq := htarget.mono target.model (hgeomr.trans hrq)
  let H := ⌈Real.exp r⌉₊
  exact ⟨{
    target := target
    target_geometry := htargetq
    target_dimension := by simpa only [Fintype.card_fin] using htargetDim
    target_forward := htargetForward
    target_inverse := fun i j => (htargetInverse i j).trans (hinverser.trans hrq)
    target_structure := htargetq.2.2.1
    entries_height := H
    entries_height_pos := lt_of_lt_of_le Nat.zero_lt_one (one_le_ceil_exp r)
    entries_bound := (ceil_exp_le_exp_add_one hr).trans (Real.exp_le_exp.mpr (hbudget p hp))
    entries := fun i j => rationalHeightLE_ceil_exp ((hmap j i).trans hmapr)
    entries_logHeight := fun i j => (hmap j i).trans (hmapr.trans hrq)
  }⟩

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct NNReal

variable {ι : Type v} [Fintype ι] {L₀ : Type u} {L : ι → Type u}
    [LieRing L₀] [∀ i, LieRing (L i)] [LieAlgebra ℚ L₀] [∀ i, LieAlgebra ℚ (L i)]
    {s d₀ : ℕ} {d : ι → ℕ}
    (D₀ : RationalFilteredNilmanifold L₀ s d₀)
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
    {P : Type*} (observable : P → D₀.Space → ℂ)

theorem optionOriginalObservable_unit_interval
    (hunit : ∀ a y, (observable a y).im = 0 ∧
      0 ≤ (observable a y).re ∧ (observable a y).re ≤ 1) :
    ∀ a y, (optionOriginalObservable D₀ D observable a y).im = 0 ∧
      0 ≤ (optionOriginalObservable D₀ D observable a y).re ∧
      (optionOriginalObservable D₀ D observable a y).re ≤ 1 := by
  intro a y
  exact hunit a (optionOriginalSpaceProjection D₀ D y)

theorem optionOriginalObservable_member_net (sites : Set P) {n : ℕ}
    (centers : Fin n → {a : P // a ∈ sites}) (η : ℝ)
    (hnet : ∀ a ∈ sites, ∃ i, ∀ y,
      ‖observable a y - observable (centers i).val y‖ ≤ η) :
    ∀ a ∈ sites, ∃ i, ∀ y,
      ‖optionOriginalObservable D₀ D observable a y -
        optionOriginalObservable D₀ D observable (centers i).val y‖ ≤ η := by
  intro a ha
  obtain ⟨i, hi⟩ := hnet a ha
  exact ⟨i, fun y => hi (optionOriginalSpaceProjection D₀ D y)⟩

theorem optionOriginalObservable_member_nets (sites : Set P) (entropy : ℝ → ℝ)
    (hnets : ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ entropy η ∧ ∃ centers : Fin n → {a : P // a ∈ sites},
        ∀ a ∈ sites, ∃ i, ∀ y,
          ‖observable a y - observable (centers i).val y‖ ≤ η) :
    ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ entropy η ∧ ∃ centers : Fin n → {a : P // a ∈ sites},
        ∀ a ∈ sites, ∃ i, ∀ y,
          ‖optionOriginalObservable D₀ D observable a y -
            optionOriginalObservable D₀ D observable (centers i).val y‖ ≤ η := by
  intro η hη hη1
  obtain ⟨n, hn, centers, hnet⟩ := hnets η hη hη1
  exact ⟨n, hn, centers,
    optionOriginalObservable_member_net D₀ D observable sites centers η hnet⟩

theorem optionOriginalObservable_adapted_unit_interval
    (adapted : (optionProduct D₀ D).AdaptedModelData)
    (hunit : ∀ a y, (observable a y).im = 0 ∧
      0 ≤ (observable a y).re ∧ (observable a y).re ≤ 1) :
    ∀ a (y : adapted.model.Space),
      (optionOriginalObservable D₀ D observable a y).im = 0 ∧
      0 ≤ (optionOriginalObservable D₀ D observable a y).re ∧
      (optionOriginalObservable D₀ D observable a y).re ≤ 1 :=
  optionOriginalObservable_unit_interval D₀ D observable hunit

theorem optionOriginalObservable_adapted_member_nets
    (adapted : (optionProduct D₀ D).AdaptedModelData)
    (sites : Set P) (entropy : ℝ → ℝ)
    (hnets : ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ entropy η ∧ ∃ centers : Fin n → {a : P // a ∈ sites},
        ∀ a ∈ sites, ∃ i, ∀ y,
          ‖observable a y - observable (centers i).val y‖ ≤ η) :
    ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ entropy η ∧ ∃ centers : Fin n → {a : P // a ∈ sites},
        ∀ a ∈ sites, ∃ i, ∀ y : adapted.model.Space,
          ‖optionOriginalObservable D₀ D observable a y -
            optionOriginalObservable D₀ D observable (centers i).val y‖ ≤ η :=
  optionOriginalObservable_member_nets D₀ D observable sites entropy hnets

noncomputable def optionOriginalAdaptedLipschitzBound (ℓ : ℝ≥0) (H : ℕ) : ℝ≥0 :=
  ℓ * coordinateLipschitzBound d₀
      (Fintype.card (Σ i : Option ι, Fin (optionDimension d₀ d i))) 1 *
    coordinateLipschitzBound
      (Fintype.card (Σ i : Option ι, Fin (optionDimension d₀ d i)))
      (finrank ℚ (∀ i : Option ι, optionLieSpace L₀ L i)) H

include D₀ D in

theorem optionOriginalAdaptedLipschitzBound_le_exp (ℓ : ℝ≥0) (H : ℕ)
    {p : ℝ} (hp : 0 ≤ p) (hℓ : (ℓ : ℝ) ≤ Real.exp p)
    (hd₀ : (d₀ : ℝ) ≤ p)
    (htotal : (Fintype.card (Σ i : Option ι, Fin (optionDimension d₀ d i)) : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) :
    (optionOriginalAdaptedLipschitzBound (L₀ := L₀) (L := L)
      (d₀ := d₀) (d := d) ℓ H : ℝ) ≤ Real.exp (p + 2 * (p + 2) ^ 2) := by
  have hfin : (finrank ℚ (∀ i : Option ι, optionLieSpace L₀ L i) : ℝ) ≤ p := by
    simpa only [finrank_eq_card_basis (optionProduct D₀ D).basis, Fintype.card_fin] using htotal
  have hproj := coordinateLipschitzBound_le_exp d₀
    (Fintype.card (Σ i : Option ι, Fin (optionDimension d₀ d i))) 1 hp hd₀ htotal
    (by simpa only [NNReal.coe_one] using Real.one_le_exp_iff.mpr hp)
  have hbase := coordinateLipschitzBound_le_exp
    (Fintype.card (Σ i : Option ι, Fin (optionDimension d₀ d i)))
    (finrank ℚ (∀ i : Option ι, optionLieSpace L₀ L i)) H hp htotal hfin hH
  calc
    _ ≤ Real.exp p * Real.exp ((p + 2) ^ 2) * Real.exp ((p + 2) ^ 2) := by
      exact mul_le_mul (mul_le_mul hℓ hproj (NNReal.coe_nonneg _) (Real.exp_pos _).le)
        hbase (NNReal.coe_nonneg _) (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

section Metric

variable [TopologicalSpace (ℝ ⊗[ℚ] L₀)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₀)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₀)] [T2Space (ℝ ⊗[ℚ] L₀)]
    [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
    [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
    [TopologicalSpace (ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace L₀ L i))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace L₀ L i))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace L₀ L i))]
    [T2Space (ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace L₀ L i))]

theorem optionOriginalObservable_lipschitz (ℓ : ℝ≥0)
    (hLip : ∀ a, letI := D₀.metricSpace; LipschitzWith ℓ (observable a)) :
    ∀ a, letI := (optionProduct D₀ D).metricSpace
      LipschitzWith (ℓ * coordinateLipschitzBound d₀
        (Fintype.card (Σ i : Option ι, Fin (optionDimension d₀ d i))) 1)
        (optionOriginalObservable D₀ D observable a) := by
  intro a
  let := D₀.metricSpace
  let := (optionProduct D₀ D).metricSpace
  exact (hLip a).comp (optionOriginalSpaceProjection_lipschitz D₀ D)

theorem optionOriginalObservable_adapted_lipschitz
    (adapted : (optionProduct D₀ D).AdaptedModelData) (ℓ : ℝ≥0) (H : ℕ)
    (hH : ∀ i j, RationalHeightLE ((optionProduct D₀ D).basis.repr (adapted.basis i) j) H)
    (hLip : ∀ a, letI := D₀.metricSpace; LipschitzWith ℓ (observable a)) :
    ∀ a, letI := adapted.model.metricSpace
      LipschitzWith (optionOriginalAdaptedLipschitzBound (L₀ := L₀) (L := L)
        (d₀ := d₀) (d := d) ℓ H)
        (fun y : adapted.model.Space => optionOriginalObservable D₀ D observable a y) := by
  intro a
  let := adapted.model.metricSpace
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have horiginal := optionOriginalObservable_lipschitz D₀ D observable ℓ hLip a
  have hd : dist (optionOriginalObservable D₀ D observable a x)
      (optionOriginalObservable D₀ D observable a y) ≤
      ↑(ℓ * coordinateLipschitzBound d₀
        (Fintype.card (Σ i : Option ι, Fin (optionDimension d₀ d i))) 1) *
        @dist (optionProduct D₀ D).Space (optionProduct D₀ D).metricSpace.toDist x y := by
    let := (optionProduct D₀ D).metricSpace
    exact horiginal.dist_le_mul x y
  have hchange := adapted.original_dist_le H hH x y
  calc
    dist (optionOriginalObservable D₀ D observable a x)
        (optionOriginalObservable D₀ D observable a y) ≤
        ↑(ℓ * coordinateLipschitzBound d₀
          (Fintype.card (Σ i : Option ι, Fin (optionDimension d₀ d i))) 1) *
          @dist (optionProduct D₀ D).Space (optionProduct D₀ D).metricSpace.toDist x y := hd
    _ ≤ ↑(ℓ * coordinateLipschitzBound d₀
          (Fintype.card (Σ i : Option ι, Fin (optionDimension d₀ d i))) 1) *
        (coordinateLipschitzBound
          (Fintype.card (Σ i : Option ι, Fin (optionDimension d₀ d i)))
          (finrank ℚ (∀ i : Option ι, optionLieSpace L₀ L i)) H * dist x y) :=
      mul_le_mul_of_nonneg_left hchange (NNReal.coe_nonneg _)
    _ = _ := by simp only [optionOriginalAdaptedLipschitzBound, NNReal.coe_mul]; ring

theorem optionOriginalObservable_adapted_lipschitz_of_logHeight
    (adapted : (optionProduct D₀ D).AdaptedModelData) (ℓ : ℝ≥0) (height : ℝ)
    (hheight : ∀ i j,
      rationalLogHeight ((optionProduct D₀ D).basis.repr (adapted.basis i) j) ≤ height)
    (hLip : ∀ a, letI := D₀.metricSpace; LipschitzWith ℓ (observable a)) :
    ∀ a, letI := adapted.model.metricSpace
      LipschitzWith (optionOriginalAdaptedLipschitzBound (L₀ := L₀) (L := L)
        (d₀ := d₀) (d := d) ℓ ⌈Real.exp height⌉₊)
        (fun y : adapted.model.Space => optionOriginalObservable D₀ D observable a y) :=
  optionOriginalObservable_adapted_lipschitz D₀ D observable adapted ℓ
    ⌈Real.exp height⌉₊ (fun i j => rationalHeightLE_ceil_exp (hheight i j)) hLip

end Metric

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

noncomputable def nativeOptionFixedSourceMarkExponent : ℕ :=
  Classical.choose exists_native_fixedSource_adapted_mark_geometry.{u, v}

theorem nativeOptionFixedSourceMarkExponent_ge_two :
    2 ≤ nativeOptionFixedSourceMarkExponent.{u, v} :=
  (Classical.choose_spec exists_native_fixedSource_adapted_mark_geometry.{u, v}).1

noncomputable def nativeOptionFixedSourceQuotientMarkInput (p : ℝ) : ℝ :=
  (p + 3) ^ 2 + quotientInducedMarkHeightBudget p

theorem nativeOptionFixedSourceQuotientMarkInput_bounds {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ nativeOptionFixedSourceQuotientMarkInput p ∧
    (p + 3) ^ 2 ≤ nativeOptionFixedSourceQuotientMarkInput p ∧
    quotientInducedMarkHeightBudget p ≤ nativeOptionFixedSourceQuotientMarkInput p := by
  have hinduced : 0 ≤ quotientInducedMarkHeightBudget p := by
    unfold quotientInducedMarkHeightBudget
    positivity
  have hjoint : 0 ≤ (p + 3) ^ 2 := sq_nonneg _
  dsimp [nativeOptionFixedSourceQuotientMarkInput]
  constructor
  · exact add_nonneg hjoint hinduced
  constructor <;> linarith

variable {Pivot : Type v} [Fintype Pivot]
    {L M : Type u} {Partner : Pivot → Type u}
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    [∀ a, LieRing (Partner a)] [∀ a, LieAlgebra ℚ (Partner a)]
    {s d f dQ : ℕ} {dp : Pivot → ℕ}
    (D : RationalFilteredNilmanifold L s d)
    (Mmark : RationalFilteredNilmanifold M s f)
    (ideal : LieIdeal ℚ L)
    (hkill : D.filtration.layer (s + 1) ≤ ideal.toSubmodule)
    (Q : RationalFilteredNilmanifold (L ⧸ ideal) s dQ)
    (hQ : Q.filtration = D.filtration.quotientLie ideal hkill)
    (atoms : ∀ a, RationalFilteredNilmanifold (Partner a) s (dp a))
    (φ : L →ₗ⁅ℚ⁆ M) (hker : ∀ x ∈ ideal, φ x = 0)
    (hφ : ∀ k, ∀ x ∈ D.filtration.layer k, φ x ∈ Mmark.filtration.layer k)
    (source : (optionProduct Q atoms).AdaptedModelData)

include hQ hφ in

theorem nativeOptionFixedSourceQuotientMark_mem_layer
    (k : ℕ) (x : ∀ i : Option Pivot, optionLieSpace (L ⧸ ideal) Partner i)
    (hx : x ∈ source.model.filtration.layer k) :
    optionMarkedLieMap (L := Partner) (quotientInducedMark ideal φ hker) x ∈
      (NilpotentLieFiltration.pi
        (optionFiltrations Mmark.filtration (fun a => (atoms a).filtration))).layer k := by
  have hinduced : ∀ k, ∀ y ∈ Q.filtration.layer k,
      quotientInducedMark ideal φ hker y ∈ Mmark.filtration.layer k := by
    intro k y hy
    rw [hQ] at hy
    exact D.filtration.quotientInducedMark_mem_layer Mmark.filtration
      ideal hkill φ hker hφ k y hy
  have hfiltration : (fun i => (optionFactors Q atoms i).filtration) =
      optionFiltrations Q.filtration (fun a => (atoms a).filtration) := by
    funext i
    cases i <;> rfl
  change x ∈ (NilpotentLieFiltration.pi (fun i => (optionFactors Q atoms i).filtration)).layer k at hx
  rw [hfiltration] at hx
  exact optionMarkedLieMap_mem_layer Q.filtration Mmark.filtration
    (fun a => (atoms a).filtration) (quotientInducedMark ideal φ hker) hinduced k x hx

include hQ hφ in

theorem exists_nativeOptionFixedSourceQuotientMarkGeometry
    {p : ℝ} (hp : 0 ≤ p)
    (hD : D.GeometryComplexityLE p) (hMmark : Mmark.GeometryComplexityLE p)
    (hQgeometry : Q.GeometryComplexityLE p)
    (hAtoms : ∀ a, (atoms a).GeometryComplexityLE p)
    (hPivot : (Fintype.card Pivot : ℝ) ≤ p)
    (hprojection : ∀ i j, rationalLogHeight
      (Q.basis.repr (lieQuotientMap ideal (D.basis j)) i) ≤ p)
    (hmark : ∀ i j, rationalLogHeight (Mmark.basis.repr (φ (D.basis j)) i) ≤ p)
    (hsource : ∀ i j, rationalLogHeight
      ((optionProduct Q atoms).basis.repr (source.basis i) j) ≤ (p + 3) ^ 2 + 1) :
    ∃ markGeometry : (optionProduct Q atoms).FixedSourceAdaptedMarkGeometryData
        (optionProduct Mmark atoms) source
        (optionMarkedLieMap (L := Partner) (quotientInducedMark ideal φ hker))
        (nativeOptionFixedSourceQuotientMarkInput p)
        ((nativeOptionFixedSourceQuotientMarkInput p + 2) ^ nativeOptionFixedSourceMarkExponent.{max u v, max u v}),
      markGeometry.target.model.filtration =
        NilpotentLieFiltration.pi
          (optionFiltrations Mmark.filtration (fun a => (atoms a).filtration)) ∧
      ∀ k, ∀ x ∈ source.model.filtration.layer k,
        optionMarkedLieMap (L := Partner) (quotientInducedMark ideal φ hker) x ∈
          markGeometry.target.model.filtration.layer k := by
  have hinput := nativeOptionFixedSourceQuotientMarkInput_bounds hp
  have hinduced := D.quotientInducedMark_native_logHeight Mmark ideal Q φ hker
    hp hD hQgeometry hprojection hmark
  have hinduced0 : 0 ≤ quotientInducedMarkHeightBudget p := by
    unfold quotientInducedMarkHeightBudget
    positivity
  have hoption := optionMarkedLieMap_native_logHeight Q Mmark atoms
    (quotientInducedMark ideal φ hker) hinduced0 hinduced
  have hsourceGeo := optionProduct_geometry Q atoms hp hPivot hQgeometry hAtoms
  have htargetGeo := optionProduct_geometry Mmark atoms hp hPivot hMmark hAtoms
  obtain ⟨markGeometry⟩ :=
    (Classical.choose_spec exists_native_fixedSource_adapted_mark_geometry.{max u v, max u v}).2
      (optionProduct Q atoms) (optionProduct Mmark atoms) source
      (optionMarkedLieMap (L := Partner) (quotientInducedMark ideal φ hker))
      hinput.1
      (hsourceGeo.mono (optionProduct Q atoms) hinput.2.1)
      (htargetGeo.mono (optionProduct Mmark atoms) hinput.2.1)
      (fun i j => (hsource i j).trans (by linarith only [hinput.2.1]))
      (fun i j => (hoption j i).trans hinput.2.2)
  have hMark : markGeometry.target.model.filtration =
      NilpotentLieFiltration.pi
        (optionFiltrations Mmark.filtration (fun a => (atoms a).filtration)) := by
    change NilpotentLieFiltration.pi (fun i => (optionFactors Mmark atoms i).filtration) = _
    congr 1
    funext i
    cases i <;> rfl
  refine ⟨markGeometry, hMark, ?_⟩
  intro k x hx
  rw [hMark]
  exact D.nativeOptionFixedSourceQuotientMark_mem_layer Mmark ideal hkill Q hQ
    atoms φ hker hφ source k x hx

theorem optionAdaptedModel_layers
    (target : (optionProduct Mmark atoms).AdaptedModelData) (k : ℕ) :
    (NilpotentLieFiltration.pi
      (optionFiltrations Mmark.filtration (fun a => (atoms a).filtration))).layer k =
      Submodule.span ℚ (target.basis '' {i | k ≤ target.weight i}) := by
  have hfiltration : (fun i => (optionFactors Mmark atoms i).filtration) =
      optionFiltrations Mmark.filtration (fun a => (atoms a).filtration) := by
    funext i
    cases i <;> rfl
  have hlayers := target.layers k
  change (NilpotentLieFiltration.pi (fun i => (optionFactors Mmark atoms i).filtration)).layer k =
    Submodule.span ℚ (target.basis '' {i | k ≤ target.weight i}) at hlayers
  rw [hfiltration] at hlayers
  exact hlayers

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

variable {Pivot : Type v} [Fintype Pivot]
    {L M : Type u} {Partner : Pivot → Type u}
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    [∀ a, LieRing (Partner a)] [∀ a, LieAlgebra ℚ (Partner a)]
    {s d f dQ : ℕ} {dp : Pivot → ℕ}
    (D : RationalFilteredNilmanifold L s d)
    (Mmark : RationalFilteredNilmanifold M s f)
    (ideal : LieIdeal ℚ L)
    (hkill : D.filtration.layer (s + 1) ≤ ideal.toSubmodule)
    (Q : RationalFilteredNilmanifold (L ⧸ ideal) s dQ)
    (hQ : Q.filtration = D.filtration.quotientLie ideal hkill)
    (atoms : ∀ a, RationalFilteredNilmanifold (Partner a) s (dp a))
    (φ : L →ₗ⁅ℚ⁆ M) (hker : ∀ x ∈ ideal, φ x = 0)
    (source : (optionProduct Q atoms).AdaptedModelData)
    (hsurj : ∀ k, ∀ y ∈ Mmark.filtration.layer k,
      ∃ x ∈ D.filtration.layer k, φ x = y)

include hQ hsurj in

theorem nativeOptionFixedSourceQuotientMark_layer_surjective
    (k : ℕ) (y : ∀ i : Option Pivot, optionLieSpace M Partner i)
    (hy : y ∈ (NilpotentLieFiltration.pi
      (optionFiltrations Mmark.filtration (fun a => (atoms a).filtration))).layer k) :
    ∃ x ∈ source.model.filtration.layer k,
      optionMarkedLieMap (L := Partner) (quotientInducedMark ideal φ hker) x = y := by
  have hcoord := (mem_pi_layer
    (optionFiltrations Mmark.filtration (fun a => (atoms a).filtration)) k y).mp hy
  obtain ⟨x₀, hx₀, hxy₀⟩ := hsurj k (y none) (hcoord none)
  let x : ∀ i : Option Pivot, optionLieSpace (L ⧸ ideal) Partner i
    | none => lieQuotientMap ideal x₀
    | some a => y (some a)
  refine ⟨x, ?_, ?_⟩
  · change x ∈ (NilpotentLieFiltration.pi
      (fun i => (optionFactors Q atoms i).filtration)).layer k
    apply (mem_pi_layer (fun i => (optionFactors Q atoms i).filtration) k x).mpr
    intro i
    cases i with
    | none =>
      change lieQuotientMap ideal x₀ ∈ Q.filtration.layer k
      rw [hQ]
      exact ⟨x₀, hx₀, rfl⟩
    | some a => exact hcoord (some a)
  · funext i
    cases i with
    | none => exact hxy₀
    | some a => rfl

include hQ hsurj in

theorem nativeOptionFixedSourceQuotientMark_adaptedTarget_layer_surjective
    (target : (optionProduct Mmark atoms).AdaptedModelData)
    (k : ℕ) (y : ∀ i : Option Pivot, optionLieSpace M Partner i)
    (hy : y ∈ target.model.filtration.layer k) :
    ∃ x ∈ source.model.filtration.layer k,
      optionMarkedLieMap (L := Partner) (quotientInducedMark ideal φ hker) x = y := by
  have htarget : target.model.filtration = NilpotentLieFiltration.pi
      (optionFiltrations Mmark.filtration (fun a => (atoms a).filtration)) := by
    change NilpotentLieFiltration.pi (fun i => (optionFactors Mmark atoms i).filtration) = _
    congr 1
    funext i
    cases i <;> rfl
  rw [htarget] at hy
  exact D.nativeOptionFixedSourceQuotientMark_layer_surjective Mmark ideal hkill Q hQ
    atoms φ hker source hsurj k y hy

end Erdos3.RationalFilteredNilmanifold

end

end OAI

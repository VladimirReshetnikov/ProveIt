/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import Mathlib.Algebra.Lie.Prod
import OAI.Combinatorics.Progressions.Estimates.QuotientInducedMark
import OAI.Combinatorics.Progressions.Linear.RealifiedTripleProjections
import OAI.Combinatorics.Progressions.Nilpotent.BCHUniformQuotientCharts

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

def squareLayer (j : ℕ) : Submodule ℚ (L × L) where
  carrier := {x | x.1 ∈ F.layer j ∧ x.2 ∈ F.layer j ∧ x.1 - x.2 ∈ F.layer (j + 1)}
  zero_mem' := by simp
  add_mem' hx hy := by
    refine ⟨(F.layer j).add_mem hx.1 hy.1, (F.layer j).add_mem hx.2.1 hy.2.1, ?_⟩
    change _ + _ - (_ + _) ∈ F.layer (j + 1)
    rw [show ∀ a b c d : L, a + b - (c + d) = (a - c) + (b - d) by intros; abel]
    exact (F.layer (j + 1)).add_mem hx.2.2 hy.2.2
  smul_mem' r x hx := by
    refine ⟨(F.layer j).smul_mem r hx.1, (F.layer j).smul_mem r hx.2.1, ?_⟩
    change r • x.1 - r • x.2 ∈ F.layer (j + 1)
    rw [← smul_sub]
    exact (F.layer (j + 1)).smul_mem r hx.2.2

@[simp] theorem mem_squareLayer (j : ℕ) (x : L × L) :
    x ∈ F.squareLayer j ↔
      x.1 ∈ F.layer j ∧ x.2 ∈ F.layer j ∧ x.1 - x.2 ∈ F.layer (j + 1) := Iff.rfl

theorem squareLayer_antitone : Antitone F.squareLayer := by
  intro i j hij x hx
  exact ⟨F.antitone hij hx.1, F.antitone hij hx.2.1,
    F.antitone (Nat.add_le_add_right hij 1) hx.2.2⟩

theorem squareLayer_lie_mem {i j : ℕ} {x y : L × L}
    (hx : x ∈ F.squareLayer i) (hy : y ∈ F.squareLayer j) :
    ⁅x, y⁆ ∈ F.squareLayer (i + j) := by
  refine ⟨F.lie_mem hx.1 hy.1, F.lie_mem hx.2.1 hy.2.1, ?_⟩
  change ⁅x.1, y.1⁆ - ⁅x.2, y.2⁆ ∈ F.layer (i + j + 1)
  have he : ⁅x.1, y.1⁆ - ⁅x.2, y.2⁆ =
      ⁅x.1 - x.2, y.1⁆ + ⁅x.2, y.1 - y.2⁆ := by
    simp only [sub_lie, lie_sub]
    abel
  rw [he]
  exact (F.layer (i + j + 1)).add_mem
    (by simpa only [Nat.add_right_comm i 1 j] using F.lie_mem hx.2.2 hy.1)
    (by simpa only [Nat.add_assoc] using F.lie_mem hx.2.1 hy.2.2)

def squareLieSubalgebra : LieSubalgebra ℚ (L × L) :=
  { F.squareLayer 1 with
    lie_mem' := fun hx hy => F.squareLayer_antitone (by omega) (F.squareLayer_lie_mem hx hy) }

@[simp] theorem mem_squareLieSubalgebra (x : L × L) :
    x ∈ F.squareLieSubalgebra ↔ x.1 - x.2 ∈ F.layer 2 := by
  change x ∈ F.squareLayer 1 ↔ _
  simp only [mem_squareLayer, F.one_eq_top, Submodule.mem_top, true_and]

def squareFiltration : NilpotentLieFiltration F.squareLieSubalgebra s where
  layer j := (F.squareLayer j).comap F.squareLieSubalgebra.incl.toLinearMap
  antitone := fun _ _ hij x hx => F.squareLayer_antitone hij hx
  one_eq_top := by
    apply top_unique
    intro x _
    exact x.property
  lie_mem := fun hx hy => F.squareLayer_lie_mem hx hy
  terminal := by
    apply bot_unique
    intro x hx
    change x = 0
    apply Subtype.ext
    apply Prod.ext
    · exact (Submodule.mem_bot ℚ).mp (F.terminal ▸ hx.1)
    · exact (Submodule.mem_bot ℚ).mp (F.terminal ▸ hx.2.1)

@[simp] theorem mem_squareFiltration_layer (j : ℕ) (x : F.squareLieSubalgebra) :
    x ∈ F.squareFiltration.layer j ↔ (x : L × L) ∈ F.squareLayer j := Iff.rfl

theorem mem_squareFiltration_top (x : F.squareLieSubalgebra) :
    x ∈ F.squareFiltration.layer s ↔ x.val.1 ∈ F.layer s ∧ x.val.1 = x.val.2 := by
  change x.val ∈ F.squareLayer s ↔ _
  rw [mem_squareLayer, F.terminal, Submodule.mem_bot, sub_eq_zero]
  constructor
  · exact fun h => ⟨h.1, h.2.2⟩
  · exact fun h => ⟨h.1, h.2 ▸ h.1, h.2⟩

def squareFst : F.squareLieSubalgebra →ₗ⁅ℚ⁆ L :=
  (LieHom.fst ℚ L L).comp F.squareLieSubalgebra.incl

def squareSnd : F.squareLieSubalgebra →ₗ⁅ℚ⁆ L :=
  (LieHom.snd ℚ L L).comp F.squareLieSubalgebra.incl

@[simp] theorem squareFst_apply (x : F.squareLieSubalgebra) : F.squareFst x = x.val.1 := rfl
@[simp] theorem squareSnd_apply (x : F.squareLieSubalgebra) : F.squareSnd x = x.val.2 := rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

theorem NilpotentLieFiltration.top_layer_central (F : NilpotentLieFiltration L s)
    {v : L} (hv : v ∈ F.layer s) (w : L) : ⁅v, w⁆ = 0 := by
  have hw : w ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
  have h := F.lie_mem hv hw
  simpa only [F.terminal, Submodule.mem_bot] using h

theorem rationalLieInclusion_central (v : L) (hv : ∀ w : L, ⁅v, w⁆ = 0)
    (w : ℝ ⊗[ℚ] L) : ⁅rationalLieInclusion v, w⁆ = 0 := by
  induction w using TensorProduct.inductionOn with
  | tmul r w => simp only [rationalLieInclusion_apply, LieAlgebra.ExtendScalars.bracket_tmul,
      hv, TensorProduct.tmul_zero]
  | add x y hx hy => rw [lie_add, hx, hy, add_zero]

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem scaled_basis_mem_bchSubgroup (b : Basis κ ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (N : ℕ)
    (hgrid : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ) (j : κ) :
    (⟨(N : ℚ) • b j⟩ : NilpotentLieBCHGroup L s hnil) ∈ Γ := by
  classical
  have hx : b.equivFun ((N : ℚ) • b j) ∈ scaledIntegerGrid N := by
    refine ⟨fun k => if k = j then 1 else 0, ?_⟩
    ext k
    by_cases h : k = j
    · subst k
      simp [Basis.equivFun_apply]
    · simp [Basis.equivFun_apply, h]
  have h := hgrid hx
  change (⟨b.equivFun.symm (b.equivFun ((N : ℚ) • b j))⟩ : NilpotentLieBCHGroup L s hnil) ∈ Γ at h
  simpa only [LinearEquiv.symm_apply_apply] using h

theorem scaled_real_basis_mem_realification (b : Basis κ ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (N : ℕ)
    (hgrid : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ) (j : κ) :
    (⟨(N : ℝ) • (b.baseChange ℝ) j⟩ : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s
      (realification_lowerCentralSeries_eq_bot hnil)) ∈ Γ.map realificationHom := by
  refine Subgroup.mem_map.mpr ⟨⟨(N : ℚ) • b j⟩, scaled_basis_mem_bchSubgroup b Γ N hgrid j, ?_⟩
  apply NilpotentLieBCHGroup.ext
  change rationalLieInclusion ((N : ℚ) • b j) = (N : ℝ) • (b.baseChange ℝ) j
  simp only [Nat.cast_smul_eq_nsmul, map_nsmul, Basis.baseChange_apply, rationalLieInclusion_apply]

omit [Fintype κ] in
theorem scaled_real_basis_central (b : Basis κ ℚ L) (j : κ)
    (hv : ∀ w : L, ⁅b j, w⁆ = 0) (N : ℕ) (w : ℝ ⊗[ℚ] L) :
    ⁅(N : ℝ) • (b.baseChange ℝ) j, w⁆ = 0 := by
  rw [smul_lie, Basis.baseChange_apply]
  change (N : ℝ) • ⁅rationalLieInclusion (b j), w⁆ = 0
  rw [rationalLieInclusion_central _ hv, smul_zero]

omit [Fintype κ] in
theorem scaled_real_basis_coordinate_bound (e : Basis ι ℚ L) (b : Basis κ ℚ L)
    (N : ℕ) (j : κ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ i, |(e.repr (b j) i : ℝ)| ≤ B) :
    coordinateL2Norm ((e.baseChange ℝ).equivFun ((N : ℝ) • (b.baseChange ℝ) j)) ≤
      (Fintype.card ι + 1) * ((N : ℝ) * B) := by
  apply coordinateL2Norm_le_card_bound _ (mul_nonneg (Nat.cast_nonneg N) hB)
  intro i
  change |(e.baseChange ℝ).repr ((N : ℝ) • (b.baseChange ℝ) j) i| ≤ _
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, abs_mul]
  rw [abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
  simpa [Basis.baseChange_apply, Basis.baseChange_repr_tmul, Algebra.smul_def] using hb i

end Erdos3

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem omitted_weighted_top (i : σ) (hi : bound i = 1) (hs : ∑ j, bound j = s) :
    F.weightedLayer (omittedCoordinateWeight i) s = ⊥ := by
  have h := omittedCoordinateWeight_total i bound
  rw [hi, hs] at h
  simpa only [h] using F.weightedLayer_terminal (omittedCoordinateWeight i)

theorem additiveTriple_top_group_relation (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (htop : F.weightedLayer c s = ⊥)
    (g : (F.additiveTripleFiltration i hi c hc).Group)
    (hg : g ∈ (F.additiveTripleFiltration i hi c hc).subgroup s) :
    (NilpotentLieBCHGroup.map (F.additiveTripleFirst i hi c hc) g : F.Group) =
      NilpotentLieBCHGroup.map (F.additiveTripleSecond i hi c hc) g *
      NilpotentLieBCHGroup.map (F.additiveTripleThird i hi c hc) g := by
  apply NilpotentLieBCHGroup.ext
  change F.additiveTripleFirst i hi c hc g.coord =
    lieBCH s (F.additiveTripleSecond i hi c hc g.coord) (F.additiveTripleThird i hi c hc g.coord)
  rw [lieBCH_eq_add_of_lie_eq_zero F.ordinary.lowerCentralSeries_eq_bot
    (F.ordinary.top_layer_central (F.additiveTripleProjections_mem i hi c hc hg).2.1 _)]
  exact F.additiveTripleTop_relation i hi c hc htop hg

theorem additiveTriple_omitted_top_group_relation (i : σ) (hi : bound i = 1)
    (hs : ∑ j, bound j = s)
    (g : (F.additiveTripleFiltration i hi.le (omittedCoordinateWeight i)
      (omittedCoordinateWeight_le_one i)).Group)
    (hg : g ∈ (F.additiveTripleFiltration i hi.le (omittedCoordinateWeight i)
      (omittedCoordinateWeight_le_one i)).subgroup s) :
    (NilpotentLieBCHGroup.map (F.additiveTripleFirst i hi.le (omittedCoordinateWeight i)
      (omittedCoordinateWeight_le_one i)) g : F.Group) =
      NilpotentLieBCHGroup.map (F.additiveTripleSecond i hi.le (omittedCoordinateWeight i)
        (omittedCoordinateWeight_le_one i)) g *
      NilpotentLieBCHGroup.map (F.additiveTripleThird i hi.le (omittedCoordinateWeight i)
        (omittedCoordinateWeight_le_one i)) g :=
  F.additiveTriple_top_group_relation i hi.le _ _ (F.omitted_weighted_top i hi hs) g hg

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def squareFstHom : F.squareFiltration.Group →* F.Group :=
  map F.squareFst

noncomputable def squareSndHom : F.squareFiltration.Group →* F.Group :=
  map F.squareSnd

@[simp] theorem squareFstHom_coord (g : F.squareFiltration.Group) :
    (F.squareFstHom g).coord = g.coord.val.1 := rfl

@[simp] theorem squareSndHom_coord (g : F.squareFiltration.Group) :
    (F.squareSndHom g).coord = g.coord.val.2 := rfl

noncomputable def squareLattice (Γ : Subgroup F.Group) : Subgroup F.squareFiltration.Group :=
  Γ.comap F.squareFstHom ⊓ Γ.comap F.squareSndHom

theorem mem_squareLattice (Γ : Subgroup F.Group) (g : F.squareFiltration.Group) :
    g ∈ F.squareLattice Γ ↔ F.squareFstHom g ∈ Γ ∧ F.squareSndHom g ∈ Γ := Iff.rfl

theorem squareLattice_le_fst (Γ : Subgroup F.Group) : F.squareLattice Γ ≤ Γ.comap F.squareFstHom :=
  fun _ h => h.1

theorem squareLattice_le_snd (Γ : Subgroup F.Group) : F.squareLattice Γ ≤ Γ.comap F.squareSndHom :=
  fun _ h => h.2

theorem square_projections_joint_injective {g h : F.squareFiltration.Group}
    (hfst : F.squareFstHom g = F.squareFstHom h) (hsnd : F.squareSndHom g = F.squareSndHom h) : g = h := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  exact Prod.ext (congrArg NilpotentLieBCHGroup.coord hfst) (congrArg NilpotentLieBCHGroup.coord hsnd)

theorem square_top_projections {g : F.squareFiltration.Group}
    (hg : g ∈ F.squareFiltration.subgroup s) :
    F.squareFstHom g ∈ F.subgroup s ∧ F.squareFstHom g = F.squareSndHom g := by
  have h := (F.mem_squareFiltration_top g.coord).mp hg
  exact ⟨h.1, NilpotentLieBCHGroup.ext h.2⟩

theorem top_commutes (g : F.Group) (hg : g ∈ F.subgroup s) (h : F.Group) : Commute g h :=
  commute_of_lie_eq_zero g h (F.top_layer_central hg h.coord)

end Erdos3.NilpotentLieFiltration

namespace Erdos3

variable {G H : Type*} [Group G] [Group H]

theorem cosetMap_smul (Γ : Subgroup G) (Λ : Subgroup H) (φ : G →* H)
    (hφ : Γ ≤ Λ.comap φ) (g : G) (x : G ⧸ Γ) :
    cosetMap Γ Λ φ hφ (g • x) = φ g • cosetMap Γ Λ φ hφ x := by
  induction x using Quotient.inductionOn with
  | h a =>
    change (QuotientGroup.mk (φ (g * a)) : H ⧸ Λ) = QuotientGroup.mk (φ g * φ a)
    rw [map_mul]

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem realLayer_eq_span_basis (b : Basis ι ℚ L) (i : ℕ) (S : Set ι)
    (hS : F.layer i = Submodule.span ℚ (b '' S)) :
    (F.realLayer i).toSubmodule = Submodule.span ℝ (b.baseChange ℝ '' S) := by
  change (F.layer i).baseChange ℝ = _
  rw [hS, Submodule.baseChange_span, Set.image_image]
  congr 2
  funext j
  exact (Basis.baseChange_apply ℝ b j).symm

theorem realLayer_le_span_scaled_basis (b : Basis ι ℚ L) (i : ℕ) (S : Set ι)
    (hS : F.layer i = Submodule.span ℚ (b '' S)) (N : ℕ) (hN : 0 < N) :
    (F.realLayer i).toSubmodule ≤
      Submodule.span ℝ (Set.range (fun j : S => (N : ℝ) • b.baseChange ℝ j)) := by
  rw [F.realLayer_eq_span_basis b i S hS]
  apply Submodule.span_le.mpr
  rintro v ⟨j, hj, rfl⟩
  change b.baseChange ℝ j ∈
    Submodule.span ℝ (Set.range (fun j : S => (N : ℝ) • b.baseChange ℝ j))
  have h : (N : ℝ)⁻¹ • ((N : ℝ) • b.baseChange ℝ j) ∈
      Submodule.span ℝ (Set.range (fun j : S => (N : ℝ) • b.baseChange ℝ j)) :=
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩)
  simpa only [smul_smul, inv_mul_cancel₀ (show (N : ℝ) ≠ 0 by exact_mod_cast hN.ne'),
    one_smul] using h

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators TensorProduct

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem realAdditiveTripleProjection_mem (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (j : Fin 3) {n : ℕ}
    {g : (F.additiveTripleFiltration i hi c hc).realification.Group}
    (hg : g ∈ (F.additiveTripleFiltration i hi c hc).realification.subgroup n) :
    F.realAdditiveTripleProjection i hi c hc j g ∈ F.realification.ordinary.subgroup n := by
  have hm := (F.realifiedAdditiveTripleEquiv_mem_layer i hi c hc n g.coord).mp hg
  obtain ⟨h₀, h₁, h₂⟩ := F.realification.additiveTripleProjections_mem i hi c hc hm
  change (F.realAdditiveTripleProjection i hi c hc j g).coord ∈ F.realification.ordinary.layer n
  rw [F.realAdditiveTripleProjection_coord]
  fin_cases j
  · exact h₀
  · exact h₁
  · exact h₂

theorem realAdditiveTriple_top_group_relation (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1)
    (htop : F.realification.weightedLayer c s = ⊥)
    (g : (F.additiveTripleFiltration i hi c hc).realification.Group)
    (hg : g ∈ (F.additiveTripleFiltration i hi c hc).realification.subgroup s) :
    F.realAdditiveTripleProjection i hi c hc 0 g =
      F.realAdditiveTripleProjection i hi c hc 1 g *
        F.realAdditiveTripleProjection i hi c hc 2 g := by
  let q : (F.realification.additiveTripleFiltration i hi c hc).Group :=
    ⟨F.realifiedAdditiveTripleEquiv i hi c hc g.coord⟩
  have hq : q ∈ (F.realification.additiveTripleFiltration i hi c hc).subgroup s :=
    (F.realifiedAdditiveTripleEquiv_mem_layer i hi c hc s g.coord).mp hg
  have he (j : Fin 3) : F.realAdditiveTripleProjection i hi c hc j g =
      (NilpotentLieBCHGroup.map (F.realification.additiveTripleProjection i hi c hc j) q :
        F.realification.Group) := by
    apply NilpotentLieBCHGroup.ext
    exact F.realAdditiveTripleProjection_coord i hi c hc j g
  rw [he 0, he 1, he 2]
  exact F.realification.additiveTriple_top_group_relation i hi c hc htop q hq

theorem realAdditiveTriple_top_phase {A : Type*} [Add A]
    (i : σ) (hi : bound i ≤ 1) (c : σ → ℕ) (hc : ∀ j, c j ≤ 1)
    (htop : F.realification.weightedLayer c s = ⊥) (χ : F.realification.Group → A)
    (hχ : ∀ z w, z ∈ F.realification.ordinary.subgroup s →
      w ∈ F.realification.ordinary.subgroup s → χ (z * w) = χ z + χ w)
    (g : (F.additiveTripleFiltration i hi c hc).realification.Group)
    (hg : g ∈ (F.additiveTripleFiltration i hi c hc).realification.subgroup s) :
    χ (F.realAdditiveTripleProjection i hi c hc 0 g) =
      χ (F.realAdditiveTripleProjection i hi c hc 1 g) +
        χ (F.realAdditiveTripleProjection i hi c hc 2 g) := by
  rw [F.realAdditiveTriple_top_group_relation i hi c hc htop g hg]
  exact hχ _ _ (F.realAdditiveTripleProjection_mem i hi c hc 1 hg)
    (F.realAdditiveTripleProjection_mem i hi c hc 2 hg)

theorem realAdditiveTriple_omitted_top_group_relation (i : σ) (hi : bound i = 1)
    (hs : ∑ j, bound j = s)
    (g : (F.additiveTripleFiltration i hi.le (omittedCoordinateWeight i)
      (omittedCoordinateWeight_le_one i)).realification.Group)
    (hg : g ∈ (F.additiveTripleFiltration i hi.le (omittedCoordinateWeight i)
      (omittedCoordinateWeight_le_one i)).realification.subgroup s) :
    F.realAdditiveTripleProjection i hi.le _ (omittedCoordinateWeight_le_one i) 0 g =
      F.realAdditiveTripleProjection i hi.le _ (omittedCoordinateWeight_le_one i) 1 g *
        F.realAdditiveTripleProjection i hi.le _ (omittedCoordinateWeight_le_one i) 2 g :=
  F.realAdditiveTriple_top_group_relation i hi.le _ _
    (F.realification.omitted_weighted_top i hi hs) g hg

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup CircleFourier

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (Γ : Subgroup F.Group)

noncomputable def squareObservable (ε : F.Group) (u : F.Group ⧸ Γ → ℂ)
    (x : F.squareFiltration.Group ⧸ F.squareLattice Γ) : ℂ :=
  u (ε • cosetMap (F.squareLattice Γ) Γ F.squareFstHom (F.squareLattice_le_fst Γ) x) *
    star (u (cosetMap (F.squareLattice Γ) Γ F.squareSndHom (F.squareLattice_le_snd Γ) x))

theorem squareObservable_mk (ε : F.Group) (u : F.Group ⧸ Γ → ℂ)
    (g : F.squareFiltration.Group) :
    F.squareObservable Γ ε u (QuotientGroup.mk g) =
      u (QuotientGroup.mk (ε * F.squareFstHom g)) * star (u (QuotientGroup.mk (F.squareSndHom g))) := rfl

theorem squareObservable_norm_le (ε : F.Group) (u : F.Group ⧸ Γ → ℂ)
    {B : ℝ} (hB : 0 ≤ B) (hu : ∀ x, ‖u x‖ ≤ B)
    (x : F.squareFiltration.Group ⧸ F.squareLattice Γ) :
    ‖F.squareObservable Γ ε u x‖ ≤ B ^ 2 := by
  rw [squareObservable, norm_mul, norm_star, pow_two]
  exact mul_le_mul (hu _) (hu _) (norm_nonneg _) hB

theorem squareObservable_top_invariant (ε : F.Group) (u : F.Group ⧸ Γ → ℂ)
    (χ : F.Group → CircleFourier.Circle)
    (hu : ∀ z ∈ F.subgroup s, ∀ x, u (z • x) = character (χ z) * u x)
    (k : F.squareFiltration.Group) (hk : k ∈ F.squareFiltration.subgroup s)
    (x : F.squareFiltration.Group ⧸ F.squareLattice Γ) :
    F.squareObservable Γ ε u (k • x) = F.squareObservable Γ ε u x := by
  obtain ⟨hz, heq⟩ := F.square_top_projections hk
  let z := F.squareFstHom k
  have hε : ∀ y : F.Group ⧸ Γ, ε • (z • y) = z • (ε • y) := by
    intro y
    rw [← mul_smul, ← mul_smul, (F.top_commutes z hz ε).eq]
  simp only [squareObservable, cosetMap_smul, ← heq]
  rw [hε, hu z hz, hu z hz, star_mul]
  have hc : character (χ z) * star (character (χ z)) = 1 := by
    rw [← character_neg, ← character_add, add_neg_cancel, character_zero]
  calc
    _ = (character (χ z) * star (character (χ z))) *
        (u (ε • cosetMap (F.squareLattice Γ) Γ F.squareFstHom (F.squareLattice_le_fst Γ) x) *
          star (u (cosetMap (F.squareLattice Γ) Γ F.squareSndHom (F.squareLattice_le_snd Γ) x))) := by ring
    _ = _ := by rw [hc, one_mul]

theorem exists_square_observable_descent (ε : F.Group) (u : F.Group ⧸ Γ → ℂ)
    (χ : F.Group → CircleFourier.Circle)
    (hu : ∀ z ∈ F.subgroup s, ∀ x, u (z • x) = character (χ z) * u x) :
    let I := F.squareFiltration.layerIdeal s
    let π := quotientHom (hnil := F.squareFiltration.lowerCentralSeries_eq_bot) I
    ∃! v : _ ⧸ (F.squareLattice Γ).map π → ℂ, ∀ g : F.squareFiltration.Group,
      v (QuotientGroup.mk (π g)) = F.squareObservable Γ ε u (QuotientGroup.mk g) := by
  dsimp only
  apply exists_unique_observable_reconstruction _ (quotientHom_surjective _)
    (F.squareLattice Γ) _ le_rfl (F.squareObservable Γ ε u)
  intro k hk x
  rw [quotientHom_ker] at hk
  exact F.squareObservable_top_invariant Γ ε u χ hu k hk (QuotientGroup.mk x)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open CircleFourier

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))

noncomputable def squareReductionHom : F.squareFiltration.Group →*
    F.squareFiltration.quotientTop.Group :=
  F.squareFiltration.quotientStepHom (F.squareFiltration.layerIdeal (s + 1)) le_rfl

theorem squareReductionHom_surjective : Function.Surjective F.squareReductionHom :=
  F.squareFiltration.quotientStepHom_surjective _ le_rfl

theorem squareReductionHom_ker : F.squareReductionHom.ker = F.squareFiltration.subgroup (s + 1) :=
  F.squareFiltration.quotientStepHom_ker _ le_rfl

noncomputable def reducedSquareOrbit {σ : Type*} {w : σ → ℕ}
    (q : F.squareFiltration.PolynomialOrbit w) : F.squareFiltration.quotientTop.PolynomialOrbit w :=
  F.squareFiltration.quotientPolynomialOrbit _ le_rfl q

theorem reducedSquareOrbit_eval {σ : Type*} {w : σ → ℕ}
    (q : F.squareFiltration.PolynomialOrbit w) (x : σ → ℤ) :
    F.squareFiltration.quotientTop.polynomialOrbitEval w x (F.reducedSquareOrbit q) =
      F.squareReductionHom (F.squareFiltration.polynomialOrbitEval w x q) :=
  F.squareFiltration.quotientPolynomialOrbit_eval _ le_rfl q x

theorem exists_reduced_square_observable (Γ : Subgroup F.Group) (ε : F.Group)
    (u : F.Group ⧸ Γ → ℂ) (χ : F.Group → CircleFourier.Circle)
    (hu : ∀ z ∈ F.subgroup (s + 1), ∀ x, u (z • x) = character (χ z) * u x) :
    ∃! v : F.squareFiltration.quotientTop.Group ⧸
      (F.squareLattice Γ).map F.squareReductionHom → ℂ,
      ∀ g : F.squareFiltration.Group, v (QuotientGroup.mk (F.squareReductionHom g)) =
        F.squareObservable Γ ε u (QuotientGroup.mk g) := by
  apply exists_unique_observable_reconstruction _ F.squareReductionHom_surjective
    (F.squareLattice Γ) _ le_rfl (F.squareObservable Γ ε u)
  intro k hk x
  rw [F.squareReductionHom_ker] at hk
  exact F.squareObservable_top_invariant Γ ε u χ hu k hk (QuotientGroup.mk x)

end Erdos3.NilpotentLieFiltration

end

end OAI

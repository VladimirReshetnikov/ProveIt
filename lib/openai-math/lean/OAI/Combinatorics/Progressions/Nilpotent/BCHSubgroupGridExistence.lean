import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import OAI.Combinatorics.Progressions.Estimates.RationalLieSubalgebra

namespace OAI

section

namespace Erdos3
variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
namespace NilpotentLieBCHGroup
variable {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

noncomputable def quotientHom (I : LieIdeal ℚ L) :
    NilpotentLieBCHGroup L s hnil →*
      NilpotentLieBCHGroup (L ⧸ I) s (lie_quotient_lowerCentralSeries_eq_bot hnil I) :=
  map (lieQuotientMap I)

@[simp] theorem quotientHom_coord (I : LieIdeal ℚ L) (a : NilpotentLieBCHGroup L s hnil) :
    (quotientHom I a).coord = lieQuotientMap I a.coord := rfl

theorem quotientHom_surjective (I : LieIdeal ℚ L) :
    Function.Surjective (quotientHom (hnil := hnil) I) := by
  intro b
  obtain ⟨a, ha⟩ := lieQuotientMap_surjective I b.coord
  exact ⟨⟨a⟩, ext ha⟩

theorem quotientHom_ker (I : LieIdeal ℚ L) :
    (quotientHom (hnil := hnil) I).ker = subgroup I.toLieSubalgebra := by
  ext a
  change quotientHom I a = 1 ↔ a.coord ∈ I
  constructor
  · intro h
    apply (lieQuotientMap_eq_zero I a.coord).mp
    exact congrArg coord h
  · intro h
    apply ext
    exact (lieQuotientMap_eq_zero I a.coord).mpr h

noncomputable def quotientEquiv (I : LieIdeal ℚ L) :
    NilpotentLieBCHGroup L s hnil ⧸ (quotientHom (hnil := hnil) I).ker ≃*
      NilpotentLieBCHGroup (L ⧸ I) s (lie_quotient_lowerCentralSeries_eq_bot hnil I) :=
  QuotientGroup.quotientKerEquivOfSurjective (quotientHom I) (quotientHom_surjective I)

@[simp] theorem quotientEquiv_mk (I : LieIdeal ℚ L) (a : NilpotentLieBCHGroup L s hnil) :
    quotientEquiv I (QuotientGroup.mk a) = quotientHom I a := rfl

theorem subgroup_ideal_normal (I : LieIdeal ℚ L) :
    (subgroup (hnil := hnil) I.toLieSubalgebra).Normal := by
  rw [← quotientHom_ker]
  infer_instance

theorem commute_of_lie_eq_zero (a b : NilpotentLieBCHGroup L s hnil)
    (hab : ⁅a.coord, b.coord⁆ = 0) : Commute a b := by
  apply ext
  change lieBCH s a.coord b.coord = lieBCH s b.coord a.coord
  have hba : ⁅b.coord, a.coord⁆ = 0 := by rw [← lie_skew, hab, neg_zero]
  rw [lieBCH_eq_add_of_lie_eq_zero hnil hab, lieBCH_eq_add_of_lie_eq_zero hnil hba, add_comm]

theorem commutator_mem_ideal (I : LieIdeal ℚ L) (a b : NilpotentLieBCHGroup L s hnil)
    (hab : ⁅a.coord, b.coord⁆ ∈ I) : (a * b * a⁻¹ * b⁻¹).coord ∈ I := by
  have hlie : ⁅(quotientHom I a).coord, (quotientHom I b).coord⁆ = 0 := by
    rw [quotientHom_coord, quotientHom_coord, ← LieHom.map_lie]
    exact (lieQuotientMap_eq_zero I _).mpr hab
  have hc := commute_of_lie_eq_zero (quotientHom I a) (quotientHom I b) hlie
  have h : quotientHom I (a * b * a⁻¹ * b⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [hc.eq]
    simp [mul_assoc]
  apply (lieQuotientMap_eq_zero I _).mp
  exact congrArg coord h

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)

include hnil

theorem lieBCH_sub_add_mem (I : LieIdeal ℚ L) (a b : L) (hab : ⁅a, b⁆ ∈ I) :
    lieBCH s a b - (a + b) ∈ I := by
  apply (lieQuotientMap_eq_zero I _).mp
  have hbracket : ⁅lieQuotientMap I a, lieQuotientMap I b⁆ = 0 := by
    rw [← LieHom.map_lie]
    exact (lieQuotientMap_eq_zero I _).mpr hab
  rw [map_sub, map_add, map_lieBCH,
    lieBCH_eq_add_of_lie_eq_zero (lie_quotient_lowerCentralSeries_eq_bot hnil I) hbracket, sub_self]

namespace NilpotentLieBCHGroup

theorem additive_remainder_mem (I : LieIdeal ℚ L) (r w : L) (hrw : ⁅r, w⁆ ∈ I) :
    (((⟨r⟩ : NilpotentLieBCHGroup L s hnil)⁻¹ * ⟨r + w⟩ * (⟨w⟩ : NilpotentLieBCHGroup L s hnil)⁻¹).coord) ∈ I := by
  have hsum : quotientHom I (⟨r + w⟩ : NilpotentLieBCHGroup L s hnil) =
      quotientHom I (⟨r⟩ : NilpotentLieBCHGroup L s hnil) * quotientHom I (⟨w⟩ : NilpotentLieBCHGroup L s hnil) := by
    apply ext
    change lieQuotientMap I (r + w) = lieBCH s (lieQuotientMap I r) (lieQuotientMap I w)
    rw [map_add]
    apply (lieBCH_eq_add_of_lie_eq_zero (lie_quotient_lowerCentralSeries_eq_bot hnil I) ?_).symm
    rw [← LieHom.map_lie]
    exact (lieQuotientMap_eq_zero I _).mpr hrw
  apply (lieQuotientMap_eq_zero I _).mp
  have h : quotientHom I
      ((⟨r⟩ : NilpotentLieBCHGroup L s hnil)⁻¹ * ⟨r + w⟩ * (⟨w⟩ : NilpotentLieBCHGroup L s hnil)⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, map_inv, hsum]
    simp only [inv_mul_cancel_left, mul_inv_cancel]
  exact congrArg coord h

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem coord_pow (g : NilpotentLieBCHGroup L s hnil) (n : ℕ) :
    (g ^ n).coord = n • g.coord := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, coord_mul, ih,
      lieBCH_eq_add_of_lie_eq_zero hnil (by simp [nsmul_lie]), succ_nsmul]

theorem coord_zpow (g : NilpotentLieBCHGroup L s hnil) (n : ℤ) :
    (g ^ n).coord = n • g.coord := by
  cases n with
  | ofNat n =>
    change (g ^ (n : ℤ)).coord = (n : ℤ) • g.coord
    simpa only [zpow_natCast, natCast_zsmul] using coord_pow g n
  | negSucc n =>
    simp only [zpow_negSucc, coord_inv, coord_pow, negSucc_zsmul]

theorem coord_pow_rat (g : NilpotentLieBCHGroup L s hnil) (n : ℕ) :
    (g ^ n).coord = (n : ℚ) • g.coord := by
  rw [coord_pow, Nat.cast_smul_eq_nsmul ℚ]

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3
variable (L : Type*) [LieRing L] [LieAlgebra ℚ L]

structure NilpotentLieFiltration (s : ℕ) where
  layer : ℕ → Submodule ℚ L
  antitone : Antitone layer
  one_eq_top : layer 1 = ⊤
  lie_mem : ∀ {i j : ℕ} {a b : L}, a ∈ layer i → b ∈ layer j → ⁅a, b⁆ ∈ layer (i + j)
  terminal : layer (s + 1) = ⊥

namespace NilpotentLieFiltration
variable {L} {s : ℕ} (F : NilpotentLieFiltration L s)
include F

def layerIdeal (i : ℕ) : LieIdeal ℚ L :=
  { F.layer i with
    lie_mem := by
      intro x y hy
      have hx : x ∈ F.layer 1 := by simp [F.one_eq_top]
      exact F.antitone (Nat.le_add_left i 1) (F.lie_mem hx hy) }

@[simp] theorem mem_layerIdeal (i : ℕ) (a : L) : a ∈ F.layerIdeal i ↔ a ∈ F.layer i := Iff.rfl

theorem lowerCentralSeries_le (n : ℕ) :
    LieModule.lowerCentralSeries ℚ L L n ≤ F.layerIdeal (n + 1) := by
  induction n with
  | zero =>
    intro a _
    change a ∈ F.layer 1
    simp [F.one_eq_top]
  | succ n ih =>
    rw [LieModule.lowerCentralSeries_succ, LieSubmodule.lie_le_iff]
    intro a _ b hb
    have ha : a ∈ F.layer 1 := by simp [F.one_eq_top]
    have h := F.lie_mem ha (ih hb)
    change ⁅a, b⁆ ∈ F.layer (n + 1 + 1)
    simpa only [Nat.add_comm 1 (n + 1)] using h

theorem lowerCentralSeries_eq_bot : LieModule.lowerCentralSeries ℚ L L s = ⊥ := by
  apply bot_unique
  intro a ha
  have h := F.lowerCentralSeries_le s ha
  change a ∈ F.layer (s + 1) at h
  change a = 0
  simpa only [F.terminal, Submodule.mem_bot] using h

abbrev Group := NilpotentLieBCHGroup L s F.lowerCentralSeries_eq_bot

theorem bch_mem {i : ℕ} {a b : L} (ha : a ∈ F.layer i) (hb : b ∈ F.layer i) :
    lieBCH s a b ∈ F.layer i :=
  lieBCH_mem (F.layerIdeal i).toLieSubalgebra s ha hb

def subgroup (i : ℕ) : Subgroup F.Group :=
  NilpotentLieBCHGroup.subgroup (F.layerIdeal i).toLieSubalgebra

@[simp] theorem mem_subgroup (i : ℕ) (a : F.Group) : a ∈ F.subgroup i ↔ a.coord ∈ F.layer i := Iff.rfl

theorem subgroup_normal (i : ℕ) : (F.subgroup i).Normal :=
  NilpotentLieBCHGroup.subgroup_ideal_normal (F.layerIdeal i)

theorem commutator_mem {i j : ℕ} {a b : F.Group}
    (ha : a.coord ∈ F.layer i) (hb : b.coord ∈ F.layer j) :
    (a * b * a⁻¹ * b⁻¹).coord ∈ F.layer (i + j) :=
  NilpotentLieBCHGroup.commutator_mem_ideal (F.layerIdeal (i + j)) a b (F.lie_mem ha hb)

theorem subgroup_one : F.subgroup 1 = ⊤ := by
  apply top_unique
  intro a _
  change a.coord ∈ F.layer 1
  simp [F.one_eq_top]

theorem subgroup_terminal : F.subgroup (s + 1) = ⊥ := by
  apply bot_unique
  intro a ha
  rw [Subgroup.mem_bot]
  apply NilpotentLieBCHGroup.ext
  change a.coord = 0
  change a.coord ∈ F.layer (s + 1) at ha
  simpa only [F.terminal, Submodule.mem_bot] using ha

theorem descendingCentralSeries :
    Subgroup.IsDescendingCentralSeries (fun n => F.subgroup (n + 1)) := by
  refine ⟨F.subgroup_one, ?_⟩
  intro a n ha b
  change (a * b * a⁻¹ * b⁻¹).coord ∈ F.layer (n + 1 + 1)
  have hb : b.coord ∈ F.layer 1 := by simp [F.one_eq_top]
  exact F.commutator_mem ha hb

theorem group_lowerCentralSeries_eq_bot : (⊤ : Subgroup F.Group).lowerCentralSeries s = ⊥ := by
  apply bot_unique
  exact (Subgroup.descending_central_series_ge_lower _ F.descendingCentralSeries s).trans
    F.subgroup_terminal.le

theorem isNilpotentGroup : _root_.Group.IsNilpotent F.Group :=
  Subgroup.nilpotent_iff_lowerCentralSeries.mpr ⟨s, F.group_lowerCentralSeries_eq_bot⟩

theorem nilpotencyClass_le : _root_.Group.nilpotencyClass F.Group ≤ s := by
  have := F.isNilpotentGroup
  exact Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp F.group_lowerCentralSeries_eq_bot

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥}

def bchSubgroupCoordinates (e : Basis ι ℚ L) (Γ : Subgroup (NilpotentLieBCHGroup L s hL)) :
    Set (ι → ℚ) := {x | (⟨e.equivFun.symm x⟩ : NilpotentLieBCHGroup L s hL) ∈ Γ}

variable [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq ι] in

theorem bchSubgroupCoordinates_comap (b : Basis κ ℚ M) (e : Basis ι ℚ L)
    (φ : M →ₗ⁅ℚ⁆ L) (Γ : Subgroup (NilpotentLieBCHGroup L s hL)) :
    bchSubgroupCoordinates b (Γ.comap (NilpotentLieBCHGroup.map (hnil := hM) φ)) =
      (LinearMap.toMatrix b e φ.toLinearMap).mulVec ⁻¹' bchSubgroupCoordinates e Γ := by
  ext x
  change ((⟨φ (b.equivFun.symm x)⟩ : NilpotentLieBCHGroup L s hL) ∈ Γ) ↔
    ((⟨e.equivFun.symm (LinearMap.toMatrix b e φ.toLinearMap *ᵥ x)⟩ :
      NilpotentLieBCHGroup L s hL) ∈ Γ)
  rw [basisMatrix_mulVec, LinearEquiv.symm_apply_apply]
  rfl

omit [DecidableEq κ] in

theorem bchSubgroupCoordinates_map (e : Basis ι ℚ L) (b : Basis κ ℚ M)
    (φ : L →ₗ⁅ℚ⁆ M) (Γ : Subgroup (NilpotentLieBCHGroup L s hL)) :
    bchSubgroupCoordinates b (Γ.map (NilpotentLieBCHGroup.map (hM := hM) φ)) =
      (LinearMap.toMatrix e b φ.toLinearMap).mulVec '' bchSubgroupCoordinates e Γ := by
  ext y
  constructor
  · intro hy
    obtain ⟨g, hg, heq⟩ := Subgroup.mem_map.mp hy
    refine ⟨e.equivFun g.coord, ?_, ?_⟩
    · change (⟨e.equivFun.symm (e.equivFun g.coord)⟩ : NilpotentLieBCHGroup L s hL) ∈ Γ
      simpa only [LinearEquiv.symm_apply_apply] using hg
    · rw [basisMatrix_mulVec, LinearEquiv.symm_apply_apply]
      have h := congrArg NilpotentLieBCHGroup.coord heq
      change φ g.coord = b.equivFun.symm y at h
      change b.equivFun (φ g.coord) = y
      rw [h, LinearEquiv.apply_symm_apply]
  · rintro ⟨x, hx, hxy⟩
    apply Subgroup.mem_map.mpr
    refine ⟨⟨e.equivFun.symm x⟩, hx, ?_⟩
    apply NilpotentLieBCHGroup.ext
    change φ (e.equivFun.symm x) = b.equivFun.symm y
    apply b.equivFun.injective
    rw [LinearEquiv.apply_symm_apply]
    change b.equivFun (φ.toLinearMap (e.equivFun.symm x)) = y
    simpa only [basisMatrix_mulVec] using hxy

theorem exists_bchSubgroup_comap_grid_exp_bound (b : Basis κ ℚ M) (e : Basis ι ℚ L)
    (φ : M →ₗ⁅ℚ⁆ L) (hφ : Function.Injective φ)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hL)) {H l : ℕ} (hHpos : 1 ≤ H) (hlpos : 0 < l)
    (hB : ∀ i j, RationalHeightLE (LinearMap.toMatrix b e φ.toLinearMap i j) H)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
    {p : ℝ} (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p) (hr : (Fintype.card κ : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) (hl : (l : ℝ) ≤ Real.exp p) :
    ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ Real.exp ((p + 2) ^ 9) ∧
      scaledIntegerGrid N ⊆ bchSubgroupCoordinates b
        (Γ.comap (NilpotentLieBCHGroup.map (hnil := hM) φ)) ∧
      bchSubgroupCoordinates b (Γ.comap (NilpotentLieBCHGroup.map (hnil := hM) φ)) ⊆ denominatorGrid N := by
  rw [bchSubgroupCoordinates_comap b e φ Γ]
  exact exists_preimage_grid_exp_bound (LinearMap.toMatrix b e φ.toLinearMap)
    (Matrix.mulVec_injective_iff.mp (basisMatrix_injective b e φ.toLinearMap hφ))
    hHpos hlpos hB _ hinner houter hp hd hr hH hl

theorem exists_bchSubgroup_map_grid_exp_bound (e : Basis ι ℚ L) (b : Basis κ ℚ M)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : Function.Surjective φ)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hL)) {H l : ℕ} (hHpos : 1 ≤ H) (hlpos : 0 < l)
    (hD : ∀ i j, RationalHeightLE (LinearMap.toMatrix e b φ.toLinearMap i j) H)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
    {p : ℝ} (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p) (hr : (Fintype.card κ : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) (hl : (l : ℝ) ≤ Real.exp p) :
    ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ Real.exp ((p + 2) ^ 9) ∧
      scaledIntegerGrid N ⊆ bchSubgroupCoordinates b
        (Γ.map (NilpotentLieBCHGroup.map (hM := hM) φ)) ∧
      bchSubgroupCoordinates b (Γ.map (NilpotentLieBCHGroup.map (hM := hM) φ)) ⊆ denominatorGrid N := by
  rw [bchSubgroupCoordinates_map e b φ Γ]
  exact exists_image_grid_exp_bound (LinearMap.toMatrix e b φ.toLinearMap)
    (basisMatrix_surjective e b φ.toLinearMap hφ) hHpos hlpos hD _ hinner houter hp hd hr hH hl

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup
variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
variable {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem descendingCentralSeries : Subgroup.IsDescendingCentralSeries
    (fun n => subgroup (hnil := hnil)
      ((LieModule.lowerCentralSeries ℚ L L n : LieIdeal ℚ L) : LieSubalgebra ℚ L)) := by
  constructor
  · apply top_unique
    intro a _
    change a.coord ∈ LieModule.lowerCentralSeries ℚ L L 0
    simp
  · intro a n ha b
    change (a * b * a⁻¹ * b⁻¹).coord ∈ LieModule.lowerCentralSeries ℚ L L (n + 1)
    apply commutator_mem_ideal
    rw [← lie_skew a.coord b.coord]
    apply (LieModule.lowerCentralSeries ℚ L L (n + 1)).neg_mem
    rw [LieModule.lowerCentralSeries_succ]
    exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top b.coord) ha

theorem lowerCentralSeries_eq_bot :
    (⊤ : Subgroup (NilpotentLieBCHGroup L s hnil)).lowerCentralSeries s = ⊥ := by
  apply bot_unique
  apply (Subgroup.descending_central_series_ge_lower _ (descendingCentralSeries (hnil := hnil)) s).trans
  intro a ha
  rw [Subgroup.mem_bot]
  apply ext
  change a.coord = 0
  change a.coord ∈ LieModule.lowerCentralSeries ℚ L L s at ha
  simpa only [hnil, LieSubmodule.mem_bot] using ha

theorem isNilpotentGroup : _root_.Group.IsNilpotent (NilpotentLieBCHGroup L s hnil) :=
  Subgroup.nilpotent_iff_lowerCentralSeries.mpr ⟨s, lowerCentralSeries_eq_bot⟩

theorem nilpotencyClass_le : _root_.Group.nilpotencyClass (NilpotentLieBCHGroup L s hnil) ≤ s := by
  have := isNilpotentGroup (hnil := hnil)
  exact Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp lowerCentralSeries_eq_bot

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

noncomputable def conjugationCoord (g : NilpotentLieBCHGroup L s hnil) (x : L) : L :=
  (g * (⟨x⟩ : NilpotentLieBCHGroup L s hnil) * g⁻¹).coord

theorem conjugationCoord_nsmul (g : NilpotentLieBCHGroup L s hnil) (n : ℕ) (x : L) :
    conjugationCoord g (n • x) = n • conjugationCoord g x := by
  have he : (⟨n • x⟩ : NilpotentLieBCHGroup L s hnil) =
      (⟨x⟩ : NilpotentLieBCHGroup L s hnil) ^ n := by
    apply ext
    exact (coord_pow _ _).symm
  change ((MulAut.conj g) (⟨n • x⟩ : NilpotentLieBCHGroup L s hnil)).coord = _
  rw [he, map_pow, coord_pow]
  rfl

theorem conjugationCoord_zsmul (g : NilpotentLieBCHGroup L s hnil) (n : ℤ) (x : L) :
    conjugationCoord g (n • x) = n • conjugationCoord g x := by
  have he : (⟨n • x⟩ : NilpotentLieBCHGroup L s hnil) =
      (⟨x⟩ : NilpotentLieBCHGroup L s hnil) ^ n := by
    apply ext
    exact (coord_zpow _ _).symm
  change ((MulAut.conj g) (⟨n • x⟩ : NilpotentLieBCHGroup L s hnil)).coord = _
  rw [he, map_zpow, coord_zpow]
  rfl

theorem conjugationCoord_rat_smul (g : NilpotentLieBCHGroup L s hnil) (q : ℚ) (x : L) :
    conjugationCoord g (q • x) = q • conjugationCoord g x := by
  have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hq : (q.den : ℚ) * q = (q.num : ℚ) := by
    calc
      _ = (q.den : ℚ) * ((q.num : ℚ) / q.den) :=
        congrArg ((q.den : ℚ) * ·) (Rat.num_div_den q).symm
      _ = _ := by field_simp
  apply smul_right_injective L hd
  dsimp only
  calc
    _ = conjugationCoord g ((q.den : ℚ) • (q • x)) := by
      simpa only [Nat.cast_smul_eq_nsmul] using (conjugationCoord_nsmul g q.den (q • x)).symm
    _ = conjugationCoord g ((q.num : ℚ) • x) := by rw [smul_smul, hq]
    _ = (q.num : ℚ) • conjugationCoord g x := by
      simpa only [Int.cast_smul_eq_zsmul] using conjugationCoord_zsmul g q.num x
    _ = _ := by rw [smul_smul, hq]

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem quotient_bch_eq_add {i : ℕ} (hi : 1 ≤ i) {a b : L}
    (ha : a ∈ F.layer i) (hb : b ∈ F.layer i) :
    lieQuotientMap (F.layerIdeal (i + 1)) (lieBCH s a b) =
      lieQuotientMap (F.layerIdeal (i + 1)) (a + b) := by
  rw [map_lieBCH, map_add]
  apply lieBCH_eq_add_of_lie_eq_zero
    (lie_quotient_lowerCentralSeries_eq_bot F.lowerCentralSeries_eq_bot (F.layerIdeal (i + 1)))
  rw [← LieHom.map_lie]
  exact (lieQuotientMap_eq_zero _ _).mpr (F.antitone (by omega) (F.lie_mem ha hb))

theorem quotient_prod_eq_sum {i : ℕ} (hi : 1 ≤ i) (xs : List L)
    (hx : ∀ a ∈ xs, a ∈ F.layer i) :
    NilpotentLieBCHGroup.quotientHom (F.layerIdeal (i + 1))
        (xs.map (fun a => (⟨a⟩ : F.Group))).prod =
      NilpotentLieBCHGroup.quotientHom (F.layerIdeal (i + 1)) (⟨xs.sum⟩ : F.Group) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    have ha := hx a (List.mem_cons_self ..)
    have hxs : ∀ b ∈ xs, b ∈ F.layer i := fun b hb => hx b (List.mem_cons_of_mem a hb)
    simp only [List.map_cons, List.prod_cons, map_mul, List.sum_cons]
    rw [ih hxs]
    apply NilpotentLieBCHGroup.ext
    change lieBCH s (lieQuotientMap (F.layerIdeal (i + 1)) a)
      (lieQuotientMap (F.layerIdeal (i + 1)) xs.sum) =
      lieQuotientMap (F.layerIdeal (i + 1)) (a + xs.sum)
    rw [← map_lieBCH]
    exact F.quotient_bch_eq_add hi ha (list_sum_mem hxs)

theorem exists_product_of_layerwise_sum (S : Set L)
    (hS : ∀ i, 1 ≤ i → ∀ a ∈ F.layer i,
      ∃ xs : List L, (∀ b ∈ xs, b ∈ S ∧ b ∈ F.layer i) ∧ xs.sum = a)
    (a : L) :
    ∃ xs : List L, (∀ b ∈ xs, b ∈ S) ∧ (xs.map (fun b => (⟨b⟩ : F.Group))).prod = ⟨a⟩ := by
  have aux : ∀ k i : ℕ, i + k = s + 1 → 1 ≤ i → ∀ a ∈ F.layer i,
      ∃ xs : List L, (∀ b ∈ xs, b ∈ S) ∧ (xs.map (fun b => (⟨b⟩ : F.Group))).prod = ⟨a⟩ := by
    intro k
    induction k with
    | zero =>
      intro i hi _ a ha
      have hieq : i = s + 1 := by omega
      have haz : a = 0 := by simpa only [hieq, F.terminal, Submodule.mem_bot] using ha
      refine ⟨[], by simp, ?_⟩
      simp only [List.map_nil, List.prod_nil, haz]
      rfl
    | succ k ih =>
      intro i hi hipos a ha
      obtain ⟨ys, hys, hsum⟩ := hS i hipos a ha
      let g : F.Group := (ys.map (fun b => (⟨b⟩ : F.Group))).prod
      let r : F.Group := g⁻¹ * ⟨a⟩
      have hquot : NilpotentLieBCHGroup.quotientHom (F.layerIdeal (i + 1)) g =
          NilpotentLieBCHGroup.quotientHom (F.layerIdeal (i + 1)) (⟨a⟩ : F.Group) := by
        simpa only [g, hsum] using F.quotient_prod_eq_sum hipos ys (fun b hb => (hys b hb).2)
      have hr : r.coord ∈ F.layer (i + 1) := by
        have hzero : NilpotentLieBCHGroup.quotientHom (F.layerIdeal (i + 1)) r = 1 := by
          simp only [r, map_mul, map_inv, hquot, inv_mul_cancel]
        have hc := congrArg NilpotentLieBCHGroup.coord hzero
        exact (lieQuotientMap_eq_zero _ _).mp hc
      obtain ⟨zs, hzs, hprod⟩ := ih (i + 1) (by omega) (by omega) r.coord hr
      refine ⟨ys ++ zs, ?_, ?_⟩
      · intro b hb
        rcases List.mem_append.mp hb with hb | hb
        · exact (hys b hb).1
        · exact hzs b hb
      · rw [List.map_append, List.prod_append, hprod]
        change g * r = ⟨a⟩
        simp only [r, mul_inv_cancel_left]
  exact aux s 1 (by omega) (by omega) a (by simp [F.one_eq_top])

theorem exists_product_of_layerwise_range {J : Type*} (f : J → L)
    (hf : ∀ i, 1 ≤ i → ∀ a ∈ F.layer i,
      ∃ xs : List L, (∀ b ∈ xs, b ∈ Set.range f ∧ b ∈ F.layer i) ∧ xs.sum = a)
    (a : L) :
    ∃ xs : List J, (xs.map (fun j => (⟨f j⟩ : F.Group))).prod = ⟨a⟩ := by
  classical
  obtain ⟨ys, hys, hprod⟩ := F.exists_product_of_layerwise_sum (Set.range f) hf a
  choose c hc using fun y : {y : L // y ∈ ys} => hys y.val y.property
  let xs := ys.attach.map c
  have hmap : xs.map f = ys := by
    dsimp only [xs]
    rw [List.map_map]
    have hfc : f ∘ c = Subtype.val := funext hc
    rw [hfc]
    exact List.attach_map_subtype_val ys
  refine ⟨xs, ?_⟩
  have h := congrArg (fun zs : List L => (zs.map (fun b => (⟨b⟩ : F.Group))).prod) hmap
  simpa only [List.map_map, Function.comp_def] using h.trans hprod

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module

theorem exists_bchSubgroup_comap_grid
    {ι κ L M : Type*} [Fintype ι] [Fintype κ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
    {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥}
    (b : Basis κ ℚ M) (e : Basis ι ℚ L) (φ : M →ₗ⁅ℚ⁆ L) (hφ : Function.Injective φ)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hL)) (l : ℕ) (hl : 0 < l)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l) :
    ∃ N : ℕ, 0 < N ∧
      scaledIntegerGrid N ⊆ bchSubgroupCoordinates b (Γ.comap (NilpotentLieBCHGroup.map (hnil := hM) φ)) ∧
      bchSubgroupCoordinates b (Γ.comap (NilpotentLieBCHGroup.map (hnil := hM) φ)) ⊆ denominatorGrid N := by
  classical
  obtain ⟨σ, hσ⟩ := φ.toLinearMap.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hφ)
  let B := LinearMap.toMatrix b e φ.toLinearMap
  let C := LinearMap.toMatrix e b σ
  have hCB : C * B = 1 := by
    change LinearMap.toMatrix e b σ * LinearMap.toMatrix b e φ.toLinearMap = 1
    rw [← LinearMap.toMatrix_comp]
    rw [hσ]
    exact LinearMap.toMatrix_id b
  rw [bchSubgroupCoordinates_comap b e φ Γ]
  exact ⟨l * (matrixDenominator B * matrixDenominator C),
    Nat.mul_pos hl (Nat.mul_pos (matrixDenominator_pos B) (matrixDenominator_pos C)),
    rational_preimage_grid_transport B C hCB l _ hinner houter⟩

end Erdos3

end

end OAI

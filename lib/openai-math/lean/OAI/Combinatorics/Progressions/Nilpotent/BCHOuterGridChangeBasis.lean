import OAI.Combinatorics.Progressions.Estimates.PowerSubgroup
import OAI.Combinatorics.Progressions.Nilpotent.BCHSubgroupGridExistence
import OAI.Combinatorics.Progressions.Sampling.IntegralGridFunctional

namespace OAI

section

namespace Erdos3

variable {X L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem rational_nat_smul_mem (M : Submodule ℤ L) {z : L} (hz : z ∈ M) (D : ℕ) :
    (D : ℚ) • z ∈ M := by
  rw [Nat.cast_smul_eq_nsmul ℚ]
  exact M.nsmul_mem hz D

theorem rightBracketList_mem_intModule (M : Submodule ℤ L)
    (hbr : ∀ a ∈ M, ∀ b ∈ M, ⁅a, b⁆ ∈ M)
    (f : X → L) (hf : ∀ x, f x ∈ M) (xs : List X) {z : L} (hz : z ∈ M) :
    rightBracketList f xs z ∈ M := by
  induction xs generalizing z with
  | nil => exact hz
  | cons x xs ih => exact ih (hbr z hz (f x) (hf x))

theorem dynkinWord_mem_multiple (M : Submodule ℤ L) (D : ℕ)
    (hbr : ∀ a ∈ M, ∀ b ∈ M, ∃ z ∈ M, ⁅a, b⁆ = (D : ℚ) • z)
    (f : X → L) (hf : ∀ x, f x ∈ M) (w : FreeSemigroup X) (hw : w.tail ≠ []) :
    ∃ z ∈ M, dynkinWord f w = (D : ℚ) • z := by
  have hclosed : ∀ a ∈ M, ∀ b ∈ M, ⁅a, b⁆ ∈ M := by
    intro a ha b hb
    obtain ⟨z, hz, heq⟩ := hbr a ha b hb
    rw [heq]
    exact rational_nat_smul_mem M hz D
  cases htail : w.tail with
  | nil => exact False.elim (hw htail)
  | cons x xs =>
      obtain ⟨z, hz, heq⟩ := hbr (f w.head) (hf _) (f x) (hf _)
      refine ⟨rightBracketList f xs z, rightBracketList_mem_intModule M hclosed f hf xs hz, ?_⟩
      simp only [dynkinWord, htail, rightBracketList_cons, Module.End.mul_apply,
        rightBracket_apply, heq, map_smul]

theorem lieBCH_mem_of_divisible_brackets (M : Submodule ℤ L) (D : ℕ) {s : ℕ}
    (hs : 1 ≤ s)
    (hbr : ∀ a ∈ M, ∀ b ∈ M, ∃ z ∈ M, ⁅a, b⁆ = (D : ℚ) • z)
    (hc : ∀ w ∈ bchBracketSupport s, ∃ n : ℤ, (D : ℚ) * bchBracketCoefficient s w = (n : ℚ))
    {a b : L} (ha : a ∈ M) (hb : b ∈ M) : lieBCH s a b ∈ M := by
  classical
  rw [lieBCH_eq_add_nonlinear_sum hs]
  apply M.add_mem (M.add_mem ha hb)
  apply M.sum_mem
  intro w hw
  obtain ⟨hw, htail⟩ := Finset.mem_filter.mp hw
  have hf : ∀ i : Fin 2, ![a, b] i ∈ M := by
    intro i
    fin_cases i <;> assumption
  obtain ⟨z, hz, heq⟩ := dynkinWord_mem_multiple M D hbr ![a, b] hf w htail
  obtain ⟨n, hn⟩ := hc w hw
  rw [heq, smul_smul, mul_comm _ (D : ℚ), hn, Int.cast_smul_eq_zsmul ℚ]
  exact M.smul_mem n hz

theorem lieBCH_mem_of_divisible_brackets_nilpotent (M : Submodule ℤ L) (D : ℕ) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (hbr : ∀ a ∈ M, ∀ b ∈ M, ∃ z ∈ M, ⁅a, b⁆ = (D : ℚ) • z)
    (hc : ∀ w ∈ bchBracketSupport s, ∃ n : ℤ, (D : ℚ) * bchBracketCoefficient s w = (n : ℚ))
    {a b : L} (ha : a ∈ M) (hb : b ∈ M) : lieBCH s a b ∈ M := by
  by_cases hs : 1 ≤ s
  · exact lieBCH_mem_of_divisible_brackets M D hs hbr hc ha hb
  · have hs0 : s = 0 := by omega
    subst s
    have hz : a = 0 := by
      have h : a ∈ LieModule.lowerCentralSeries ℚ L L 0 := by simp
      simpa only [hnil, LieSubmodule.mem_bot] using h
    rw [hz, lieBCH_zero_left hnil]
    exact hb

def intModuleBCHSubgroup (M : Submodule ℤ L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (hstable : ∀ a ∈ M, ∀ b ∈ M, lieBCH s a b ∈ M) :
    Subgroup (NilpotentLieBCHGroup L s hnil) where
  carrier := {g | g.coord ∈ M}
  one_mem' := M.zero_mem
  mul_mem' := by intro a b ha hb; exact hstable a.coord ha b.coord hb
  inv_mem' := by intro a ha; exact M.neg_mem ha

end Erdos3

end

section

namespace Erdos3

open Module

theorem denominator_grid_smul_mem_scaled {ι : Type*} (l m₀ m : ℕ)
    (hm : l * m₀ ∣ m) {x : ι → ℚ} (hx : x ∈ denominatorGrid l) :
    (m : ℚ) • x ∈ scaledIntegerGrid m₀ := by
  obtain ⟨k, rfl⟩ := hm
  obtain ⟨z, hz⟩ := hx
  refine ⟨fun i => (k : ℤ) * z i, ?_⟩
  ext i
  have hi := hz i
  change (l : ℚ) * x i = (z i : ℚ) at hi
  simp only [Pi.smul_apply, smul_eq_mul, Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
  calc
    _ = (m₀ : ℚ) * k * ((l : ℚ) * x i) := by ring
    _ = _ := by rw [hi]; ring

theorem denominator_grid_subset_mul {ι : Type*} (l m : ℕ) :
    (denominatorGrid l : Set (ι → ℚ)) ⊆ denominatorGrid (m * l) := by
  intro x hx
  have h := hx.nat_smul m
  simpa only [denominatorGrid, Set.mem_ofPred_eq, smul_smul, Nat.cast_mul] using h

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem bchSubgroupCoordinates_repr (e : Basis ι ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (g : NilpotentLieBCHGroup L s hnil) :
    e.equivFun g.coord ∈ bchSubgroupCoordinates e Γ ↔ g ∈ Γ := by
  change (⟨e.equivFun.symm (e.equivFun g.coord)⟩ : NilpotentLieBCHGroup L s hnil) ∈ Γ ↔ _
  rw [LinearEquiv.symm_apply_apply]

theorem subgroupPowerCover_inner_grid (e : Basis ι ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l m : ℕ)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ) :
    scaledIntegerGrid (m * l) ⊆ bchSubgroupCoordinates e (subgroupPowerCover Γ m) := by
  rintro x ⟨z, rfl⟩
  let g : NilpotentLieBCHGroup L s hnil := ⟨e.equivFun.symm ((l : ℚ) • fun i => (z i : ℚ))⟩
  have hg : g ∈ Γ := hinner ⟨z, rfl⟩
  have heq : e.equivFun (g ^ m).coord = ((m * l : ℕ) : ℚ) • fun i => (z i : ℚ) := by
    rw [NilpotentLieBCHGroup.coord_pow_rat, map_smul]
    change (m : ℚ) • e.equivFun (e.equivFun.symm ((l : ℚ) • fun i => (z i : ℚ))) = _
    rw [LinearEquiv.apply_symm_apply, smul_smul, Nat.cast_mul]
  rw [← heq]
  exact (bchSubgroupCoordinates_repr e _ _).mpr (pow_mem_subgroupPowerCover Γ hg m)

theorem subgroupPowerCover_le_of_grid (e : Basis ι ℚ L)
    (Γ Λ₀ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l m₀ m : ℕ)
    (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
    (hinner : scaledIntegerGrid m₀ ⊆ bchSubgroupCoordinates e Λ₀)
    (hm : l * m₀ ∣ m) : subgroupPowerCover Γ m ≤ Λ₀ := by
  apply (subgroupPowerCover_le_iff Γ Λ₀ m).mpr
  intro g hg
  apply (bchSubgroupCoordinates_repr e Λ₀ (g ^ m)).mp
  rw [NilpotentLieBCHGroup.coord_pow_rat, map_smul]
  exact hinner (denominator_grid_smul_mem_scaled l m₀ m hm
    (houter ((bchSubgroupCoordinates_repr e Γ g).mpr hg)))

theorem subgroupPowerCover_grid (e : Basis ι ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l m : ℕ)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l) :
    scaledIntegerGrid (m * l) ⊆ bchSubgroupCoordinates e (subgroupPowerCover Γ m) ∧
      bchSubgroupCoordinates e (subgroupPowerCover Γ m) ⊆ denominatorGrid (m * l) := by
  refine ⟨subgroupPowerCover_inner_grid e Γ l m hinner, ?_⟩
  intro x hx
  exact denominator_grid_subset_mul l m (houter (subgroupPowerCover_le Γ m hx))

end Erdos3

end

section

namespace Erdos3

open Module

noncomputable def bchIntegralDenominatorBound (s : ℕ) : ℕ :=
  bchCoefficientHeight s ^ (bchBracketSupport s).card

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

theorem exists_bch_stable_integral_grid (e : Basis ι ℚ L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) (l : ℕ) (hl : 0 < l) {H : ℕ}
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) :
    ∃ B : ℕ, 0 < B ∧ l ∣ B ∧
      B ≤ bchIntegralDenominatorBound s * H ^ (Fintype.card ι ^ 3) * l ∧
      ∀ a ∈ coordinateGridModule e B, ∀ b ∈ coordinateGridModule e B,
        lieBCH s a b ∈ coordinateGridModule e B := by
  classical
  obtain ⟨D, hD, hDb, u, hu, _⟩ := exists_bch_integer_coefficients s
  obtain ⟨E, hE, hEb, c, hEcoeff, _⟩ := exists_bounded_integer_array
    (fun ijk : ι × (ι × ι) => lieStructureConstants e ijk.1 ijk.2.1 ijk.2.2)
    (fun ijk => hc ijk.1 ijk.2.1 ijk.2.2)
  have hEb' : E ≤ H ^ (Fintype.card ι ^ 3) := by
    simpa only [Fintype.card_prod, pow_succ, pow_zero, one_mul, mul_assoc] using hEb
  let B := (D * E) * l
  have hscaled (i j k : ι) :
      ∃ n : ℤ, (B : ℚ) * lieStructureConstants e i j k = (D : ℚ) * n := by
    refine ⟨(l : ℤ) * c (i, j, k), ?_⟩
    simp only [B, Nat.cast_mul, Int.cast_mul, Int.cast_natCast, hEcoeff]
    ring
  refine ⟨B, Nat.mul_pos (Nat.mul_pos hD hE) hl, dvd_mul_left l (D * E),
    Nat.mul_le_mul_right l (Nat.mul_le_mul hDb hEb'), ?_⟩
  intro a ha b hb
  exact lieBCH_mem_of_divisible_brackets_nilpotent (coordinateGridModule e B) D hnil
    (fun x hx y hy => coordinateGrid_bracket_divisible e B D hscaled hx hy)
    (fun w hw => ⟨u w hw, (hu w hw).symm⟩) ha hb

def coordinateGridBCHSubgroup (e : Basis ι ℚ L) (B : ℕ) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (hstable : ∀ a ∈ coordinateGridModule e B, ∀ b ∈ coordinateGridModule e B,
      lieBCH s a b ∈ coordinateGridModule e B) :
    Subgroup (NilpotentLieBCHGroup L s hnil) :=
  intModuleBCHSubgroup (coordinateGridModule e B) hnil hstable

theorem coordinateGridBCHSubgroup_coordinates (e : Basis ι ℚ L) (B : ℕ) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (hstable : ∀ a ∈ coordinateGridModule e B, ∀ b ∈ coordinateGridModule e B,
      lieBCH s a b ∈ coordinateGridModule e B) :
    bchSubgroupCoordinates e (coordinateGridBCHSubgroup e B hnil hstable) = scaledIntegerGrid B := by
  ext x
  change e.equivFun (e.equivFun.symm x) ∈ scaledIntegerGrid B ↔ x ∈ scaledIntegerGrid B
  rw [LinearEquiv.apply_symm_apply]

theorem exists_integral_grid_subgroup (e : Basis ι ℚ L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l) {H : ℕ}
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ) :
    ∃ (B : ℕ) (Λ : Subgroup (NilpotentLieBCHGroup L s hnil)),
      0 < B ∧ l ∣ B ∧ B ≤ bchIntegralDenominatorBound s * H ^ (Fintype.card ι ^ 3) * l ∧
      Λ ≤ Γ ∧ bchSubgroupCoordinates e Λ = scaledIntegerGrid B := by
  obtain ⟨B, hB, hdiv, hbound, hstable⟩ := exists_bch_stable_integral_grid e hnil l hl hc
  let Λ := coordinateGridBCHSubgroup e B hnil hstable
  have hcoords := coordinateGridBCHSubgroup_coordinates e B hnil hstable
  refine ⟨B, Λ, hB, hdiv, hbound, ?_, hcoords⟩
  intro g hg
  apply (bchSubgroupCoordinates_repr e Γ g).mp
  apply hinner
  apply scaledIntegerGrid_subset_of_dvd hdiv
  rw [← hcoords]
  exact (bchSubgroupCoordinates_repr e Λ g).mpr hg

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

theorem exists_bchSubgroup_outer_grid_change_basis
    {ι κ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
    (e : Basis ι ℚ L) (b : Basis κ ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l) :
    ∃ N : ℕ, 0 < N ∧ bchSubgroupCoordinates b Γ ⊆ denominatorGrid N := by
  classical
  let A := LinearMap.toMatrix e b (LinearMap.id : L →ₗ[ℚ] L)
  refine ⟨matrixDenominator A * l, Nat.mul_pos (matrixDenominator_pos A) hl, ?_⟩
  intro x hx
  let g : NilpotentLieBCHGroup L s hnil := ⟨b.equivFun.symm x⟩
  have hg : g ∈ Γ := hx
  have hgrid := houter ((bchSubgroupCoordinates_repr e Γ g).mpr hg)
  have hint := integralVector_denominator_mulVec A ((l : ℚ) • e.equivFun g.coord) hgrid
  have hA : A *ᵥ e.equivFun g.coord = x := by
    dsimp only [A]
    rw [basisMatrix_mulVec, LinearEquiv.symm_apply_apply]
    exact b.equivFun.apply_symm_apply x
  simpa only [denominatorGrid, Set.mem_ofPred_eq, Matrix.mulVec_smul, hA,
    smul_smul, Nat.cast_mul] using hint

end Erdos3

end

end OAI

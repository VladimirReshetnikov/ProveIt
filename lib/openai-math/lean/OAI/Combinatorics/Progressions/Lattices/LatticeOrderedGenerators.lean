import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import OAI.Combinatorics.Progressions.Estimates.PowerIndexFromOrderedGenerators
import OAI.Combinatorics.Progressions.Nilpotent.BCHOuterGridChangeBasis

namespace OAI

section

namespace Erdos3.IsCentralLieBasis

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d s : ℕ}
  {e : Basis (Fin d) ℚ L} (he : IsCentralLieBasis e)
  (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
  (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))

include he

def leadingCoordinateSubgroup (j : Fin d) : AddSubgroup ℚ where
  carrier := {q | ∃ g ∈ Γ, g.coord ∈ basisTail e j.val ∧ e.repr g.coord j = q}
  zero_mem' := ⟨1, Γ.one_mem, (basisTail e j.val).zero_mem, by simp⟩
  add_mem' := by
    rintro a b ⟨g, hg, hgt, rfl⟩ ⟨h, hh, hht, rfl⟩
    refine ⟨g * h, Γ.mul_mem hg hh, ?_, ?_⟩
    · exact (NilpotentLieBCHGroup.subgroup (he.tailIdeal j.val).toLieSubalgebra).mul_mem hgt hht
    · exact he.bch_low_coordinate hnil j.val g.coord hht j le_rfl
  neg_mem' := by
    rintro a ⟨g, hg, hgt, rfl⟩
    exact ⟨g⁻¹, Γ.inv_mem hg, (basisTail e j.val).neg_mem hgt, by simp⟩

theorem leadingCoordinateSubgroup_le_zmultiples (l : ℕ) (hl : 0 < l)
    (hgrid : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l) (j : Fin d) :
    he.leadingCoordinateSubgroup hnil Γ j ≤ AddSubgroup.zmultiples ((l : ℚ)⁻¹) := by
  rintro q ⟨g, hg, _, rfl⟩
  obtain ⟨z, hz⟩ := (mem_denominatorGrid_iff l hl _).mp
    (hgrid ((bchSubgroupCoordinates_repr e Γ g).mpr hg))
  apply AddSubgroup.mem_zmultiples_iff.mpr
  refine ⟨z j, ?_⟩
  simpa only [zsmul_eq_mul, div_eq_mul_inv, Basis.equivFun_apply] using (hz j).symm

theorem leadingCoordinateSubgroup_isAddCyclic (l : ℕ) (hl : 0 < l)
    (hgrid : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l) (j : Fin d) :
    IsAddCyclic (he.leadingCoordinateSubgroup hnil Γ j) :=
  AddSubgroup.isAddCyclic_of_le (he.leadingCoordinateSubgroup_le_zmultiples hnil Γ l hl hgrid j)

theorem exists_tail_generator (l : ℕ) (hl : 0 < l)
    (hgrid : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l) (j : Fin d) :
    ∃ a ∈ Γ, a.coord ∈ basisTail e j.val ∧
      ∀ g ∈ Γ, g.coord ∈ basisTail e j.val →
        ∃ n : ℤ, ((a ^ n)⁻¹ * g).coord ∈ basisTail e (j.val + 1) := by
  let H := he.leadingCoordinateSubgroup hnil Γ j
  let : IsAddCyclic H := he.leadingCoordinateSubgroup_isAddCyclic hnil Γ l hl hgrid j
  obtain ⟨q, hq⟩ := (AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top H).mp inferInstance
  have hqmem : q ∈ H := hq ▸ AddSubgroup.mem_zmultiples q
  obtain ⟨a, ha, hat, haq⟩ := hqmem
  refine ⟨a, ha, hat, ?_⟩
  intro g hg hgt
  have hcoord : e.repr g.coord j ∈ H := ⟨g, hg, hgt, rfl⟩
  rw [← hq] at hcoord
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hcoord
  refine ⟨n, (mem_basisTail_succ_iff e j _).mpr ⟨?_, ?_⟩⟩
  · let T := NilpotentLieBCHGroup.subgroup (hnil := hnil) (he.tailIdeal j.val).toLieSubalgebra
    exact T.mul_mem (T.inv_mem (T.zpow_mem hat n)) hgt
  · change e.repr (lieBCH s (-((a ^ n).coord)) g.coord) j = 0
    rw [he.bch_low_coordinate hnil j.val _ hgt j le_rfl]
    simp only [map_neg, Finsupp.neg_apply, NilpotentLieBCHGroup.coord_zpow,
      map_zsmul, Finsupp.smul_apply, haq, hn, neg_add_cancel]

end Erdos3.IsCentralLieBasis

end

section

namespace Erdos3.IsCentralLieBasis

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d s : ℕ}
  {e : Basis (Fin d) ℚ L} (he : IsCentralLieBasis e)
  (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
  (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))

include he

theorem exists_ordered_lattice_generators (l : ℕ) (hl : 0 < l)
    (hgrid : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l) :
    ∃ a : Fin d → NilpotentLieBCHGroup L s hnil,
      (∀ j, a j ∈ Γ) ∧ (∀ j, (a j).coord ∈ basisTail e j.val) ∧
      ∀ g ∈ Γ, ∃ z : Fin d → ℤ, orderedZpowProduct a z = g := by
  classical
  choose a ha hat hpeel using fun j => he.exists_tail_generator hnil Γ l hl hgrid j
  have hfactor (k i : ℕ) (hik : i + k = d)
      (g : NilpotentLieBCHGroup L s hnil) (hg : g ∈ Γ) (hgt : g.coord ∈ basisTail e i) :
      ∃ z : Fin d → ℤ, orderedGroupTailProduct (fun j => a j ^ z j) i = g := by
    induction k generalizing i g with
    | zero =>
        have hi : i = d := by omega
        subst i
        refine ⟨fun _ => 0, ?_⟩
        rw [orderedGroupTailProduct_terminal _ le_rfl]
        apply NilpotentLieBCHGroup.ext
        have hz : g.coord = 0 := by
          simpa only [basisTail_terminal, Submodule.mem_bot] using hgt
        exact hz.symm
    | succ k ih =>
        have hi : i < d := by omega
        let j : Fin d := ⟨i, hi⟩
        obtain ⟨n, hn⟩ := hpeel j g hg hgt
        let r := (a j ^ n)⁻¹ * g
        have hr : r ∈ Γ := Γ.mul_mem (Γ.inv_mem (Γ.zpow_mem (ha j) n)) hg
        obtain ⟨z, hz⟩ := ih (i + 1) (by omega) r hr hn
        let u := Function.update z j n
        have huj : u j = n := by simp [u]
        have hu : orderedGroupTailProduct (fun j => a j ^ u j) (i + 1) =
            orderedGroupTailProduct (fun j => a j ^ z j) (i + 1) := by
          apply orderedGroupTailProduct_congr
          intro v hv
          have hvj : v ≠ j := by
            intro h
            subst v
            change i + 1 ≤ i at hv
            omega
          change a v ^ Function.update z j n v = a v ^ z v
          rw [Function.update_of_ne hvj]
        refine ⟨u, ?_⟩
        change orderedGroupTailProduct (fun j => a j ^ u j) j.val = g
        rw [orderedGroupTailProduct_step, huj]
        change a j ^ n * orderedGroupTailProduct (fun j => a j ^ u j) (i + 1) = g
        rw [hu, hz]
        exact mul_inv_cancel_left (a j ^ n) g
  refine ⟨a, ha, hat, ?_⟩
  intro g hg
  exact hfactor d 0 (by omega) g hg (by simp [basisTail_zero])

theorem exists_surjective_orderedZpowProduct (l : ℕ) (hl : 0 < l)
    (hgrid : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l) :
    ∃ a : Fin d → Γ, Function.Surjective (orderedZpowProduct a) := by
  obtain ⟨a, ha, _, hgen⟩ := he.exists_ordered_lattice_generators hnil Γ l hl hgrid
  refine ⟨fun j => ⟨a j, ha j⟩, ?_⟩
  intro g
  obtain ⟨z, hz⟩ := hgen g g.property
  refine ⟨z, Subtype.ext ?_⟩
  change Γ.subtype (orderedZpowProduct (fun j => ⟨a j, ha j⟩) z) = g.val
  rw [orderedZpowProduct_map]
  exact hz

end Erdos3.IsCentralLieBasis

end

end OAI

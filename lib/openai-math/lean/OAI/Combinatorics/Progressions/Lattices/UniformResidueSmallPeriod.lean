/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import Mathlib.Probability.Distributions.Uniform
import OAI.Combinatorics.Progressions.Estimates.CoefficientRowReindex

namespace OAI


namespace Erdos3

open scoped BigOperators Classical Matrix

theorem uniformPMF_map_fiber {G H : Type*} [Fintype G] [Nonempty G]
    [DecidableEq H] (f : G → H) (y : H) :
    ((PMF.uniformOfFintype G).map f y).toReal =
      ((Finset.univ.filter (fun x => f x = y)).card : ℝ) / Fintype.card G := by
  classical
  rw [pmf_map_toReal_indicator, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

theorem uniformPMF_map_hom_image {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    [Fintype G] [Fintype H] (f : G →+ H) (y : H) :
    ((PMF.uniformOfFintype G).map f y).toReal =
      if y ∈ f.range then (Nat.card f.range : ℝ)⁻¹ else 0 := by
  classical
  rw [uniformPMF_map_fiber]
  by_cases hy : y ∈ f.range
  · simp only [hy, ite_true]
    have he := AddMonoidHom.card_fiber_eq_of_mem_range f hy
      (show (0 : H) ∈ Set.range f from ⟨0, f.map_zero⟩)
    have hk : (Finset.univ.filter (fun x => f x = 0)).card = Fintype.card f.ker := by
      simp [Fintype.card_subtype, AddMonoidHom.mem_ker]
    have hc : Fintype.card f.ker * Fintype.card f.range = Fintype.card G := by
      simpa only [AddSubgroup.index_ker, Nat.card_eq_fintype_card] using f.ker.card_mul_index
    rw [he, hk, ← hc, Nat.cast_mul, Nat.card_eq_fintype_card]
    have hkn : (Fintype.card f.ker : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp
  · simp only [hy, ite_false]
    have hz : Finset.univ.filter (fun x => f x = y) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hy ⟨x, (Finset.mem_filter.mp hx).2⟩
    simp [hz]

theorem uniformPMF_map_hom_index {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    [Fintype G] [Fintype H] (f : G →+ H) (y : H) :
    ((PMF.uniformOfFintype G).map f y).toReal =
      (if y ∈ f.range then (f.range.index : ℝ) else 0) / Fintype.card H := by
  classical
  rw [uniformPMF_map_hom_image]
  by_cases hy : y ∈ f.range
  · simp only [hy, ite_true]
    have hcard : (Nat.card f.range : ℝ) * f.range.index = Fintype.card H := by
      have h := f.range.card_mul_index
      rw [Nat.card_eq_fintype_card (α := H)] at h
      exact_mod_cast h
    have hn : (Nat.card f.range : ℝ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
    have hh : (Fintype.card H : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    apply (eq_div_iff hh).mpr
    rw [← hcard, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]
  · simp [hy]

theorem uniformResidueMatrix_image_mask {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (d : ℕ) [NeZero d]
    (hperiod : integerScalarLattice I (d : ℤ) ≤ A.mulVecLin.range) (v : I → ℤ) :
    ((PMF.uniformOfFintype (J → ZMod d)).map
      (fun x => integerResidueMatrix A d *ᵥ x) (integerResidueMap I d v)).toReal =
        coefficientImageMultiplier A v / (d : ℝ) ^ Fintype.card I := by
  classical
  let f := (integerResidueMatrix A d).mulVecLin.toAddMonoidHom
  have hr : f.range = (residueLatticeImage A.mulVecLin.range d).toAddSubgroup := by
    ext y
    exact (integerMatrixResidue_mem A d y).symm
  have hm : integerResidueMap I d v ∈ f.range ↔ v ∈ A.mulVecLin.range := by
    rw [hr]
    exact (residueLatticeImage_mem_iff _ _ hperiod v).symm
  have hi : f.range.index = A.mulVecLin.range.toAddSubgroup.index := by
    rw [hr, residueLatticeImage_index _ _ hperiod]
  change ((PMF.uniformOfFintype (J → ZMod d)).map f _).toReal = _
  rw [uniformPMF_map_hom_index]
  simp only [hm, hi, coefficientImageMultiplier, Fintype.card_fun, ZMod.card, Nat.cast_pow]

end Erdos3


namespace Erdos3

open scoped BigOperators Classical Matrix

theorem residueLatticeImage_index_le_period {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (d m : ℕ) [NeZero m]
    (hperiod : integerScalarLattice I (m : ℤ) ≤ L) :
    (residueLatticeImage L d).toAddSubgroup.index ≤ m ^ Fintype.card I := by
  have hcard := residueLatticeImage_card_mul_index L m hperiod
  have hn : L.toAddSubgroup.index ≠ 0 := by
    intro h
    rw [h, mul_zero] at hcard
    exact pow_ne_zero _ (NeZero.ne m) hcard.symm
  have hd := L.toAddSubgroup.index_map_dvd (f := (integerResidueMap I d).toAddMonoidHom)
    (integerResidueMap_surjective I d)
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd).trans
    (residueLatticeImage_index_le L m hperiod)

theorem uniformResidueMatrix_density_bound {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (d m : ℕ) [NeZero d] [NeZero m]
    (hperiod : integerScalarLattice I (m : ℤ) ≤ A.mulVecLin.range) (r : I → ZMod d) :
    (d : ℝ) ^ Fintype.card I *
      (((PMF.uniformOfFintype (J → ZMod d)).map
        (fun x => integerResidueMatrix A d *ᵥ x)) r).toReal ≤ (m : ℝ) ^ Fintype.card I := by
  let f := (integerResidueMatrix A d).mulVecLin.toAddMonoidHom
  have hr : f.range = (residueLatticeImage A.mulVecLin.range d).toAddSubgroup := by
    ext y
    exact (integerMatrixResidue_mem A d y).symm
  have hi : (f.range.index : ℝ) ≤ (m : ℝ) ^ Fintype.card I := by
    rw [hr]
    exact_mod_cast residueLatticeImage_index_le_period A.mulVecLin.range d m hperiod
  have hc : (Fintype.card (I → ZMod d) : ℝ) = (d : ℝ) ^ Fintype.card I := by
    simp only [Fintype.card_fun, ZMod.card, Nat.cast_pow]
  have hc0 : (Fintype.card (I → ZMod d) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  change (d : ℝ) ^ Fintype.card I * (((PMF.uniformOfFintype (J → ZMod d)).map f) r).toReal ≤ _
  rw [uniformPMF_map_hom_index, ← hc]
  by_cases h : r ∈ f.range
  · simp only [h, ite_true]
    convert hi using 1
    field_simp
  · simp only [h, ite_false, zero_div, mul_zero]
    positivity

theorem uniformResidueMatrix_family_density_bound {T : Type*} [Fintype T]
    {I J B : T → Type*} [∀ t, Fintype (I t)] [∀ t, Fintype (J t)]
    [∀ t, DecidableEq (J t)] [∀ t, Fintype (B t)]
    (A : ∀ t, Matrix (I t) (J t) ℤ) (d period : ℕ) [NeZero d] [NeZero period]
    (hperiod : ∀ t, integerScalarLattice (I t) (period : ℤ) ≤ (A t).mulVecLin.range)
    (r : ∀ t, I t → B t → ZMod d) :
    (∏ t, ∏ i : B t, (d : ℝ) ^ Fintype.card (I t) *
      (((PMF.uniformOfFintype (J t → ZMod d)).map
        (fun z => integerResidueMatrix (A t) d *ᵥ z)) (fun x => r t x i)).toReal) ≤
      ∏ t, ∏ _i : B t, (period : ℝ) ^ Fintype.card (I t) := by
  apply Finset.prod_le_prod₀
  · intro t _
    positivity
  · intro t _
    apply Finset.prod_le_prod₀
    · intro i _
      positivity
    · intro i _
      exact uniformResidueMatrix_density_bound (A t) d period (hperiod t) (fun x => r t x i)

end Erdos3


namespace Erdos3

open scoped BigOperators Classical Matrix

theorem uniformPMF_map_hom_toReal_eq_of_sub_mem {G H : Type*}
    [AddCommGroup G] [AddCommGroup H] [Fintype G] [Fintype H]
    (f : G →+ H) {x y : H} (hxy : x - y ∈ f.range) :
    (((PMF.uniformOfFintype G).map f) x).toReal =
      (((PMF.uniformOfFintype G).map f) y).toReal := by
  have hmem : x ∈ f.range ↔ y ∈ f.range := by
    constructor
    · intro hx
      simpa only [sub_sub_cancel] using f.range.sub_mem hx hxy
    · intro hy
      simpa only [sub_add_cancel] using f.range.add_mem hxy hy
  simp only [uniformPMF_map_hom_image, hmem]

theorem uniformResidueMatrix_toReal_eq_of_period {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (d period : ℕ) [NeZero d]
    (hperiod : integerScalarLattice I (period : ℤ) ≤ A.mulVecLin.range)
    (v w : I → ℤ) (hvw : integerResidueMap I period v = integerResidueMap I period w) :
    (((PMF.uniformOfFintype (J → ZMod d)).map
      (fun z => integerResidueMatrix A d *ᵥ z)) (integerResidueMap I d v)).toReal =
    (((PMF.uniformOfFintype (J → ZMod d)).map
      (fun z => integerResidueMatrix A d *ᵥ z)) (integerResidueMap I d w)).toReal := by
  have hdiff : v - w ∈ A.mulVecLin.range := by
    apply hperiod
    rw [← integerResidueMap_ker, LinearMap.mem_ker, map_sub, hvw, sub_self]
  have himage : integerResidueMap I d (v - w) ∈ residueLatticeImage A.mulVecLin.range d :=
    ⟨v - w, hdiff, rfl⟩
  obtain ⟨z, hz⟩ := (integerMatrixResidue_mem A d _).mp himage
  apply uniformPMF_map_hom_toReal_eq_of_sub_mem (integerResidueMatrix A d).mulVecLin.toAddMonoidHom
  exact ⟨z, hz.trans (map_sub (integerResidueMap I d) v w)⟩

noncomputable def uniformResidueSmallPeriodDensity {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq J] (A : Matrix I J ℤ) (d period : ℕ) [NeZero d]
    (r : I → ZMod period) : ℝ :=
  (d : ℝ) ^ Fintype.card I *
    (((PMF.uniformOfFintype (J → ZMod d)).map
      (fun z => integerResidueMatrix A d *ᵥ z))
        (fun i => ((r i).val : ZMod d))).toReal

theorem uniformResidueSmallPeriodDensity_apply {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (d period : ℕ) [NeZero d] [NeZero period]
    (hperiod : integerScalarLattice I (period : ℤ) ≤ A.mulVecLin.range) (v : I → ℤ) :
    uniformResidueSmallPeriodDensity A d period (integerResidueMap I period v) =
      (d : ℝ) ^ Fintype.card I *
        (((PMF.uniformOfFintype (J → ZMod d)).map
          (fun z => integerResidueMatrix A d *ᵥ z)) (integerResidueMap I d v)).toReal := by
  unfold uniformResidueSmallPeriodDensity
  congr 1
  have h := uniformResidueMatrix_toReal_eq_of_period A d period hperiod
    (fun i => (((v i : ZMod period).val : ℕ) : ℤ)) v (by
      ext i
      simp only [integerResidueMap_apply, Int.cast_natCast, ZMod.natCast_zmod_val])
  simpa only [integerResidueMap, LinearMap.coe_mk, AddHom.coe_mk, Int.cast_natCast] using h

theorem uniformResidueSmallPeriodDensity_bounds {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (d period : ℕ) [NeZero d] [NeZero period]
    (hperiod : integerScalarLattice I (period : ℤ) ≤ A.mulVecLin.range) (r : I → ZMod period) :
    0 ≤ uniformResidueSmallPeriodDensity A d period r ∧
      uniformResidueSmallPeriodDensity A d period r ≤ (period : ℝ) ^ Fintype.card I := by
  constructor
  · exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) ENNReal.toReal_nonneg
  · exact uniformResidueMatrix_density_bound A d period hperiod _

end Erdos3

end OAI

import OAI.Combinatorics.Progressions.Estimates.ImageRepresentatives
import OAI.Combinatorics.Progressions.Linear.RealOrderedBasisProduct
import OAI.Combinatorics.Progressions.Sampling.IntegralGridBudget

namespace OAI

section

namespace Erdos3

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d s : ℕ}
  (e : Basis (Fin d) ℚ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)

noncomputable def integralOrderedBasisProduct (B : ℕ) (z : Fin d → ℤ) :
    NilpotentLieBCHGroup L s hnil :=
  orderedBasisProduct e hnil (fun j => (B : ℚ) * (z j : ℚ))

theorem integralOrderedBasisProduct_eq_zpowProduct (B : ℕ) (z : Fin d → ℤ) :
    integralOrderedBasisProduct e hnil B z = orderedZpowProduct
      (fun j => (⟨(B : ℚ) • e j⟩ : NilpotentLieBCHGroup L s hnil)) z := by
  unfold integralOrderedBasisProduct orderedBasisProduct orderedBasisTailProduct
    orderedZpowProduct orderedGroupProduct orderedGroupTailProduct
  apply congrArg List.prod
  apply List.map_congr_left
  intro j _
  apply NilpotentLieBCHGroup.ext
  rw [NilpotentLieBCHGroup.coord_zpow, ← Int.cast_smul_eq_zsmul ℚ, smul_smul]
  change ((B : ℚ) * (z j : ℚ)) • e j = ((z j : ℚ) * (B : ℚ)) • e j
  rw [mul_comm (B : ℚ) (z j : ℚ)]

theorem integral_basis_factor_mem (Λ : Subgroup (NilpotentLieBCHGroup L s hnil)) (B : ℕ)
    (hgrid : bchSubgroupCoordinates e Λ = scaledIntegerGrid B) (j : Fin d) (n : ℤ) :
    (⟨((B : ℚ) * (n : ℚ)) • e j⟩ : NilpotentLieBCHGroup L s hnil) ∈ Λ := by
  apply (bchSubgroupCoordinates_repr e Λ _).mp
  rw [hgrid]
  have h := (coordinateGridModule e B).smul_mem n (scaled_basis_mem_coordinateGridModule e B j)
  rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul, mul_comm (n : ℚ) (B : ℚ)] at h
  exact h

theorem integralOrderedBasisProduct_mem (Λ : Subgroup (NilpotentLieBCHGroup L s hnil)) (B : ℕ)
    (hgrid : bchSubgroupCoordinates e Λ = scaledIntegerGrid B) (z : Fin d → ℤ) :
    integralOrderedBasisProduct e hnil B z ∈ Λ := by
  apply list_prod_mem
  intro g hg
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hg
  exact integral_basis_factor_mem e hnil Λ B hgrid j (z j)

namespace IsCentralLieBasis

variable {e} (he : IsCentralLieBasis e)
include he

theorem integralOrderedBasisProduct_injective (B : ℕ) (hB : 0 < B) :
    Function.Injective (integralOrderedBasisProduct e hnil B) := by
  intro z w hzw
  have h := he.orderedBasisProduct_injective hnil hzw
  funext j
  apply Int.cast_injective (α := ℚ)
  exact mul_left_cancel₀ (show (B : ℚ) ≠ 0 by exact_mod_cast hB.ne') (congrFun h j)

theorem exists_integralOrderedBasisProduct
    (Λ : Subgroup (NilpotentLieBCHGroup L s hnil)) (B : ℕ)
    (hgrid : bchSubgroupCoordinates e Λ = scaledIntegerGrid B)
    (g : NilpotentLieBCHGroup L s hnil) (hg : g ∈ Λ) :
    ∃ z : Fin d → ℤ, integralOrderedBasisProduct e hnil B z = g := by
  classical
  have hfactor (k i : ℕ) (hik : i + k = d)
      (g : NilpotentLieBCHGroup L s hnil) (hg : g ∈ Λ) (hgt : g.coord ∈ basisTail e i) :
      ∃ z : Fin d → ℤ,
        orderedBasisTailProduct e hnil i (fun j => (B : ℚ) * (z j : ℚ)) = g := by
    induction k generalizing i g with
    | zero =>
        have hi : i = d := by omega
        subst i
        refine ⟨fun _ => 0, ?_⟩
        rw [orderedBasisTailProduct_terminal e hnil le_rfl]
        apply NilpotentLieBCHGroup.ext
        have hz : g.coord = 0 := by
          simpa only [basisTail_terminal, Submodule.mem_bot] using hgt
        exact hz.symm
    | succ k ih =>
        have hi : i < d := by omega
        let j : Fin d := ⟨i, hi⟩
        have hcoord := (bchSubgroupCoordinates_repr e Λ g).mpr hg
        rw [hgrid] at hcoord
        obtain ⟨v, hv⟩ := hcoord
        have hvj : e.repr g.coord j = (B : ℚ) * (v j : ℚ) := congrFun hv j
        let a : NilpotentLieBCHGroup L s hnil := ⟨((B : ℚ) * (v j : ℚ)) • e j⟩
        have ha : a ∈ Λ := integral_basis_factor_mem e hnil Λ B hgrid j (v j)
        let r := a⁻¹ * g
        have hr : r ∈ Λ := Λ.mul_mem (Λ.inv_mem ha) hg
        have hrt : r.coord ∈ basisTail e (i + 1) := by
          simpa only [hvj] using he.peel_mem_tail hnil j g hgt
        obtain ⟨z, hz⟩ := ih (i + 1) (by omega) r hr hrt
        let u := Function.update z j (v j)
        have huj : u j = v j := by simp [u]
        have hu : orderedBasisTailProduct e hnil (i + 1) (fun l => (B : ℚ) * (u l : ℚ)) =
            orderedBasisTailProduct e hnil (i + 1) (fun l => (B : ℚ) * (z l : ℚ)) := by
          apply orderedBasisTailProduct_congr
          intro l hl
          have hlj : l ≠ j := by
            intro h
            subst l
            change i + 1 ≤ i at hl
            omega
          simp only [u, Function.update_of_ne hlj]
        refine ⟨u, ?_⟩
        change orderedBasisTailProduct e hnil j.val _ = g
        rw [orderedBasisTailProduct_step, huj]
        change a * orderedBasisTailProduct e hnil (i + 1) _ = g
        rw [hu, hz]
        exact mul_inv_cancel_left a g
  exact hfactor d 0 (by omega) g hg (by simp [basisTail_zero])

noncomputable def integralOrderedBasisEquiv
    (Λ : Subgroup (NilpotentLieBCHGroup L s hnil)) (B : ℕ) (hB : 0 < B)
    (hgrid : bchSubgroupCoordinates e Λ = scaledIntegerGrid B) : (Fin d → ℤ) ≃ Λ :=
  Equiv.ofBijective
    (fun z => ⟨integralOrderedBasisProduct e hnil B z, integralOrderedBasisProduct_mem e hnil Λ B hgrid z⟩)
    ⟨fun _ _ h => he.integralOrderedBasisProduct_injective hnil B hB (congrArg Subtype.val h), by
      intro g
      obtain ⟨z, hz⟩ := he.exists_integralOrderedBasisProduct hnil Λ B hgrid g g.property
      exact ⟨z, Subtype.ext hz⟩⟩

theorem exists_unique_integralOrderedBasisProduct
    (Λ : Subgroup (NilpotentLieBCHGroup L s hnil)) (B : ℕ) (hB : 0 < B)
    (hgrid : bchSubgroupCoordinates e Λ = scaledIntegerGrid B)
    (g : NilpotentLieBCHGroup L s hnil) (hg : g ∈ Λ) :
    ∃! z : Fin d → ℤ, integralOrderedBasisProduct e hnil B z = g := by
  obtain ⟨z, hz⟩ := he.exists_integralOrderedBasisProduct hnil Λ B hgrid g hg
  exact ⟨z, hz, fun w hw => he.integralOrderedBasisProduct_injective hnil B hB (hw.trans hz.symm)⟩

end IsCentralLieBasis
end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d s : ℕ}
  (e : Basis (Fin d) ℚ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)

noncomputable def realIntegralOrderedBasisProduct (B : ℕ) (z : Fin d → ℤ) :
    NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil) :=
  realOrderedBasisProduct (e.baseChange ℝ) (realification_lowerCentralSeries_eq_bot hnil)
    (fun j => (B : ℝ) * (z j : ℝ))

theorem realification_integralOrderedBasisProduct (B : ℕ) (z : Fin d → ℤ) :
    realificationHom (integralOrderedBasisProduct e hnil B z) =
      realIntegralOrderedBasisProduct e hnil B z := by
  unfold integralOrderedBasisProduct orderedBasisProduct orderedBasisTailProduct
    realIntegralOrderedBasisProduct realOrderedBasisProduct realOrderedBasisTailProduct
  rw [map_list_prod, List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro j _
  apply NilpotentLieBCHGroup.ext
  change rationalLieInclusion (((B : ℚ) * (z j : ℚ)) • e j) =
    ((B : ℝ) * (z j : ℝ)) • (e.baseChange ℝ) j
  rw [map_smul, Basis.baseChange_apply]
  simp only [rationalLieInclusion_apply, ← Rat.cast_smul_eq_qsmul ℝ,
    Rat.cast_mul, Rat.cast_natCast, Rat.cast_intCast]

theorem realIntegralOrderedBasisProduct_mem
    (Λ : Subgroup (NilpotentLieBCHGroup L s hnil)) (B : ℕ)
    (hgrid : bchSubgroupCoordinates e Λ = scaledIntegerGrid B) (z : Fin d → ℤ) :
    realIntegralOrderedBasisProduct e hnil B z ∈ Λ.map realificationHom := by
  exact Subgroup.mem_map.mpr ⟨integralOrderedBasisProduct e hnil B z,
    integralOrderedBasisProduct_mem e hnil Λ B hgrid z,
    realification_integralOrderedBasisProduct e hnil B z⟩

namespace IsCentralLieBasis

variable {e} (he : IsCentralLieBasis e)
include he

theorem realIntegralOrderedBasisProduct_injective (B : ℕ) (hB : 0 < B) :
    Function.Injective (realIntegralOrderedBasisProduct e hnil B) := by
  intro z w h
  apply he.integralOrderedBasisProduct_injective hnil B hB
  apply realificationHom_injective e
  simpa only [realification_integralOrderedBasisProduct] using h

theorem exists_realIntegralOrderedBasisProduct
    (Λ : Subgroup (NilpotentLieBCHGroup L s hnil)) (B : ℕ)
    (hgrid : bchSubgroupCoordinates e Λ = scaledIntegerGrid B)
    (g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil))
    (hg : g ∈ Λ.map realificationHom) :
    ∃ z : Fin d → ℤ, realIntegralOrderedBasisProduct e hnil B z = g := by
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hg
  obtain ⟨z, hz⟩ := he.exists_integralOrderedBasisProduct hnil Λ B hgrid a ha
  exact ⟨z, (realification_integralOrderedBasisProduct e hnil B z).symm.trans
    (congrArg realificationHom hz)⟩

theorem exists_unique_realIntegralOrderedBasisProduct
    (Λ : Subgroup (NilpotentLieBCHGroup L s hnil)) (B : ℕ) (hB : 0 < B)
    (hgrid : bchSubgroupCoordinates e Λ = scaledIntegerGrid B)
    (g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil))
    (hg : g ∈ Λ.map realificationHom) :
    ∃! z : Fin d → ℤ, realIntegralOrderedBasisProduct e hnil B z = g := by
  obtain ⟨z, hz⟩ := he.exists_realIntegralOrderedBasisProduct hnil Λ B hgrid g hg
  exact ⟨z, hz, fun w hw =>
    he.realIntegralOrderedBasisProduct_injective hnil B hB (hw.trans hz.symm)⟩

noncomputable def realIntegralOrderedBasisEquiv
    (Λ : Subgroup (NilpotentLieBCHGroup L s hnil)) (B : ℕ) (hB : 0 < B)
    (hgrid : bchSubgroupCoordinates e Λ = scaledIntegerGrid B) :
    (Fin d → ℤ) ≃ Λ.map realificationHom :=
  Equiv.ofBijective
    (fun z => ⟨realIntegralOrderedBasisProduct e hnil B z,
      realIntegralOrderedBasisProduct_mem e hnil Λ B hgrid z⟩)
    ⟨fun _ _ h => he.realIntegralOrderedBasisProduct_injective hnil B hB
      (congrArg Subtype.val h), by
      intro g
      obtain ⟨z, hz⟩ := he.exists_realIntegralOrderedBasisProduct hnil Λ B hgrid g g.property
      exact ⟨z, Subtype.ext hz⟩⟩

theorem mul_realIntegralOrderedBasisProduct_coordinate (B : ℕ) (z : Fin d → ℤ)
    (a : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil))
    (j : Fin d) :
    (e.baseChange ℝ).repr (a * realIntegralOrderedBasisProduct e hnil B z).coord j =
      (e.baseChange ℝ).repr (a * realOrderedBasisPrefixProduct (e.baseChange ℝ)
        (realification_lowerCentralSeries_eq_bot hnil) j.val
        (fun k => (B : ℝ) * (z k : ℝ))).coord j + (B : ℝ) * (z j : ℝ) :=
  he.real_baseChange.mul_realOrderedBasisProduct_coordinate
    (realification_lowerCentralSeries_eq_bot hnil) a _ j

end IsCentralLieBasis
end Erdos3

end

section

namespace Erdos3

open Module

theorem exists_controlled_integral_coordinates (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      (e : Basis (Fin d) ℚ L) (_he : IsCentralLieBasis e)
      (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l H : ℕ) (p : ℝ),
      0 < l → (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ →
      bchSubgroupCoordinates e Γ ⊆ denominatorGrid l →
      0 ≤ p → (d : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      ∃ (B : ℕ) (Λ : Subgroup (NilpotentLieBCHGroup L s hnil)),
        0 < B ∧ l ∣ B ∧ (B : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        Λ ≤ Γ ∧ (Λ.subgroupOf Γ).FiniteIndex ∧
        bchSubgroupCoordinates e Λ = scaledIntegerGrid B ∧
        ∀ g ∈ Λ, ∃! z : Fin d → ℤ, integralOrderedBasisProduct e hnil B z = g := by
  obtain ⟨C, hC, hgrid⟩ := exists_integral_grid_subgroup_exp s
  obtain ⟨I, _, hindex⟩ := exists_subgroup_index_exp_bound s
  refine ⟨C, hC, ?_⟩
  intro L _ _ d e he hnil Γ l H p hl hc hinner houter hp hd hH hlp
  obtain ⟨B, Λ, hB, hdiv, hbound, hΛ, hcoords⟩ :=
    hgrid e hnil Γ l H p hl hc hinner hp (by simpa only [Fintype.card_fin] using hd) hH hlp
  have hpq : p ≤ (p + C) ^ C := by
    calc
      p ≤ p + C := le_add_of_nonneg_right (Nat.cast_nonneg C)
      _ ≤ (p + C) ^ C := by
        simpa only [pow_one] using pow_le_pow_right₀ (show (1 : ℝ) ≤ p + C by
          have : (2 : ℝ) ≤ C := by exact_mod_cast hC
          linarith) (show 1 ≤ C by omega)
  have hfinite := (hindex e hnil Γ Λ l B H ((p + C) ^ C) hΛ hl hB houter
    (by rw [hcoords]) hc (hp.trans hpq) (by simpa only [Fintype.card_fin] using hd.trans hpq)
    (hH.trans (Real.exp_le_exp.mpr hpq)) (hlp.trans (Real.exp_le_exp.mpr hpq)) hbound).1
  exact ⟨B, Λ, hB, hdiv, hbound, hΛ, hfinite, hcoords,
    he.exists_unique_integralOrderedBasisProduct hnil Λ B hB hcoords⟩

end Erdos3

end

end OAI

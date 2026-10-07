import OAI.Combinatorics.Progressions.Sampling.SmoothSplitSampling

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem pmf_map_equiv_apply {X Y : Type*} (p : PMF X) (e : X ≃ Y) (y : Y) :
    (p.map e) y = p (e.symm y) := by
  classical
  rw [PMF.map_apply, tsum_eq_single (e.symm y)]
  · simp
  · intro z hz
    have he : y ≠ e z := by
      intro he
      apply hz
      apply e.injective
      simpa only [e.apply_symm_apply] using he.symm
    simp only [ite_eq_right_iff]
    exact fun h => (he h).elim

theorem smoothProductPMF_reindex_apply {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (S : J → ℝ) (hS : ∀ j, 0 < S j) (z : J → ℤ) :
    smoothProductPMF (S ∘ e) (fun i => hS (e i)) (z ∘ e) = smoothProductPMF S hS z := by
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [smoothProductPMF_apply, smoothProductPMF_apply]
  exact Equiv.prod_comp e (fun j => (smoothCoefficientPMF (S j) (hS j) (z j)).toReal)

theorem smoothProductPMF_reindex {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (S : J → ℝ) (hS : ∀ j, 0 < S j) :
    (smoothProductPMF (S ∘ e) (fun i => hS (e i))).map
      (fun z => z ∘ e.symm) = smoothProductPMF S hS := by
  let E : (I → ℤ) ≃ (J → ℤ) := Equiv.arrowCongr e (Equiv.refl ℤ)
  change (smoothProductPMF (S ∘ e) (fun i => hS (e i))).map E = _
  ext z
  rw [pmf_map_equiv_apply]
  exact smoothProductPMF_reindex_apply e S hS z

theorem smoothSplit_inputPMF_join {I J : Type*} [Fintype I] [Fintype J]
    (S : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j) :
    (scaledInputPMF (smoothSplitProfile J I) (fun p => (smoothSplitProfile_range J I p).1)
      S T hS hT (smoothSplitProfile_zero_outside J I) (smoothSplit_mass_pos S T hS hT)).map
        (fun p => Sum.elim p.1 p.2) =
      smoothProductPMF (Sum.elim S T) (fun k => Sum.rec hS hT k) := by
  let E := (Equiv.sumPiEquivProdPi (fun _ : I ⊕ J => ℤ)).symm
  change (scaledInputPMF _ _ _ _ _ _ _ _).map E = _
  ext z
  rw [pmf_map_equiv_apply]
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [smoothSplit_inputPMF_apply, smoothProductPMF_apply]
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]
  rfl

end Erdos3

end

end OAI

import OAI.Combinatorics.Progressions.Estimates.RealSubspaceIntersectionCorrections

namespace OAI

section

namespace Erdos3

theorem exists_controlled_kernel_split_equiv {H ι κ ν τ : Type*}
    [AddCommGroup H] [Module ℝ H] [Fintype ι] [Fintype κ] [Fintype ν]
    (e : H ≃ₗ[ℝ] (ι → ℝ)) (U K : Submodule ℝ H)
    (A : Matrix ι κ ℚ) (B : Matrix ι ν ℚ)
    (hAspan : Submodule.span ℝ (Set.range (A.map (Rat.castHom ℝ)).col) = U.map e.toLinearMap)
    (hBspan : Submodule.span ℝ (Set.range (B.map (Rat.castHom ℝ)).col) = K.map e.toLinearMap)
    (b : ν → K) (hb : ∀ j, e (b j).val = (B.map (Rat.castHom ℝ)).col j)
    (R : K →ₗ[ℝ] (τ → ℝ)) (n : ℕ) (hR : ∀ j, R (b j) ∈ realDenominatorGrid n)
    {J l : ℕ} (hJ : 1 ≤ J) (hl : 0 < l)
    (hA : ∀ i j, RationalHeightLE (A i j) J) (hB : ∀ i j, RationalHeightLE (B i j) J)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hcols : (Fintype.card (κ ⊕ ν) : ℝ) ≤ p)
    (hJp : (J : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧
      ∃ split : H →ₗ[ℝ] K,
        (∀ x, x ∈ U ⊔ K → x - (split x).val ∈ U) ∧
        (∀ x, ‖e (split x).val‖ ≤ Real.exp ((p + 2) ^ 19) * ‖e x‖) ∧
        ∀ x, e x ∈ realDenominatorGrid l → R (split x) ∈ realDenominatorGrid (n * m) := by
  let eK : K ≃ₗ[ℝ] K.map e.toLinearMap := e.submoduleMap K
  let R' := R.comp eK.symm.toLinearMap
  have hb' : ∀ j, (eK (b j)).val = (B.map (Rat.castHom ℝ)).col j := hb
  have hR' : ∀ j, R' (eK (b j)) ∈ realDenominatorGrid n := by
    intro j
    simpa only [R', LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.symm_apply_apply] using hR j
  obtain ⟨m, hm, hmp, split', hsplit', hnorm, hgrid⟩ :=
    exists_controlled_kernel_split (U.map e.toLinearMap) (K.map e.toLinearMap)
      A B hAspan hBspan (fun j => eK (b j)) hb' R' n hR' hJ hl hA hB hp hι hcols hJp hlp
  let split : H →ₗ[ℝ] K := eK.symm.toLinearMap.comp (split'.comp e.toLinearMap)
  have hsplit (x : H) : e (split x).val = (split' (e x)).val :=
    congrArg Subtype.val (eK.apply_symm_apply (split' (e x)))
  refine ⟨m, hm, hmp, split, ?_, ?_, ?_⟩
  · intro x hx
    have hex : e x ∈ U.map e.toLinearMap ⊔ K.map e.toLinearMap := by
      rw [← Submodule.map_sup]
      exact ⟨x, hx, rfl⟩
    have hmem : e (x - (split x).val) ∈ U.map e.toLinearMap := by
      rw [map_sub, hsplit]
      exact hsplit' (e x) hex
    simpa only [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply] using hmem
  · intro x
    rw [hsplit]
    exact hnorm (e x)
  · intro x hx
    exact hgrid (e x) hx

end Erdos3

end

end OAI

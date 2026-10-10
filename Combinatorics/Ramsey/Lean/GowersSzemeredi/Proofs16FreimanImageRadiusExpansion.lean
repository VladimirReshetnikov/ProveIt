import GowersSzemeredi.Proofs16BoundedImageRemoveFrequencies

/-! A small image on a small Bohr domain controls the entire original
Freiman domain. Residue-cell differences stay in the small domain; within
each cell, the Freiman equation translates its image. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Preserve the full original radius, at an explicit residue-cell cost. -/
theorem freiman_image_expand_radius_cells {N M K : Nat} [NeZero N] [NeZero M]
    (T : Finset (ZMod N)) (f : ZMod N → ZMod N) {rho r : Real}
    (hrho : 0 ≤ rho) (hrle : r ≤ rho) (hcell : 1 ≤ r*(M : Real))
    (hf : IsFreimanLinearOn (bohr T rho) f) (hsmall : ((bohr T r).image f).card ≤ K) :
    ((bohr T rho).image f).card ≤ M^T.card*K := by
  classical
  let sig : ZMod N → T → Fin M := fun x t => dirichletCell M (t.1*x)
  let D := bohr T rho
  have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hMR : (0 : Real) < M := by exact_mod_cast NeZero.pos M
  have hdiff : ∀ x y : ZMod N, sig x=sig y → x-y ∈ bohr T r := by
    intro x y he
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun t ht => ?_⟩
    have hc := dirichletCell_close (congrFun he ⟨t,ht⟩)
    have hcR : (centeredAbs (t*x-t*y) : Real)*M < N := by exact_mod_cast hc
    have hclose : (centeredAbs (t*x-t*y) : Real) < N/M := (lt_div_iff₀ hMR).mpr hcR
    have hbound : (N : Real)/M ≤ r*N := by
      apply (div_le_iff₀ hMR).mpr
      nlinarith only [hcell,hNR]
    rw [mul_sub]
    exact hclose.le.trans hbound
  have h0 : (0 : ZMod N) ∈ D := zero_mem_bohr T hrho
  have hfib : ∀ s : T → Fin M, ((D.filter fun x => sig x=s).image f).card ≤ K := by
    intro s
    rcases (D.filter fun x => sig x=s).eq_empty_or_nonempty with he | hne
    · rw [he,Finset.image_empty,Finset.card_empty]
      exact Nat.zero_le _
    · obtain ⟨y,hy⟩ := hne
      have hyD := (Finset.mem_filter.mp hy).1
      have hySig := (Finset.mem_filter.mp hy).2
      have hsub : (D.filter fun x => sig x=s).image f ⊆
          ((bohr T r).image f).image (fun v => f y+v-f 0) := by
        intro v hv
        obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
        have hxD := (Finset.mem_filter.mp hx).1
        have hxSig := (Finset.mem_filter.mp hx).2
        have hxy := hdiff x y (hxSig.trans hySig.symm)
        have hxyD := bohr_mono_radius T hrle hxy
        have heq := hf x 0 y (x-y) hxD h0 hyD hxyD (by ring)
        refine Finset.mem_image.mpr ⟨f (x-y),Finset.mem_image_of_mem f hxy,?_⟩
        linear_combination -heq
      exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans hsmall)
  have hcover : D.image f ⊆ Finset.univ.biUnion fun s : T → Fin M => (D.filter fun x => sig x=s).image f := by
    intro v hv
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_biUnion.mpr ⟨sig x,Finset.mem_univ _,Finset.mem_image.mpr
      ⟨x,Finset.mem_filter.mpr ⟨hx,rfl⟩,rfl⟩⟩
  calc (D.image f).card ≤ (Finset.univ.biUnion fun s : T → Fin M => (D.filter fun x => sig x=s).image f).card :=
      Finset.card_le_card hcover
    _ ≤ ∑ s : T → Fin M, ((D.filter fun x => sig x=s).image f).card := Finset.card_biUnion_le
    _ ≤ ∑ _s : T → Fin M, K := Finset.sum_le_sum fun s _ => hfib s
    _ = M^T.card*K := by simp [Fintype.card_fun]

/-- An explicit expansion factor linear in the original image cap. -/
theorem freiman_image_expand_radius {N d K : Nat} [NeZero N]
    (T : Finset (ZMod N)) (f : ZMod N → ZMod N) {rho r : Real}
    (hr : 0 < r) (hrle : r ≤ rho) (hT : T.card ≤ d)
    (hf : IsFreimanLinearOn (bohr T rho) f) (hsmall : ((bohr T r).image f).card ≤ K) :
    ((bohr T rho).image f).card ≤ (refinementCells r)^d*K := by
  have hM : 0 < refinementCells r := Nat.ceil_pos.mpr (by positivity)
  letI : NeZero (refinementCells r) := ⟨ne_of_gt hM⟩
  have hceil : 1/r ≤ (refinementCells r : Real) := Nat.le_ceil _
  have hcell : 1 ≤ r*(refinementCells r : Real) := by
    rw [div_le_iff₀ hr] at hceil
    simpa only [mul_comm] using hceil
  exact (freiman_image_expand_radius_cells T f (hr.le.trans hrle) hrle hcell hf hsmall).trans
    (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hM hT))

end LeanProofs.GowersSzemeredi

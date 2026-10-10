import GowersSzemeredi.Proofs16ChartFrequencyDomains
import GowersSzemeredi.Proofs16RowLabelSelection
import GowersSzemeredi.Proofs16RecenteredQuadruples

/-! Complete and recenter a good quadruple family onto one coherent Bohr domain.
Four cell classes are chosen for the already-good quadruples, preserving
active-domain tests. The original domains need not have a common intersection. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical
open scoped BigOperators

/-- Coherent chart localization from actual linear parts and active tests.
The cell and row-label losses are explicit; all retained quadruples still
come from the original good family. -/
theorem coherent_chart_localization {N M ell : Nat} [NeZero N] [NeZero M]
    (Q : Finset (Fin 4 → ZMod N)) (X Gamma B : Finset (ZMod N))
    (D : Fin ell → Finset (ZMod N)) (S : ZMod N → Finset (Fin ell))
    (theta psi : Fin ell → ZMod N → ZMod N) (F : ZMod N → ZMod N → ZMod N)
    {rho eta kappa : Real} (hr : 0 < rho) (heta : 0 ≤ eta) (hk : 0 < kappa)
    (hcell : 1 ≤ (rho/4)*M)
    (hpsi : ∀ i, IsFreimanLinearOn (bohr Gamma rho) (psi i) ∧ psi i 0 = 0)
    (hdiff : ∀ i, ∀ a ∈ D i, ∀ b ∈ D i, theta i a-theta i b = psi i (a-b))
    (hactive : ∀ x ∈ X, ∀ i ∈ S x, x ∈ D i)
    (hlocal : ∀ x ∈ X, IsFreimanLinearOn (bohr (B ∪ (S x).image fun i => theta i x) eta) (F x) ∧ F x 0 = 0)
    (hquad : ∀ q ∈ Q, q 0+q 1 = q 2+q 3 ∧ (∀ j, q j ∈ X) ∧
      ∀ z, (∀ j, z ∈ bohr (B ∪ (S (q j)).image fun i => theta i (q j)) eta) →
        F (q 0) z+F (q 1) z = F (q 2) z+F (q 3) z)
    (hmass : kappa*(N : Real)^3 ≤ Q.card)
    (hN : 8 ≤ (kappa/(M : Real)^(4*Gamma.card))*N) :
    ∃ (t : Fin 4 → ZMod N) (color : ZMod N → Fin 4) (V : Finset (ZMod N))
      (R : Finset (Fin 4 → ZMod N)) (B' : Finset (ZMod N)),
      t ∈ Q ∧ B ⊆ B' ∧ B'.card ≤ B.card+4*ell ∧ V ⊆ bohr Gamma (rho/4) ∧
      (kappa/(512*(M : Real)^(4*Gamma.card)))*N ≤ (V.card : Real) ∧
      (kappa/(512*(M : Real)^(4*Gamma.card)))*(N : Real)^3 ≤ R.card ∧
      (∀ i, FreimanHom 2 (bohr Gamma rho) (psi i) ∧ psi i 0 = 0) ∧
      (∀ u ∈ V, t (color u)+u ∈ X ∧
        IsFreimanLinearOn (freimanFrequencyBohr B' psi (eta/2) u) (F (t (color u)+u)) ∧
        F (t (color u)+u) 0 = 0) ∧
      ∀ b ∈ R, b 0+b 1 = b 2+b 3 ∧ Function.Injective b ∧
        (∀ j, b j ∈ V ∧ color (b j) = j) ∧ (fun j => t j+b j) ∈ Q ∧
        ∀ z, (∀ j, z ∈ freimanFrequencyBohr B' psi (eta/2) (b j)) →
          F (t (color (b 0))+b 0) z+F (t (color (b 1))+b 1) z =
            F (t (color (b 2))+b 2) z+F (t (color (b 3))+b 3) z := by
  have hMR : (0 : Real) < M := by exact_mod_cast NeZero.pos M
  have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  let delta := kappa/(M : Real)^(4*Gamma.card)
  have hd : 0 < delta := by dsimp only [delta]; positivity
  obtain ⟨s,hcount⟩ := exists_quadruple_chart_cells (M := M) Gamma Q
  let C : Fin 4 → Finset (ZMod N) := fun j => chartCell Gamma (s j)
  let Qs := Q.filter fun q => ∀ j, q j ∈ C j
  have hQs : delta*(N : Real)^3 ≤ (Qs.card : Real) := by
    have hc : (Q.card : Real) ≤ (M : Real)^(4*Gamma.card)*Qs.card := by exact_mod_cast hcount
    dsimp only [delta]
    rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity)]
    simpa only [mul_comm] using hmass.trans hc
  have hQsne : Qs.Nonempty := Finset.card_pos.mp (by
    exact_mod_cast (show 0 < delta*(N : Real)^3 by positivity).trans_le hQs)
  obtain ⟨t,ht⟩ := hQsne
  have htQ : t ∈ Q := (Finset.mem_filter.mp ht).1
  have htC : ∀ j, t j ∈ C j := (Finset.mem_filter.mp ht).2
  have htadd := (hquad t htQ).1
  let A := recenteredQuadruples Qs t
  have hrealize : ∀ b ∈ A, b 0+b 1 = b 2+b 3 ∧
      (∀ j, b j ∈ bohr Gamma (rho/4)) ∧ (fun j => t j+b j) ∈ Qs := by
    intro b hb
    have hq := (mem_recenteredQuadruples Qs t b).mp hb
    obtain ⟨hqQ,hqC⟩ := Finset.mem_filter.mp hq
    refine ⟨?_,?_,hq⟩
    · have he := (hquad _ hqQ).1
      linear_combination he-htadd
    · intro j
      have hdiffC := chart_cell_difference_mem Gamma (s j) hcell (hqC j) (htC j)
      simpa only [add_sub_cancel_left] using hdiffC
  have hA : delta*(N : Real)^3 ≤ A.card := by
    simpa only [A,recenteredQuadruples_card] using hQs
  obtain ⟨color,R,hRA,hRmass,hlabels⟩ := exists_dense_quadruple_row_labels A
    (fun b hb => (hrealize b hb).1) hA hN
  let V := Finset.univ.biUnion fun j : Fin 4 => R.image (fun b => b j)
  let B' := chartFixedFrequencies B C D theta psi t
  have hmem : ∀ b ∈ R, ∀ j, b j ∈ V := by
    intro b hb j
    exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,Finset.mem_image_of_mem _ hb⟩
  have hsource : ∀ u ∈ V, u ∈ bohr Gamma (rho/4) ∧ t (color u)+u ∈ X ∧
      t (color u)+u ∈ C (color u) := by
    intro u hu
    obtain ⟨j,-,hj⟩ := Finset.mem_biUnion.mp hu
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hj
    have hbr := hrealize b (hRA hb)
    have hqQ := (Finset.mem_filter.mp hbr.2.2).1
    have hqC := (Finset.mem_filter.mp hbr.2.2).2
    rw [(hlabels b hb).2 j]
    exact ⟨hbr.2.1 j,(hquad _ hqQ).2.1 j,hqC j⟩
  have hclose : ∀ j, ∀ x ∈ C j, ∀ y ∈ C j, x-y ∈ bohr Gamma rho := by
    intro j x hx y hy
    exact bohr_mono_radius _ (by linarith) (chart_cell_difference_mem Gamma (s j) hcell hx hy)
  have hsub : ∀ j x, x ∈ C j → x ∈ X →
      freimanFrequencyBohr B' psi (eta/2) (x-t j) ⊆ bohr (B ∪ (S x).image fun i => theta i x) eta :=
    fun j x hx hXx => chart_frequency_bohr_subset_active B Gamma C D S theta psi t hr.le heta
      hpsi hdiff hclose htC j hx (hactive x hXx)
  have hVmass : (delta/512)*N ≤ (V.card : Real) := by
    have hrow := additive_quadruples_row_density R (fun b hb => (hrealize b (hRA hb)).1) hRmass 0
    have hrowV : anchorRowSupport R 0 ⊆ V := by
      intro u hu
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hu
      exact hmem b hb 0
    exact hrow.trans (Nat.cast_le.mpr (Finset.card_le_card hrowV))
  have hdEq : delta/512 = kappa/(512*(M : Real)^(4*Gamma.card)) := by dsimp only [delta]; ring
  refine ⟨t,color,V,R,B',htQ,Finset.subset_union_left,chart_fixed_frequencies_card B C D theta psi t,
    fun u hu => (hsource u hu).1,?_,?_,?_,?_,?_⟩
  · simpa only [← hdEq] using hVmass
  · simpa only [← hdEq] using hRmass
  · intro i
    exact ⟨freiman_hom_two_of_chart_linear _ _ (hpsi i).1,(hpsi i).2⟩
  · intro u hu
    have hs := hsource u hu
    have hl := hlocal _ hs.2.1
    have hsDom := hsub (color u) (t (color u)+u) hs.2.2 hs.2.1
    simp only [add_sub_cancel_left] at hsDom
    exact ⟨hs.2.1,hl.1.mono hsDom,hl.2⟩
  · intro b hb
    have hbr := hrealize b (hRA hb)
    have hqQ := (Finset.mem_filter.mp hbr.2.2).1
    have hqC := (Finset.mem_filter.mp hbr.2.2).2
    refine ⟨hbr.1,(hlabels b hb).1,fun j => ⟨hmem b hb j,(hlabels b hb).2 j⟩,hqQ,?_⟩
    intro z hz
    simp only [(hlabels b hb).2]
    apply (hquad _ hqQ).2.2 z
    intro j
    have hsubj := hsub j (t j+b j) (hqC j) ((hquad _ hqQ).2.1 j)
    simp only [add_sub_cancel_left] at hsubj
    exact hsubj (hz j)

end LeanProofs.GowersSzemeredi

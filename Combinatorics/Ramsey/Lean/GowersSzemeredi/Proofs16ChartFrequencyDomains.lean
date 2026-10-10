import GowersSzemeredi.Proofs16SandersChartCells
import GowersSzemeredi.Proofs16CoherentTranslationLocalization

/-! Recenter completed charts without losing active frequency constraints.
The cell offsets become a fixed frequency base; the common linear parts
supply the varying frequencies on the recentered Bohr domain. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical
open scoped BigOperators

def chartFixedFrequencies {N ell : Nat} (B : Finset (ZMod N))
    (C : Fin 4 → Finset (ZMod N)) (D : Fin ell → Finset (ZMod N))
    (theta psi : Fin ell → ZMod N → ZMod N) (t : Fin 4 → ZMod N) : Finset (ZMod N) :=
  B ∪ Finset.univ.biUnion fun j : Fin 4 => Finset.univ.image fun i : Fin ell =>
    affineChartCompletion (C j) (D i) (theta i) (psi i) (t j) (t j)

theorem chart_fixed_frequencies_card {N ell : Nat} (B : Finset (ZMod N))
    (C : Fin 4 → Finset (ZMod N)) (D : Fin ell → Finset (ZMod N))
    (theta psi : Fin ell → ZMod N → ZMod N) (t : Fin 4 → ZMod N) :
    (chartFixedFrequencies B C D theta psi t).card ≤ B.card+4*ell := by
  apply (Finset.card_union_le _ _).trans
  apply Nat.add_le_add_left
  apply Finset.card_biUnion_le.trans
  calc (∑ j : Fin 4, (Finset.univ.image fun i : Fin ell =>
      affineChartCompletion (C j) (D i) (theta i) (psi i) (t j) (t j)).card) ≤ ∑ _j : Fin 4, ell :=
        Finset.sum_le_sum fun j _ => Finset.card_image_le.trans (by simp [Fintype.card_fin])
    _ = _ := by simp [Fintype.card_fin]

/-- The completed chart frequency domain implies all active original
constraints at the translated point, and keeps the original fixed base. -/
theorem chart_frequency_bohr_subset_active {N ell : Nat} [NeZero N]
    (B Gamma : Finset (ZMod N)) (C : Fin 4 → Finset (ZMod N))
    (D : Fin ell → Finset (ZMod N)) (S : ZMod N → Finset (Fin ell))
    (theta psi : Fin ell → ZMod N → ZMod N) (t : Fin 4 → ZMod N)
    {rho eta : Real} (hr : 0 ≤ rho) (heta : 0 ≤ eta)
    (hpsi : ∀ i, IsFreimanLinearOn (bohr Gamma rho) (psi i) ∧ psi i 0 = 0)
    (hdiff : ∀ i, ∀ a ∈ D i, ∀ b ∈ D i, theta i a-theta i b = psi i (a-b))
    (hclose : ∀ j, ∀ a ∈ C j, ∀ b ∈ C j, a-b ∈ bohr Gamma rho)
    (ht : ∀ j, t j ∈ C j) (j : Fin 4) {x : ZMod N} (hx : x ∈ C j)
    (hactive : ∀ i ∈ S x, x ∈ D i) :
    freimanFrequencyBohr (chartFixedFrequencies B C D theta psi t) psi (eta/2) (x-t j) ⊆
      bohr (B ∪ (S x).image fun i => theta i x) eta := by
  intro z hz
  have hm := (Finset.mem_filter.mp hz).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun r hrmem => ?_⟩
  rcases Finset.mem_union.mp hrmem with hrB | hrS
  · have hbase : r ∈ chartFixedFrequencies B C D theta psi t ∪
        Finset.univ.image (fun i => psi i (x-t j)) :=
      Finset.mem_union_left _ (Finset.mem_union_left _ hrB)
    have h := hm r hbase
    exact h.trans (mul_le_mul_of_nonneg_right (by linarith : eta/2 ≤ eta) (Nat.cast_nonneg N))
  · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hrS
    let offset := affineChartCompletion (C j) (D i) (theta i) (psi i) (t j) (t j)
    have hpoint : theta i x = offset+psi i (x-t j) := by
      have he := affine_chart_completion_agree (C j) (D i) (theta i) (psi i) (t j)
        (hdiff i) hx (hactive i hi)
      have he' := affine_chart_completion_translate (C j) (D i) Gamma (theta i) (psi i)
        (ht j) hx (ht j) hr (hpsi i).1 (hpsi i).2 (hclose j)
      exact he.symm.trans he'
    have ho : offset ∈ chartFixedFrequencies B C D theta psi t ∪
        Finset.univ.image (fun i => psi i (x-t j)) := by
      refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
      exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,
        Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
    have hp : psi i (x-t j) ∈ chartFixedFrequencies B C D theta psi t ∪
        Finset.univ.image (fun i => psi i (x-t j)) :=
      Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    have hoB := hm offset ho
    have hpB := hm (psi i (x-t j)) hp
    have haddR : (centeredAbs (offset*z+psi i (x-t j)*z) : Real) ≤
        centeredAbs (offset*z)+centeredAbs (psi i (x-t j)*z) := by
      exact_mod_cast centeredAbs_add_le (offset*z) (psi i (x-t j)*z)
    rw [hpoint,add_mul]
    linarith only [haddR,hoB,hpB]

/-- The common local linear part has the native order-two interface. -/
theorem freiman_hom_two_of_chart_linear {N : Nat} (A : Finset (ZMod N))
    (psi : ZMod N → ZMod N) (h : IsFreimanLinearOn A psi) : FreimanHom 2 A psi := by
  exact isAddFreimanHom_two.mpr ⟨Set.mapsTo_univ _ _,fun a ha b hb c hc d hd he => h a b c d ha hb hc hd he⟩

end LeanProofs.GowersSzemeredi

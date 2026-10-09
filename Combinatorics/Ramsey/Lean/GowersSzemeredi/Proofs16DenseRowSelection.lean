import GowersSzemeredi.Proofs16SelectedRowBohr

/-! Dense rows of the original set give a bounded family of Freiman maps
whose values define Bohr sets in its directional differences for almost all
triples. All parameters here depend only on the density and error. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- A fixed Dirichlet cell count suffices for the row Bogolyubov radius. -/
theorem rowBohr_cell_count : (2 : Real) ≤ (1 / (8 * Real.pi)) * 64 := by
  rw [show (1 / (8 * Real.pi)) * 64 = 64 / (8 * Real.pi) by ring]
  apply (le_div_iff₀ (by positivity)).mpr
  have := Real.pi_lt_four
  linarith

def denseRowAlphabetBound (delta : Real) : Nat :=
  (2 * directionalQuarterSpanCutoff ⌈16 * delta ^ (-(2 : Real))⌉₊ 64
    (1 / (8 * Real.pi)) + 1) ^ ⌈16 * delta ^ (-(2 : Real))⌉₊

theorem denseRowAlphabetBound_pos (delta : Real) : 0 < denseRowAlphabetBound delta := by
  unfold denseRowAlphabetBound
  positivity

/-- Select dense order-eight Freiman pieces from the dense-row alphabets.
For every nonexceptional triple with its four rows in Y, the Bohr set of
at most 4m selected values lies in the four-step directional difference.
The selected maps retain their quantitative Bohr extensions. -/
theorem dense_row_selected_bohr {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) (Y : Finset (ZMod N))
    {delta epsilon : Real} (hdelta : 0 < delta) (heps : 0 < epsilon)
    (hdense : ∀ y ∈ Y, delta ≤ (rowOf A y).card / (N : Real))
    (hN : 8 / epsilon ≤ (N : Real)) :
    ∃ (m : Nat) (E : Fin m → Finset (ZMod N)) (L : Fin m → ZMod N → ZMod N)
      (S : Fin m → Finset (ZMod N)) (T : Finset (ZMod N × ZMod N × ZMod N)),
      (m : Real) * corollary20Kappa (epsilon / 2) (denseRowAlphabetBound delta) ≤
        denseRowAlphabetBound delta - 1 ∧
      (∀ i, FreimanHom 8 (E i) (L i) ∧
        corollary20Kappa (epsilon / 2) (denseRowAlphabetBound delta) * N ≤ (E i).card ∧
        ((S i).card : Real) ≤ 16 *
          (corollary20Kappa (epsilon / 2) (denseRowAlphabetBound delta)) ^ (-(2 : Real)) ∧
        IsBHomomorphism (E i) (bohr (S i)
          (corollary20Kappa (epsilon / 2) (denseRowAlphabetBound delta) / (32 * Real.pi))) (L i)) ∧
      (T.card : Real) < epsilon * (N : Real)^3 ∧
      (∀ y z w, (selectedTripleFrequencies L y z w).card ≤ 4 * m) ∧
      ∀ y z w : ZMod N, (y, z, w) ∉ T → y + z ∈ Y → z ∈ Y → y + w ∈ Y → w ∈ Y →
        ∀ d ∈ bohr (selectedTripleFrequencies L y z w) (1 / 16),
          (d, y) ∈ horDiff (verDiff (horDiff (horDiff A))) := by
  obtain ⟨U, hU, hgeom⟩ := dense_row_directional_alphabets_quarter A Y hdelta hdense 64 rowBohr_cell_count
  have hK1 : 1 ≤ denseRowAlphabetBound delta := denseRowAlphabetBound_pos delta
  obtain ⟨m, E, L, S, hm, hE, hbad⟩ := corollary20_bohr_all_triples_budget U
    (fun y => (hU y).1) hK1 (fun y => (hU y).2) heps hN
  let T := Finset.univ.filter fun t => ∃ v, BadWitness U E L t v
  refine ⟨m, E, L, S, T, hm, ?_, hbad, selectedTripleFrequencies_card_le L, ?_⟩
  · intro i
    obtain ⟨hf, hcard, hmem, hs, hhom⟩ := hE i
    exact ⟨hf, hcard, hs, hhom⟩
  · intro y z w ht hyz hz hyw hw d hd
    have hgood : ¬ ∃ v, BadWitness U E L (y, z, w) v := by
      intro h
      exact ht (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    exact hgeom y z w d hyz hz hyw hw (bohr_selectedTriple_subset_common U E L y z w hgood hd)

end LeanProofs.GowersSzemeredi

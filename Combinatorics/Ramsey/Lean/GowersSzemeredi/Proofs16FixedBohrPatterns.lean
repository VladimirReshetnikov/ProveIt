import GowersSzemeredi.Proofs16PatternBohrContainment
import GowersSzemeredi.Proofs16DenseRowSelection

/-! Fixed small index patterns with their domain constraints and the
Bohr containment needed for the next structural step. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem exists_fixed_bohr_patterns {N m : Nat} [NeZero N]
    (Gamma : ZMod N → Finset (ZMod N)) (r R : Nat) (hGamma : ∀ y, (Gamma y).card ≤ r)
    (E : Fin m → Finset (ZMod N)) (L : Fin m → ZMod N → ZMod N)
    (Y : Finset (ZMod N)) {beta epsilon : Real} (hbeta : 0 ≤ beta) (hY : beta * N ≤ Y.card)
    (hbad : ((Finset.univ.filter fun t => ∃ v, BadWitness (rowSpanAlphabet Gamma R) E L t v).card : Real)
      ≤ epsilon * (N : Real)^3) :
    ∃ (J : Fin 4 → Finset (Fin m)) (z w : ZMod N) (V : Finset (ZMod N)),
      (∀ i, (J i).card ≤ spanGeneratorBound r R) ∧
      (beta^4 - epsilon) * N ≤ ((m + 1 : Nat)^(4 * spanGeneratorBound r R) : Real) * V.card ∧
      ∀ y ∈ V, y + z ∈ Y ∧ z ∈ Y ∧ y + w ∈ Y ∧ w ∈ Y ∧
        (∀ i ∈ J 0, y + z ∈ E i) ∧ (∀ i ∈ J 1, z ∈ E i) ∧
        (∀ i ∈ J 2, y + w ∈ E i) ∧ (∀ i ∈ J 3, w ∈ E i) ∧
        bohr (patternFrequencies L J y z w) (1 / (16 * (max 1 (spanGeneratorBound r R) : Nat))) ⊆
          bohr (frequencyDifference (rowSpanAlphabet Gamma R (y + z)) (rowSpanAlphabet Gamma R z) ∩
            frequencyDifference (rowSpanAlphabet Gamma R (y + w)) (rowSpanAlphabet Gamma R w)) (1 / 4) := by
  choose I hI hactive hbohr using covered_values_small_bohr Gamma r R hGamma E L
  let B := Finset.univ.filter fun t => ∃ v, BadWitness (rowSpanAlphabet Gamma R) E L t v
  obtain ⟨J, z, w, V, hJ, hVcard, hV⟩ := exists_dense_fixed_index_patterns Y B I hI hbeta hY hbad
  refine ⟨J, z, w, V, hJ, hVcard, ?_⟩
  intro y hy
  obtain ⟨ht, h1, h2, h3, h4⟩ := hV y hy
  have hrows := (Finset.mem_filter.mp (Finset.mem_sdiff.mp ht).1).2
  have hgood : ¬ ∃ v, BadWitness (rowSpanAlphabet Gamma R) E L (y, z, w) v := by
    intro h
    exact (Finset.mem_sdiff.mp ht).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  refine ⟨hrows.1, hrows.2.1, hrows.2.2.1, hrows.2.2.2, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact (hactive (y + z) i (by simpa only [h1] using hi)).1
  · intro i hi
    exact (hactive z i (by simpa only [h2] using hi)).1
  · intro i hi
    exact (hactive (y + w) i (by simpa only [h3] using hi)).1
  · intro i hi
    exact (hactive w i (by simpa only [h4] using hi)).1
  · exact pattern_bohr_subset_common (rowSpanAlphabet Gamma R) E L I J hbohr y z w h1 h2 h3 h4 hgood

/-- Dense rows admit fixed small index patterns on a quantitatively dense
set of row parameters, with all evaluations in the selected domains. -/
theorem dense_row_fixed_bohr_patterns {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) (Y : Finset (ZMod N))
    {delta beta epsilon : Real} (hdelta : 0 < delta) (hbeta : 0 ≤ beta) (heps : 0 < epsilon)
    (hdense : ∀ y ∈ Y, delta ≤ (rowOf A y).card / (N : Real))
    (hY : beta * N ≤ Y.card) (hN : 8 / epsilon ≤ (N : Real)) :
    let r := ⌈16 * delta ^ (-(2 : Real))⌉₊
    let R := directionalQuarterSpanCutoff r 64 (1 / (8 * Real.pi))
    let ell := spanGeneratorBound r R
    let K := denseRowAlphabetBound delta
    let kappa := corollary20Kappa (epsilon / 2) K
    ∃ (m : Nat) (E : Fin m → Finset (ZMod N)) (L : Fin m → ZMod N → ZMod N)
      (S : Fin m → Finset (ZMod N)) (J : Fin 4 → Finset (Fin m))
      (z w : ZMod N) (V : Finset (ZMod N)),
      (m : Real) * kappa ≤ K - 1 ∧
      (∀ i, FreimanHom 8 (E i) (L i) ∧ kappa * N ≤ (E i).card ∧
        ((S i).card : Real) ≤ 16 * kappa ^ (-(2 : Real)) ∧
        IsBHomomorphism (E i) (bohr (S i) (kappa / (32 * Real.pi))) (L i)) ∧
      (∀ i, (J i).card ≤ ell) ∧
      (beta^4 - epsilon) * N ≤ ((m + 1 : Nat)^(4 * ell) : Real) * V.card ∧
      (∀ y, (patternFrequencies L J y z w).card ≤ 4 * ell) ∧
      ∀ y ∈ V, (∀ i ∈ J 0, y + z ∈ E i) ∧ (∀ i ∈ J 1, z ∈ E i) ∧
        (∀ i ∈ J 2, y + w ∈ E i) ∧ (∀ i ∈ J 3, w ∈ E i) ∧
        ∀ d ∈ bohr (patternFrequencies L J y z w) (1 / (16 * (max 1 ell : Nat))),
          (d, y) ∈ horDiff (verDiff (horDiff (horDiff A))) := by
  let r := ⌈16 * delta ^ (-(2 : Real))⌉₊
  let R := directionalQuarterSpanCutoff r 64 (1 / (8 * Real.pi))
  let K := denseRowAlphabetBound delta
  obtain ⟨Gamma, hGamma, hrows⟩ := dense_row_spectra A Y hdelta hdense
  let U := rowSpanAlphabet Gamma R
  have hU := rowSpanAlphabet_bounds Gamma r R hGamma
  have hK1 : 1 ≤ K := denseRowAlphabetBound_pos delta
  obtain ⟨m, E, L, S, hm, hE, hbad⟩ := corollary20_bohr_all_triples_budget U
    (fun y => (hU y).1) hK1 (fun y => (hU y).2) heps hN
  obtain ⟨J, z, w, V, hJ, hVcard, hV⟩ := exists_fixed_bohr_patterns Gamma r R hGamma E L Y hbeta hY hbad.le
  refine ⟨m, E, L, S, J, z, w, V, hm, ?_, hJ, hVcard,
    fun y => patternFrequencies_card_le L J hJ y z w, ?_⟩
  · intro i
    obtain ⟨hf, hcard, hmem, hs, hhom⟩ := hE i
    exact ⟨hf, hcard, hs, hhom⟩
  · intro y hy
    obtain ⟨hyz, hz, hyw, hw, h1, h2, h3, h4, hbohr⟩ := hV y hy
    refine ⟨h1, h2, h3, h4, ?_⟩
    intro d hd
    exact directional_bohr_span_quarter (horDiff (horDiff A)) Y Gamma r 64 hGamma
      (by positivity) (by have := Real.pi_gt_three; rw [div_lt_one (by positivity)]; linarith)
      rowBohr_cell_count hrows y z w d hyz hz hyw hw (hbohr hd)

end LeanProofs.GowersSzemeredi

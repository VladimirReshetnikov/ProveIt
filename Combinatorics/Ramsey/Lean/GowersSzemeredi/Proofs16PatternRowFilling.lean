import GowersSzemeredi.Proofs16PatternMissingRows
import GowersSzemeredi.Proofs16WeightedBohrFilling

/-! The final horizontal filling step under explicit graph regularity,
representation density, and error-budget hypotheses. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem pattern_row_filled_rank {N m Q r : Nat} [NeZero N] [NeZero Q]
    (A : Finset (ZMod N × ZMod N)) (W C T F : Finset (ZMod N))
    (psi : Fin m → ZMod N → ZMod N) (J : Fin 4 → Finset (Fin m)) (a y : ZMod N)
    {rho eta delta epsilon tau : Real} (hrho : 0 ≤ rho) (heta : 0 < eta) (hC : C.Nonempty)
    (hd0 : 0 < delta) (hd1 : delta ≤ 1) (heps : 0 ≤ epsilon) (htau : 0 < tau)
    (hW : W ⊆ bohr T (rho / 4))
    (hpsi : ∀ i ∈ J 0 ∪ J 2, FreimanHom 2 (bohr T rho) (psi i) ∧ psi i 0 = 0)
    (hgeom : ∀ t ∈ W, ∀ d ∈ bohr F eta,
      d ∈ bohr (varyingPatternFrequencies psi J t) eta → (d, a + t) ∈ A)
    (hbox : boxSum (fun (d : ↥(bohr F eta)) (t : ↥C) =>
        edgeIndicator (patternEdge psi J (eta / 4)) d t - delta) ≤
      epsilon^4 * ((bohr F eta).card : Real)^2 * (C.card : Real)^2)
    (hM : tau * (C.card : Real)^3 ≤
      ((patternRepresentationTriples W C y).card : Real))
    (hK : (F ∪ varyingPatternFrequencies psi J y).card ≤ r) (hQ : 4 ≤ eta * Q)
    (hbudget : (4 : Real)^(r + 1) * (12 * epsilon) * (Q : Real)^r ≤ (delta^3 * tau)^2) :
    ∀ d ∈ bohr (F ∪ varyingPatternFrequencies psi J y) (eta / 4 / 2),
      (d, y) ∈ horDiff (verDiff (verDiff A)) := by
  have hmissing := pattern_missing_row_bound A W C T F psi J a y hrho heta.le hC
    hd0.le hd1 heps htau.le hW hpsi hgeom hbox hM
  have hbase : ((bohr F eta).card : Real) ≤ N := by
    exact_mod_cast (show (bohr F eta).card ≤ N by simpa using Finset.card_le_univ (bohr F eta))
  have hmissing' : (((bohr (F ∪ varyingPatternFrequencies psi J y) (eta / 4)) \
      rowOf (verDiff (verDiff A)) y).card : Real) * (delta^3 * tau)^2 ≤ (12 * epsilon) * N := by
    exact hmissing.trans (mul_le_mul_of_nonneg_left hbase (by positivity))
  intro d hd
  obtain ⟨x, hx, z, hz, heq⟩ := bohr_weighted_defect_sub_cover_rank
    (F ∪ varyingPatternFrequencies psi J y) (rowOf (verDiff (verDiff A)) y)
    (show 0 < eta / 4 by positivity) (show 0 < (delta^3 * tau)^2 by positivity)
    (show 0 ≤ 12 * epsilon by positivity) hK (show 1 ≤ eta / 4 * Q by linarith)
    hmissing' hbudget d hd
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, z,
    (Finset.mem_filter.mp hx).2, (Finset.mem_filter.mp hz).2, heq⟩

end LeanProofs.GowersSzemeredi

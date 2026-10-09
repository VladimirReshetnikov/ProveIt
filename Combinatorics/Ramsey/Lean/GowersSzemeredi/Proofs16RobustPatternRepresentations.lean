import GowersSzemeredi.Proofs16CorrelationWitnessCount
import GowersSzemeredi.Proofs16ProperBohrProgression

/-! Actual plentiful witnesses for the seven-operator argument. The density
is measured in the ambient cyclic group, so these are classical polynomial
rank bounds, without a claim of quasipolynomial dependence. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- A containing class loses no witnesses. The ambient density supplies a
uniform representation density relative to the cube of that class. -/
theorem robust_pattern_representations {N : Nat} [NeZero N]
    (W C : Finset (ZMod N)) (hWC : W ⊆ C) {alpha : Real} (ha : 0 < alpha)
    (hcard : (W.card : Real) = alpha * N) :
    let S := commonLargeSpectrum W W (Real.sqrt (alpha^3) / 4)
    (S.card : Real) ≤ 16 / alpha^2 ∧
      ∀ d ∈ bohr S (1 / (4 * Real.pi)),
        alpha^4 / 4 * (C.card : Real)^3 ≤
          ((patternRepresentationTriples W C d).card : Real) := by
  obtain ⟨hS, hcount⟩ := robust_self_correlation W ha hcard
  refine ⟨hS, fun d hd => ?_⟩
  have hC : (C.card : Real) ≤ N := by
    exact_mod_cast (show C.card ≤ N by simpa using Finset.card_le_univ C)
  have hpow := pow_le_pow_left₀ (show (0 : Real) ≤ C.card by positivity) hC 3
  have h := mul_le_mul_of_nonneg_left hpow (show 0 ≤ alpha^4 / 4 by positivity)
  have hc := hcount d hd
  rw [mixed_self_correlation_norm_eq_pattern_card W C hWC] at hc
  nlinarith only [h, hc]

/-- Retain the ratio of ambient volume to the graph's right-hand class. -/
def robustRepresentationDensity {N : Nat} (alpha : Real) (C : Finset (ZMod N)) : Real :=
  alpha^4 * (N : Real)^3 / (4 * (C.card : Real)^3)

theorem robustRepresentationDensity_pos {N : Nat} [NeZero N]
    {alpha : Real} (ha : 0 < alpha) (C : Finset (ZMod N)) (hC : C.Nonempty) :
    0 < robustRepresentationDensity alpha C := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hcard : (0 : Real) < C.card := by exact_mod_cast hC.card_pos
  unfold robustRepresentationDensity
  positivity

/-- Keeping the actual class size improves the coarse density by (N/|C|)^3. -/
theorem robustRepresentationDensity_ge {N : Nat} [NeZero N]
    (alpha : Real) (C : Finset (ZMod N)) (hC : C.Nonempty) :
    alpha^4 / 4 ≤ robustRepresentationDensity alpha C := by
  have hcard : (0 : Real) < C.card := by exact_mod_cast hC.card_pos
  have hCN : (C.card : Real) ≤ N := by
    exact_mod_cast (show C.card ≤ N by simpa using Finset.card_le_univ C)
  have hp := pow_le_pow_left₀ hcard.le hCN 3
  unfold robustRepresentationDensity
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith only [mul_le_mul_of_nonneg_left hp (show 0 ≤ alpha^4 by positivity)]

/-- The sharper witness density retains the ambient cubic count exactly. -/
theorem robust_pattern_representations_exact {N : Nat} [NeZero N]
    (W C : Finset (ZMod N)) (hWC : W ⊆ C) {alpha : Real} (ha : 0 < alpha)
    (hcard : (W.card : Real) = alpha * N) :
    let S := commonLargeSpectrum W W (Real.sqrt (alpha^3) / 4)
    (S.card : Real) ≤ 16 / alpha^2 ∧
      ∀ d ∈ bohr S (1 / (4 * Real.pi)),
        robustRepresentationDensity alpha C * (C.card : Real)^3 ≤
          ((patternRepresentationTriples W C d).card : Real) := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hWpos : (0 : Real) < W.card := by rw [hcard]; positivity
  have hCpos : (0 : Real) < C.card :=
    hWpos.trans_le (by exact_mod_cast Finset.card_le_card hWC)
  obtain ⟨hS, hcount⟩ := robust_self_correlation W ha hcard
  refine ⟨hS, fun d hd => ?_⟩
  have h := hcount d hd
  rw [mixed_self_correlation_norm_eq_pattern_card W C hWC] at h
  have heq : robustRepresentationDensity alpha C * (C.card : Real)^3 =
      alpha^4 * (N : Real)^3 / 4 := by
    unfold robustRepresentationDensity
    field_simp
  rw [heq]
  exact h

/-- The entire representation Bohr set stays in the original map domain
when the dense set lies in a quarter-radius neighborhood. -/
theorem robust_representation_bohr_subset {N : Nat} [NeZero N]
    (W T : Finset (ZMod N)) {alpha rho : Real} (ha : 0 < alpha)
    (hcard : (W.card : Real) = alpha * N) (hW : W ⊆ bohr T (rho / 4)) :
    bohr (commonLargeSpectrum W W (Real.sqrt (alpha^3) / 4)) (1 / (4 * Real.pi)) ⊆
      bohr T rho := by
  intro d hd
  have h := (robust_self_correlation W ha hcard).2 d hd
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hpos : 0 < ‖mixedDifferenceCorrelation W W d‖ :=
    lt_of_lt_of_le (by positivity) h
  obtain ⟨a, haW, b, hbW, c, hcW, e, heW, heq⟩ :=
    mixedDifferenceCorrelation_representation W W d (norm_pos_iff.mp hpos)
  have hdB := bohr_four_term_mem T (hW haW) (hW hcW) (hW hbW) (hW heW)
  convert hdB using 1
  rw [heq]
  ring

/-- A proper symmetric progression of target parameters carries the robust
witness bound throughout and remains in the domain of the original maps. -/
theorem exists_proper_progression_with_many_representations {N : Nat} [NeZero N]
    (W C T : Finset (ZMod N)) (hWC : W ⊆ C) {alpha rho : Real} (ha : 0 < alpha)
    (hcard : (W.card : Real) = alpha * N) (hW : W ⊆ bohr T (rho / 4)) :
    ∃ S : Finset (ZMod N), ∃ Q : OAI.Erdos3.BohrProgression.CyclicCenteredGAP N,
      (S.card : Real) ≤ 16 / alpha^2 ∧ Q.rank ≤ S.card + 1 ∧ Q.Proper ∧
      0 ∈ Q.carrier ∧ (∀ x ∈ Q.carrier, -x ∈ Q.carrier) ∧
      Q.carrier ⊆ bohr T rho ∧
      Real.exp (-(((S.card : Real) + 1) * Real.log (1 + Real.pi) +
        10 * ((S.card : Real) + 1)^2)) * N ≤ Q.carrier.card ∧
      ∀ d ∈ Q.carrier, robustRepresentationDensity alpha C * (C.card : Real)^3 ≤
        ((patternRepresentationTriples W C d).card : Real) := by
  let S := commonLargeSpectrum W W (Real.sqrt (alpha^3) / 4)
  have hpos : 0 < (1 : Real) / Real.pi := by positivity
  have hw := logarithmic_bohr_width hpos
  have hw' : 0 ≤ Real.log (1 + Real.pi) ∧
      Real.exp (-Real.log (1 + Real.pi)) ≤ 1 / Real.pi := by simpa using hw
  obtain ⟨Q, hQR, hQproper, hQB, hQcard⟩ :=
    exists_proper_progression_in_bohr S hpos hw'.1 hw'.2
  have hQB' : Q.carrier ⊆ bohr S (1 / (4 * Real.pi)) := by
    convert hQB using 1
    congr 1
    ring
  obtain ⟨hS, hcount⟩ := robust_pattern_representations_exact W C hWC ha hcard
  refine ⟨S, Q, hS, hQR, hQproper, centered_progression_zero_mem Q,
    fun x hx => centered_progression_neg_mem Q hx,
    hQB'.trans (robust_representation_bohr_subset W T ha hcard hW), hQcard,
    fun d hd => hcount d (hQB' hd)⟩

end LeanProofs.GowersSzemeredi

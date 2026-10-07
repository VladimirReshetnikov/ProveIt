import OAI.Combinatorics.Progressions.Dynamics.InitialBudgetJointReplacement

namespace OAI

section

namespace Erdos3

theorem selectedPhysicalGrid_inverse_le_exp {J : Type*} [Fintype J] [DecidableEq J]
    (m n : ℕ) (k : J) (D : ℕ) {K A C Cwidth c epsilon P : ℝ}
    (hP : 0 ≤ P) (hK0 : 0 ≤ K) (hA0 : 0 ≤ A) (hC0 : 0 ≤ C) (hCwidth0 : 0 ≤ Cwidth)
    (hc0 : 0 < c) (heps0 : 0 < epsilon) (hD : 0 < D)
    (hn : (n : ℝ) ≤ Real.exp P) (hcard : (Fintype.card J : ℝ) ≤ Real.exp P)
    (hDlog : (D : ℝ) ≤ Real.exp P) (hK : K ≤ Real.exp P) (hA : A ≤ Real.exp P)
    (hC : C ≤ Real.exp P) (hCwidth : Cwidth ≤ Real.exp P)
    (hc : c⁻¹ ≤ Real.exp P) (heps : epsilon⁻¹ ≤ Real.exp P)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) :
    let tol := weightedReplacementTolerance ((3 * K) ^ m) ((2 : ℝ) ^ (n + 1) * A ^ n) epsilon
    let _Q := D * integerBoxGcdCutoff (Fintype.card J) Cwidth tol
    let κ := integerBoxRetainedGap (Fintype.card J) D c tol
    let Z := replacementCommonInputLog m n (Fintype.card J) P
    (physicalPairGridAccuracy n k C κ A tol)⁻¹ ≤
      Real.exp (2 * physicalPairCoefficientLog n (Fintype.card {j : J // j ≠ k}) Z + 2) := by
  intro tol Q κ Z
  obtain ⟨ht, hti, hk, hki, hq, _⟩ := replacement_selected_parameter_bounds m n (Fintype.card J) D
    hP hK0 hA0 hCwidth0 hc0 heps0 hD hDlog hK hA hCwidth hc heps
  obtain ⟨hn', hcard', hC', hA', _, hrow', hpow'⟩ :=
    replacement_common_geometric_bounds m n k hP hn hcard hC hA hprofile
  exact (physicalPairPointGridAccuracy_inverse_le_exp n k Q
    (replacementCommonInputLog_bounds m n (Fintype.card J) hP).1 hC0 hk hA0 ht
    hn' hq hC' hki hA' hti hcard' hrow' hpow').2

end Erdos3

end

end OAI

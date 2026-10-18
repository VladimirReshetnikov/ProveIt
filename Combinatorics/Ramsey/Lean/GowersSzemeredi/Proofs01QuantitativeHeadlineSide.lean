import GowersSzemeredi.Proofs01QuantitativeHeadline

/-!
# The quantitative headline consequence

This module isolates the real-power calculation which turns Gowers's
five-level threshold in Theorem 18.2 into the log--log density formulation
stated as Theorem 1.3. The final entry point supplies Theorem 18.2 to
this implication, preserving the paper's exact density exponent.

Moved here from `Proofs01QuantitativeHeadline`, which keeps only what the final
route uses. -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

private def headlineOuterExponent (k : Nat) : Real :=
  (2 : Real) ^ ((2 : Real) ^ (k + 9 : Nat))

private def headlineLogFloor (k : Nat) : Real :=
  (2 : Real) ^ headlineOuterExponent k

/-- Above a concrete (enormous) log--log floor, the density appearing in
Theorem 1.3 lies in `(0,1/2]` and satisfies Theorem 18.2's tower threshold. -/
private lemma headline_density_threshold (k N : Nat)
    (hfloor : Real.exp (Real.exp (headlineLogFloor k)) <= (N : Real)) :
    let L := Real.log (Real.log N)
    let delta := L ^ (-theorem_1_3_constant k)
    0 < delta /\ delta <= 1 / 2 /\ szemerediThreshold delta k <= N := by
  simpa only [headlineLogFloor, headlineOuterExponent, theorem_1_3_constant,
    szemerediThreshold, Real.rpow_neg (by norm_num : (0 : Real) ≤ 2)] using
    headline_density_threshold_of_exponent
      ((2 : Real) ^ ((2 : Real) ^ (k + 9 : Nat))) (by positivity) N hfloor

/-- **Gowers, Theorem 1.3, conditional on Theorem 18.2.**  This closes the
headline log--log/tower conversion with the paper's exact displayed constant
`2^(-2^(k+9))`. -/
theorem theorem_1_3_holds_of_theorem_18_2
    (h18 : theorem_18_2) : theorem_1_3 := by
  intro k hk
  refine ⟨⌈Real.exp (Real.exp (headlineLogFloor k))⌉₊, ?_⟩
  intro N hN A hAsub hAcard
  have hfloor : Real.exp (Real.exp (headlineLogFloor k)) <= (N : Real) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hN)
  let L : Real := Real.log (Real.log N)
  let delta : Real := L ^ (-theorem_1_3_constant k)
  obtain ⟨hdelta, hdeltaHalf, hthreshold⟩ :=
    headline_density_threshold k N hfloor
  have hcard : delta * N <= A.card := by
    simpa only [delta, L, mul_comm] using hAcard
  exact h18 delta k N hdelta hdeltaHalf hk hthreshold A hAsub hcard

end LeanProofs.GowersSzemeredi

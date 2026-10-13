import GowersSzemeredi.Proofs18GeneralLocalInverseAssembly
import GowersSzemeredi.Proofs18FejerCubicParameters
import GowersSzemeredi.Proofs17FejerCubicLocalization

/-! Explicit modulus threshold for the global cubic twisted discrepancy partition. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open scoped BigOperators

def fejerCubicTwistedThreshold (alpha : Real) : Real :=
  fejerCubicPrimeModelThreshold alpha
    (max 4 (quadraticExponentialThreshold (fejerCubicLocalQuadraticParameter alpha)))

/-- Cubic nonuniformity yields a full proper discrepancy partition for one
cubic twist. The explicit count is scaled by the common original cell
length, which retains the Section 13 positive-power lower bound. -/
theorem fejer_cubic_nonuniformity_twisted_discrepancy (alpha : Real)
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    ∀ (N : Nat) [NeZero N] [Fact N.Prime], fejerCubicTwistedThreshold alpha ≤ (N : Real) →
      ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha 3 →
      ∃ phi : ZMod N → ZMod N, ∃ l J : Nat, ∃ R : Fin J → ModAP N,
        PolynomialOn 3 Finset.univ phi ∧
        (N : Real) ^ fejerCubicLocalizationExponent alpha / 12 ≤ l ∧
        IsPartition (fun j => (R j).carrier) Finset.univ ∧
        (∀ j, (R j).IsProper) ∧
        (J : Real) ≤ fejerCubicLocalCountConstant alpha * N / (l : Real) ^ fejerCubicLocalCountExponent alpha ∧
        fejerCubicTwistedDiscrepancyParameter alpha * N ≤ ∑ j, ‖∑ x ∈ (R j).carrier, phaseTwist f phi x‖ := by
  let a := fejerCubicLocalQuadraticParameter alpha
  let b := quadraticDiscrepancyParameter a
  let eta := (2 : Real) ^ (-(58 : Int)) * alpha ^ 2 * (alpha / 2) ^ ((2 : Nat) ^ 42)
  let e := fejerCubicLocalizationExponent alpha
  let T := max 4 (quadraticExponentialThreshold a)
  have ha : 0 < a := fejerCubicLocalQuadraticParameter_pos hα
  have haone : a ≤ 1 := fejerCubicLocalQuadraticParameter_le_one hα.le hαone
  have hb : 0 < b := by dsimp [b, quadraticDiscrepancyParameter]; positivity
  have he : 0 < e := (section13_fejer_explicit_exponent_bounds hα hαone).1
  obtain ⟨ht, htone⟩ := fejerCubicLocalCountExponent_bounds hα hαone
  have hσ : 0 ≤ quadraticDiscrepancyExponent a := by
    change 0 < quadraticDiscrepancyExponent a / 16 at ht
    linarith only [ht]
  have hσ16 : quadraticDiscrepancyExponent a ≤ 16 := by
    change quadraticDiscrepancyExponent a / 16 ≤ 1 at htone
    linarith only [htone]
  have hparam : (eta / 2) / (2 * (2 + 2 : Nat) : Real) ^ (2 + 2) = a := by
    dsimp [eta, a, fejerCubicLocalQuadraticParameter]
    generalize (alpha / 2) ^ ((2 : Nat) ^ 42) = z
    norm_num
    ring
  have hbound : FunctionDiscrepancyBound 2
      ((eta / 2) / (2 * (2 + 2 : Nat) : Real) ^ (2 + 2)) b
      (quadraticDiscrepancyExponent a) (quadraticExponentialThreshold a) := by
    rw [hparam]
    exact quadratic_function_discrepancy_bound ha haone
  intro N _ _ hN f hf hnot
  have hNloc : section13FejerOddSquareThreshold alpha ≤ (N : Real) :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  obtain ⟨phi, K, l, Q, hpoly, hQ, hproper, hlength, hupper, hfail⟩ :=
    fejer_cubic_nonuniformity_localized_phase_removal alpha hα hαone N hNloc f hf hnot
  have hlarge : 12 * max 2 T ≤ (N : Real) ^ e := by
    simpa only [one_mul] using positivePowerThreshold_spec zero_lt_one he
      ((le_max_right _ _).trans ((le_max_right _ _).trans hN) :
        positivePowerThreshold (12 * max 2 T) 1 e ≤ (N : Real))
  change (N : Real) ^ e / 12 ≤ (l : Real) at hlength
  have hlmax : max 2 T ≤ (l : Real) := by linarith only [hlarge, hlength]
  have hl : 2 ≤ l := by exact_mod_cast ((le_max_left 2 T).trans hlmax)
  have hT : quadraticExponentialThreshold a ≤ (l : Real) :=
    (le_max_right _ _).trans ((le_max_right 2 T).trans hlmax)
  have hNreal : (256 : Real) ≤ N := (le_max_left _ _).trans hN
  have hroot0 := Real.sqrt_nonneg (N : Real)
  have hrootsq := Real.sq_sqrt (Nat.cast_nonneg N : (0 : Real) ≤ N)
  have hroot : 4 ≤ Real.sqrt N := by nlinarith only [hNreal, hroot0, hrootsq]
  have hrootprod := mul_nonneg hroot0 (sub_nonneg.mpr hroot)
  have hgeom (i : Fin K) : l ≤ (Q i).length ∧ (Q i).length ≤ l + 1 ∧
      (2 + 2) * (Q i).length ≤ N := by
    have hs : (4 : Real) * (Q i).length ≤ N := by nlinarith only [hupper i, hrootsq, hrootprod]
    have hs' : 4 * (Q i).length ≤ N := by exact_mod_cast hs
    rcases (hproper i).2 with hi | hi <;> omega
  obtain ⟨J, R, hR, hp, hc, hd⟩ := hbound.localized_partition (by dsimp [eta]; positivity) hb.le hσ hσ16
    (phaseTwist f phi) (phaseTwist_discValued hf phi) Q hQ (fun i => (hproper i).1)
    hl hT (by omega) hgeom hfail
  simp only [show (2 * (2 + 2 : Nat) : Real) = 8 by norm_num] at hc
  refine ⟨phi, l, J, R, hpoly, hlength, hR, hp, hc, ?_⟩
  have hmassparam : eta / 2 = fejerCubicLocalizedMassParameter alpha := by
    dsimp [eta, fejerCubicLocalizedMassParameter]
    generalize (alpha / 2) ^ ((2 : Nat) ^ 42) = z
    norm_num
    ring
  have hmass : eta * b / 2 = fejerCubicTwistedDiscrepancyParameter alpha := by
    change eta * b / 2 = fejerCubicLocalizedMassParameter alpha * b
    rw [← hmassparam]
    ring
  simpa only [hmass] using hd

end LeanProofs.GowersSzemeredi

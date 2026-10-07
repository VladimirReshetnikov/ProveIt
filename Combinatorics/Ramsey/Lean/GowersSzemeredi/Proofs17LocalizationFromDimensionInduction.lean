import GowersSzemeredi.Proofs17MultilinearBoxEnergy
import GowersSzemeredi.Proofs13ExplicitPowerThreshold
import GowersSzemeredi.Proofs18ShortLocalizationInverse

/-! The fixed-dimensional Section 16 structural theorem supplies the actual
short polynomial localization needed for the general inverse induction.
All geometric and Fourier-energy inputs are constructed, rather than
postulated as additional certificates. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The surviving localized uniformity parameter, including the odd-box
density loss and the full loss from Proposition 17.7. -/
def dimensionLocalizationParameter (alpha : Real) (k : Nat) : Real :=
  (2 : Real) ^ (-(2 * (k + 1) ^ 3 : Int)) *
    (section16ShortBoxDensity alpha k * alpha ^ 2 / 4)

theorem dimensionLocalizationParameter_pos {alpha : Real} (hα : 0 < alpha) (k : Nat) :
    0 < dimensionLocalizationParameter alpha k := by
  have hd := section16ShortBoxDensity_pos hα k
  unfold dimensionLocalizationParameter
  positivity

/-- From the corresponding dimension of Theorem 16.2, construct a
polynomial twist and a full proper partition on which degree-k uniformity
fails. All cells are at most sqrt(N); their common lower length is at least
N^e/(6*k), with e the proved capped corollary width exponent. -/
theorem polynomial_localization_of_dimension_induction {k : Nat} (hk : 1 ≤ k)
    (hth : Theorem162At k) (alpha : Real) (hα : 0 < alpha) (hαhalf : alpha ≤ 1 / 2) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha (k + 1) →
      ∃ phi : ZMod N → ZMod N, ∃ K l : Nat, ∃ Q : Fin K → ModAP N,
        PolynomialOn (k + 1) Finset.univ phi ∧
        IsPartition (fun i => (Q i).carrier) Finset.univ ∧
        (∀ i, (Q i).IsProper ∧ ((Q i).length = l ∨ (Q i).length = l + 1)) ∧
        (N : Real) ^ section16ShortBoxExponent alpha k / (6 * k) ≤ l ∧
        (∀ i, ((Q i).length : Real) ≤ Real.sqrt N) ∧
        ¬ UniformOnPartition (phaseTwist f phi) k (dimensionLocalizationParameter alpha k) Q (l + 1) := by
  let e := section16ShortBoxExponent alpha k
  have he : 0 < e := section16ShortBoxExponent_pos hα k
  have hd := section16ShortBoxDensity_pos hα k
  let rho := section16ShortBoxDensity alpha k * alpha ^ 2 / 4
  have hrho : 0 < rho := by dsimp [rho]; positivity
  obtain ⟨N0, hN0⟩ := corollary_16_11_of_dimension_induction hk hth alpha hα hαhalf
  refine ⟨max N0 ⌈positivePowerThreshold 4 1 e⌉₊, fun N _ _ hN f hf hnot => ?_⟩
  have hlarge : 4 ≤ (N : Real) ^ e := by
    have hsize : positivePowerThreshold 4 1 e ≤ (N : Real) :=
      (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hN)
    simpa only [one_mul] using positivePowerThreshold_spec zero_lt_one he hsize
  obtain ⟨P, mu, hp, hmu, hwidth, hmass⟩ := hN0 N ((le_max_left _ _).trans hN) f hf hnot
  obtain ⟨m, S, hm, _, hmlower, hmsqrt, hstep, _, hw, haxes, _, henergy⟩ :=
    short_odd_multilinear_fourier_box P hp (by omega) f mu hα hmu hwidth hmass hlarge
  obtain ⟨phi, K, l, Q, hpoly, hpart, hproper, hlength, hupper, hfail⟩ :=
    proposition_17_7_with_upper N k m f S mu rho hrho (by omega) hm hw haxes hstep hmsqrt hf hmu henergy
  refine ⟨phi, K, l, Q, hpoly, hpart, hproper, ?_, ?_, hfail⟩
  · have hk0 : (0 : Real) < k := by exact_mod_cast (show 0 < k by omega)
    calc
      _ = ((N : Real) ^ e / 2) / (3 * k) := by dsimp [e]; field_simp; ring
      _ ≤ (m : Real) / (3 * k) := div_le_div_of_nonneg_right hmlower (by positivity)
      _ ≤ _ := hlength
  · intro i
    exact (by exact_mod_cast hupper i : ((Q i).length : Real) ≤ m).trans hmsqrt

/-- The fixed-dimensional structural theorem and an explicit lower-degree
inverse bound now imply the next inverse bound above a finite threshold.
This is conditional on Section 16, but has no remaining geometric or
assembly hypothesis. The exact quantitative parameters are retained. -/
theorem function_inverse_step_of_dimension_induction {k : Nat} (hk : 1 ≤ k)
    (hth : Theorem162At k) {alpha beta sigma T : Real}
    (hα : 0 < alpha) (hαhalf : alpha ≤ 1 / 2)
    (hbound : FunctionDiscrepancyBound k
      ((dimensionLocalizationParameter alpha k / 2) / (2 * (k + 2 : Nat) : Real) ^ (k + 2)) beta sigma T)
    (hβ : 0 < beta) (hσ : 0 < sigma) (hσ16 : sigma ≤ 16) :
    ∃ Tnext : Real, FunctionDiscrepancyBound (k + 1) alpha
      (dimensionLocalizationParameter alpha k * beta / 4)
      (inverseStepExponent k (section16ShortBoxExponent alpha k) sigma) Tnext := by
  obtain ⟨N0, hN0⟩ := polynomial_localization_of_dimension_induction hk hth alpha hα hαhalf
  have hk0 : (0 : Real) < k := by exact_mod_cast (show 0 < k by omega)
  refine ⟨_, hbound.of_short_polynomial_localization (Tloc := (N0 : Real))
    (dimensionLocalizationParameter_pos hα k) hβ hσ hσ16
    (section16ShortBoxExponent_pos hα k) (by positivity : (0 : Real) < 6 * k) ?_⟩
  intro N _ _ (hN : (N0 : Real) ≤ N) f hf hnot
  exact hN0 N (by exact_mod_cast hN) f hf hnot

end LeanProofs.GowersSzemeredi

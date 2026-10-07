import GowersSzemeredi.Proofs16JointFrequencyBox
import GowersSzemeredi.Proofs17DenseFrequencyLocalization
import GowersSzemeredi.Proofs13ExplicitPowerThreshold
import GowersSzemeredi.Proofs18ShortLocalizationInverse

/-! The joint power cover supplies polynomial localization without the
current-dimensional source structural theorem. Only lower dimensions remain. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def jointPowerLocalizationExponent (alpha : Real) (k : Nat) : Real :=
  min (section16JointFrequencyExponent alpha k) (1 / 2)

def jointPowerLocalizationParameter (alpha : Real) (k : Nat) : Real :=
  (2 : Real) ^ (-(2 * (k + 2) ^ 3 : Int)) *
    (section16JointFrequencyDensity alpha k / (2 : Real) ^ (k + 1) * alpha ^ 2 / 4)

theorem jointPowerLocalizationExponent_pos {k : Nat} (hk : 0 < k)
    {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1 / 2) :
    0 < jointPowerLocalizationExponent alpha k :=
  lt_min (section16JointFrequencyExponent_pos hk ha ha1) (by norm_num)

theorem jointPowerLocalizationParameter_pos {alpha : Real} (ha : 0 < alpha) (k : Nat) :
    0 < jointPowerLocalizationParameter alpha k := by
  have hd := section16JointFrequencyDensity_pos ha k
  unfold jointPowerLocalizationParameter
  positivity

/-- Degree k+2 localization follows from exact structural dimensions only
through k, with all Fourier energy and short-box geometry constructed. -/
theorem polynomial_localization_of_joint_power_structure {k : Nat} (hk : 1 ≤ k)
    (hth : ∀ l : Nat, 1 ≤ l → l ≤ k → Theorem162At l)
    (alpha : Real) (ha : 0 < alpha) (haHalf : alpha ≤ 1 / 2) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha (k + 2) →
      ∃ phi : ZMod N → ZMod N, ∃ K l : Nat, ∃ Q : Fin K → ModAP N,
        PolynomialOn (k + 2) Finset.univ phi ∧
        IsPartition (fun i => (Q i).carrier) Finset.univ ∧
        (∀ i, (Q i).IsProper ∧ ((Q i).length = l ∨ (Q i).length = l + 1)) ∧
        (N : Real) ^ jointPowerLocalizationExponent alpha k / (6 * (k + 1)) ≤ l ∧
        (∀ i, ((Q i).length : Real) ≤ Real.sqrt N) ∧
        ¬ UniformOnPartition (phaseTwist f phi) (k + 1)
          (jointPowerLocalizationParameter alpha k) Q (l + 1) := by
  let e := jointPowerLocalizationExponent alpha k
  have he : 0 < e := jointPowerLocalizationExponent_pos hk ha haHalf
  obtain ⟨N0, hN0⟩ := section16_joint_frequency_box hk hth alpha ha haHalf
  refine ⟨max N0 ⌈positivePowerThreshold 4 1 e⌉₊, fun N _ _ hN f hf hnot => ?_⟩
  have hlarge : 4 ≤ (N : Real) ^ e := by
    have hsize : positivePowerThreshold 4 1 e ≤ (N : Real) :=
      (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hN)
    simpa only [one_mul] using positivePowerThreshold_spec zero_lt_one he hsize
  obtain ⟨P, mu, hp, hmu, hw, hmass⟩ := hN0 N ((le_max_left _ _).trans hN) f hf hnot
  have hwidth : (N : Real) ^ e ≤ P.width :=
    (Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast NeZero.one_le : (1 : Real) ≤ N) (min_le_left _ _)).trans hw
  simpa [jointPowerLocalizationParameter, jointPowerLocalizationExponent, Nat.cast_add, add_assoc] using
    (polynomial_localization_of_dense_frequency_box (by omega) P hp f mu ha
    (section16JointFrequencyDensity_pos ha k) (min_le_right _ _) hf hmu hwidth hlarge hmass)

/-- An inverse step now needs the structural theorem only in dimensions
strictly below the multilinear frequency dimension. The exact lower-degree
input parameter and every power loss remain explicit. -/
theorem function_inverse_step_of_joint_power_structure {k : Nat} (hk : 1 ≤ k)
    (hth : ∀ l : Nat, 1 ≤ l → l ≤ k → Theorem162At l)
    {alpha beta sigma T : Real} (ha : 0 < alpha) (haHalf : alpha ≤ 1 / 2)
    (hbound : FunctionDiscrepancyBound (k + 1)
      ((jointPowerLocalizationParameter alpha k / 2) / (2 * (k + 3 : Nat) : Real) ^ (k + 3))
      beta sigma T)
    (hb : 0 < beta) (hs : 0 < sigma) (hs16 : sigma ≤ 16) :
    ∃ Tnext : Real, FunctionDiscrepancyBound (k + 2) alpha
      (jointPowerLocalizationParameter alpha k * beta / 4)
      (inverseStepExponent (k + 1) (jointPowerLocalizationExponent alpha k) sigma) Tnext := by
  obtain ⟨N0, hN0⟩ := polynomial_localization_of_joint_power_structure hk hth alpha ha haHalf
  have hk0 : (0 : Real) < k + 1 := by positivity
  refine ⟨_, hbound.of_short_polynomial_localization (Tloc := (N0 : Real))
    (jointPowerLocalizationParameter_pos ha k) hb hs hs16
    (jointPowerLocalizationExponent_pos hk ha haHalf) (by positivity : (0 : Real) < 6 * (k + 1)) ?_⟩
  intro N _ _ (hN : (N0 : Real) ≤ N) f hf hnot
  exact hN0 N (by exact_mod_cast hN) f hf hnot

end LeanProofs.GowersSzemeredi

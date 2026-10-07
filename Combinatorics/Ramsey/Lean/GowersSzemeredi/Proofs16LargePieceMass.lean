import GowersSzemeredi.Proofs16GoodDomainTransport
import GowersSzemeredi.Proofs16RadiusComparison
import GowersSzemeredi.Proofs16CoverParameterMonotonicity

/-! The common-base density meets the mass budget required by the final
finite extraction, including the corrected density constants. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem section16_thetaTwo_inverse_le_iteration {theta gamma : Real} (k : Nat)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    (section16ThetaTwo (section16ThetaOne theta gamma k))⁻¹ ≤ multipleS theta gamma k := by
  let a := section16ThetaOne theta gamma k
  obtain ⟨ha4, ha4small⟩ := section16_density_parameter_bounds k ht ht1 hg hg1
  have ha : 0 < a := by dsimp [a]; linarith
  have ha1 : a ≤ 1 := by dsimp [a]; linarith
  have hpow : a ^ 11 ≤ a ^ 8 := pow_le_pow_of_le_one ha.le ha1 (by omega)
  have hinv : (section16ThetaTwo a)⁻¹ = (2 : Real) ^ (32 : Nat) / a ^ 8 := by
    norm_num [section16ThetaTwo, Real.rpow_neg, Real.rpow_ofNat, mul_inv_rev, div_eq_mul_inv]
    ring
  rw [hinv]
  apply le_trans _ (section16_radius_exponent_budget k ht ht1 hg hg1)
  change (2 : Real) ^ (32 : Nat) / a ^ 8 ≤ (2 : Real) ^ (83 : Nat) / (a / 4) ^ 11
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  calc
    (2 : Real) ^ (32 : Nat) * (a / 4) ^ 11 = (2 : Real) ^ (10 : Nat) * a ^ 11 := by ring
    _ ≤ (2 : Real) ^ (10 : Nat) * a ^ 8 := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ ≤ (2 : Real) ^ (83 : Nat) * a ^ 8 :=
      mul_le_mul_of_nonneg_right (by norm_num) (by positivity)

/-- Corrected common-base density is more than sufficient for the stated
iteration budget, even in the preceding dimension. -/
theorem section16_common_base_mass_budget {N k : Nat} [NeZero N] {theta gamma : Real}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    (N : Real) ^ (k + 1) / multipleS theta gamma (k + 1) ≤
      section16ThetaTwo (section16ThetaOne theta gamma k) * (N : Real) ^ (k + 1) := by
  have hd : 0 < section16ThetaTwo (section16ThetaOne theta gamma k) := by
    unfold section16ThetaTwo section16ThetaOne
    positivity
  have hi := (section16_thetaTwo_inverse_le_iteration k ht ht1 hg hg1).trans
    (multipleS_mono_dimension ht ht1 hg hg1 (Nat.le_succ k))
  have hinv := inv_anti₀ (inv_pos.mpr hd) hi
  rw [inv_inv] at hinv
  rw [div_eq_mul_inv, mul_comm (section16ThetaTwo _)]
  exact mul_le_mul_of_nonneg_left hinv (by positivity)

/-- Once the genuine all-ones unit cover is proved, the selected common-base
graph has every mass and containment property needed by the closing theorem.
The cover itself remains an explicit unresolved premise. -/
theorem section16_large_piece_of_common_base {N k : Nat} [NeZero N] [Fact N.Prime]
    (theta gamma : Real) (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (Gamma : Finset (Point N (k + 1) × ZMod N))
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (H : Finset (Point N k)) (Y : (h : Point N k) → Finset (Section16CubeElement B h))
    (x0 : Point N k) (hgraph : GraphContained B phi Gamma)
    (hmass : section16ThetaTwo (section16ThetaOne theta gamma k) * (N : Real) ^ (k + 1) ≤
      section16GoodInducedPairCount B H Y x0)
    (hML : MultiplyLinearFunction gamma 1 (section16GoodDomain B H Y x0)
      (section16PhiOne phi x0)) :
    ∃ D ⊆ Gamma, (N : Real) ^ (k + 1) / multipleS theta gamma (k + 1) ≤ D.card ∧
      MultiplyLinear gamma 1 D := by
  obtain ⟨D, hD, hd, hcover⟩ := section16_good_domain_subrelation Gamma B phi H Y x0 hgraph hmass hML
  exact ⟨D, hD, (section16_common_base_mass_budget ht ht1 hg hg1).trans hd, hcover⟩

end LeanProofs.GowersSzemeredi

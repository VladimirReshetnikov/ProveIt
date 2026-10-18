import GowersSzemeredi.Proofs18GeneralLocalInverseAssembly
import GowersSzemeredi.Proofs05VariablePhaseRefinement
import GowersSzemeredi.Proofs18QuantitativeSzemeredi
import GowersSzemeredi.Proofs13ExplicitPowerThreshold

/-! Remove polynomial phases of arbitrary degree from a discrepancy
partition, with an explicit threshold absorbing the refinement constant. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open scoped BigOperators

/-- The exponent retained after refining polynomial phases of degree k. -/
def phaseInverseExponent (k : Nat) (e : Real) : Real :=
  e / (2 * (polynomialPartitionConstant k : Real))

/-- The fixed factor in the refined partition count. -/
def phaseInverseConstant (k : Nat) (beta D : Real) : Real :=
  section5LocalRefinementConstant k beta * D ^ (polynomialPartitionConstant k : Real)⁻¹

/-- A polynomial twist may vary from cell to cell. A full power-saving
count and twisted discrepancy yield an untwisted proper partition with
explicit average-size exponent and a finite modulus threshold. -/
theorem polynomial_phase_inverse_partition {N K k : Nat} [NeZero N]
    {e beta D : Real} (hk : 1 ≤ k) (he : 0 < e) (hβ : 0 < beta) (hD : 0 < D)
    (f : ZMod N → Complex) (hf : DiscValued f)
    (Q : Fin K → ModAP N) (phi : Fin K → ZMod N → ZMod N)
    (hpoly : ∀ i, PolynomialOn k Finset.univ (phi i))
    (hQ : IsPartition (fun i => (Q i).carrier) Finset.univ)
    (hcount : (K : Real) ≤ D * (N : Real) ^ (1 - e))
    (hdis : beta * N ≤ ∑ i, ‖∑ x ∈ (Q i).carrier, phaseTwist f (phi i) x‖)
    (hN : positivePowerThreshold (phaseInverseConstant k beta D) 1
      (phaseInverseExponent k e) ≤ (N : Real)) :
    ∃ J : Nat, ∃ R : Fin J → ModAP N,
      IsPartition (fun j => (R j).carrier) Finset.univ ∧
      (∀ j, (R j).IsProper) ∧
      (N : Real) ^ phaseInverseExponent k e ≤ averageCellSize (fun j => (R j).carrier) ∧
      (beta / 2) * N ≤ ∑ j, ‖∑ x ∈ (R j).carrier, f x‖ := by
  obtain ⟨J, R, hR, _, hRproper, hJ, hdisR⟩ := variable_polynomial_phase_refinement
    Q phi f beta hk hβ hpoly hf hQ hdis
  have hNr : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hq : 0 < (polynomialPartitionConstant k : Real)⁻¹ := by
    unfold polynomialPartitionConstant; positivity
  have hs : 0 < phaseInverseExponent k e := by
    unfold phaseInverseExponent polynomialPartitionConstant; positivity
  have heq : 2 * phaseInverseExponent k e + (1 - e) * (polynomialPartitionConstant k : Real)⁻¹ +
      (1 - (polynomialPartitionConstant k : Real)⁻¹) = 1 := by
    unfold phaseInverseExponent; ring
  have hC := positivePowerThreshold_spec zero_lt_one hs hN
  rw [one_mul, phaseInverseConstant] at hC
  have hC₀ := section5LocalRefinementConstant_pos k beta
  refine ⟨J, R, hR, hRproper, ?_, hdisR⟩
  rw [hR.averageCellSize_univ,
    le_div_iff₀ (Nat.cast_pos.mpr (section18_partition_index_nonempty _ hR))]
  generalize phaseInverseExponent k e = s at hs hC heq ⊢
  generalize (polynomialPartitionConstant k : Real)⁻¹ = q at hq hJ hC heq
  generalize section5LocalRefinementConstant k beta = C₀ at hC₀ hJ hC
  calc (N : Real) ^ s * J ≤ N ^ s * (C₀ * (D * N ^ (1 - e)) ^ q * N ^ (1 - q)) := by
        gcongr; exact hJ.trans (by gcongr)
    _ = C₀ * D ^ q * (N ^ s * N ^ ((1 - e) * q + (1 - q))) := by
        rw [Real.mul_rpow hD.le (Real.rpow_nonneg hNr.le _), ← Real.rpow_mul hNr.le,
          Real.rpow_add hNr]
        ring
    _ ≤ N ^ s * (N ^ s * N ^ ((1 - e) * q + (1 - q))) := by gcongr
    _ = N := by
        rw [← Real.rpow_add hNr, ← Real.rpow_add hNr,
          show s + (s + ((1 - e) * q + (1 - q))) = 1 by linarith, Real.rpow_one]

end LeanProofs.GowersSzemeredi

import GowersSzemeredi.Proofs17QuadraticLocalization
import GowersSzemeredi.Proofs18PrimeCubeModel

/-! A constructed smaller-prime linear obstruction from quadratic
nonuniformity, retaining the polynomial twist and interval pullback. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Filter

/-- Quadratic nonuniformity produces, on a proper progression, a quadratic twist
whose index function has a linear obstruction in a strictly smaller prime
model. The new uniformity parameter is independent of the original modulus. -/
theorem quadratic_nonuniformity_prime_model :
    ∀ alpha : Real, 0 < alpha → alpha ≤ 1 → ∃ N₀ : Nat,
      ∀ (N : Nat) [NeZero N] [Fact N.Prime], N₀ ≤ N →
        ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha 2 →
        ∃ phi : ZMod N → ZMod N, ∃ P : ModAP N,
          PolynomialOn 2 Finset.univ phi ∧ P.IsProper ∧
          (N : Real) ^ (cor711Exponent ((alpha / 2) ^ (12359 : Nat)) 1) / 6 ≤ P.length ∧
          ∃ M : Nat, ∃ hM : M.Prime,
            letI : NeZero M := ⟨hM.ne_zero⟩
            3 * P.length < M ∧ M ≤ 6 * P.length ∧ (M : Real) ≤ (N : Real) / 2 ∧
            DiscValued (intervalExtension M (P.pullbackFunction (phaseTwist f phi))) ∧
            ¬ UniformOfDegree (intervalExtension M (P.pullbackFunction (phaseTwist f phi)))
              ((2 : Real) ^ (-(19 : Int)) * alpha ^ 2 * (alpha / 2) ^ (12359 : Nat) / 216) 1 := by
  intro alpha hα hαone
  let e := cor711Exponent ((alpha / 2) ^ (12359 : Nat)) 1
  let beta := (2 : Real) ^ (-(19 : Int)) * alpha ^ 2 * (alpha / 2) ^ (12359 : Nat)
  have hβ : 0 < beta := by dsimp [beta]; positivity
  obtain ⟨he, _⟩ := quadratic_frequency_exponent_bounds hα hαone
  obtain ⟨N₁, hN₁⟩ := quadratic_nonuniformity_localized_phase_removal alpha hα hαone
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (eventually_nat_mul_rpow_le (C := 12) (D := 1) he zero_lt_one)
  refine ⟨max 256 (max N₁ N₂), fun N _ _ hN f hf hnot => ?_⟩
  obtain ⟨phi, K, l, Q, hpoly, _, hproper, hlength, hupper, hfail⟩ := hN₁ N (by omega) f hf hnot
  obtain ⟨i, hi⟩ := not_uniformOnPartition_exists_cell (phaseTwist f phi) Q beta hfail
  have hlarge : 12 ≤ (N : Real) ^ e := by
    simpa only [Real.rpow_zero, mul_one, one_mul] using hN₂ N (by omega)
  change (N : Real) ^ e / 6 ≤ (l : Real) at hlength
  have hl : 2 ≤ l := by
    have hr : (2 : Real) ≤ l := by linarith only [hlength, hlarge]
    exact_mod_cast hr
  have hL : 2 ≤ (Q i).length := by rcases (hproper i).2 with h | h <;> omega
  have hNreal : (256 : Real) ≤ N := by exact_mod_cast (show 256 ≤ N by omega)
  have hroot0 := Real.sqrt_nonneg (N : Real)
  have hrootsq := Real.sq_sqrt (Nat.cast_nonneg N : (0 : Real) ≤ N)
  have hroot : 16 ≤ Real.sqrt N := by nlinarith only [hNreal, hroot0, hrootsq]
  have hrootprod := mul_nonneg hroot0 (sub_nonneg.mpr hroot)
  have hrootupper : 6 * Real.sqrt N ≤ (N : Real) / 2 := by nlinarith only [hrootsq, hrootprod]
  have hshort : 3 * (Q i).length ≤ N := by
    have hU := hupper i
    have hr : (3 : Real) * (Q i).length ≤ N := by nlinarith only [hU, hrootupper, hNreal]
    exact_mod_cast hr
  have hr : ((Q i).length : Real) ≤ (l : Real) + 1 := by
    exact_mod_cast (show (Q i).length ≤ l + 1 by rcases (hproper i).2 with h | h <;> omega)
  obtain ⟨M, hM, hMlower, hMupper, hdisc, hnew⟩ :=
    (Q i).exists_prime_model_of_nonuniform (phaseTwist f phi) beta ((l : Real) + 1)
      (hproper i).1 hL hshort (phaseTwist_discValued hf phi) hβ.le hr
      (by simpa only [Nat.cast_add, Nat.cast_one] using hi)
  letI : NeZero M := ⟨hM.ne_zero⟩
  have hM6 : M ≤ 6 * (Q i).length := by omega
  have hMhalf : (M : Real) ≤ (N : Real) / 2 := by
    have hMr : (M : Real) ≤ 6 * (Q i).length := by exact_mod_cast hM6
    have hU := hupper i
    nlinarith only [hMr, hU, hrootupper]
  have hconstant : beta / (2 * (1 + 2 : Nat) : Real) ^ (1 + 2) =
      (2 : Real) ^ (-(19 : Int)) * alpha ^ 2 * (alpha / 2) ^ (12359 : Nat) / 216 := by
    dsimp only [beta]
    generalize (alpha / 2) ^ (12359 : Nat) = a
    norm_num
  refine ⟨phi, Q i, hpoly, (hproper i).1, ?_, M, hM, hMlower, ?_, hMhalf, hdisc, ?_⟩
  · have hli : l ≤ (Q i).length := by rcases (hproper i).2 with h | h <;> omega
    exact hlength.trans (by exact_mod_cast hli)
  · exact hM6
  · simpa only [hconstant] using hnew

end LeanProofs.GowersSzemeredi

import GowersSzemeredi.Proofs17CubicLocalization
import GowersSzemeredi.Proofs18PrimeCubeModel

/-! A constructed smaller-prime quadratic obstruction from cubic
nonuniformity, retaining the polynomial twist and interval pullback. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Filter

/-- Cubic nonuniformity produces, on a proper progression, a cubic twist
whose index function has a quadratic obstruction in a strictly smaller prime
model. The new uniformity parameter is independent of the original modulus. -/
theorem cubic_nonuniformity_prime_model :
    ∀ alpha : Real, 0 < alpha → alpha ≤ 1 → ∃ N₀ : Nat,
      ∀ (N : Nat) [NeZero N] [Fact N.Prime], N₀ ≤ N →
        ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha 3 →
        ∃ phi : ZMod N → ZMod N, ∃ P : ModAP N,
          PolynomialOn 3 Finset.univ phi ∧ P.IsProper ∧
          (N : Real) ^ ((1 / 2 : Real) ^ ((2 / alpha) ^ ((2 : Nat) ^ 88))) / 12 ≤ P.length ∧
          ∃ M : Nat, ∃ hM : M.Prime,
            letI : NeZero M := ⟨hM.ne_zero⟩
            4 * P.length < M ∧ M ≤ 8 * P.length ∧ (M : Real) ≤ (N : Real) / 2 ∧
            DiscValued (intervalExtension M (P.pullbackFunction (phaseTwist f phi))) ∧
            ¬ UniformOfDegree (intervalExtension M (P.pullbackFunction (phaseTwist f phi)))
              ((2 : Real) ^ (-(70 : Int)) * alpha ^ 2 * (alpha / 2) ^ ((2 : Nat) ^ 76)) 2 := by
  intro alpha hα hαone
  let e := (1 / 2 : Real) ^ ((2 / alpha) ^ ((2 : Nat) ^ 88))
  let beta := (2 : Real) ^ (-(58 : Int)) * alpha ^ 2 * (alpha / 2) ^ ((2 : Nat) ^ 76)
  have hβ : 0 < beta := by dsimp [beta]; positivity
  obtain ⟨he, _⟩ := section13_explicit_exponent_bounds hα hαone
  obtain ⟨N₁, hN₁⟩ := cubic_nonuniformity_localized_phase_removal_with_upper alpha hα hαone
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (eventually_nat_mul_rpow_le (C := 24) (D := 1) he zero_lt_one)
  refine ⟨max 256 (max N₁ N₂), fun N _ _ hN f hf hnot => ?_⟩
  obtain ⟨phi, K, l, Q, hpoly, _, hproper, hlength, hupper, hfail⟩ := hN₁ N (by omega) f hf hnot
  obtain ⟨i, hi⟩ := not_uniformOnPartition_exists_cell (phaseTwist f phi) Q beta hfail
  have hlarge : 24 ≤ (N : Real) ^ e := by
    simpa only [Real.rpow_zero, mul_one, one_mul] using hN₂ N (by omega)
  change (N : Real) ^ e / 12 ≤ (l : Real) at hlength
  have hl : 2 ≤ l := by
    have hr : (2 : Real) ≤ l := by linarith only [hlength, hlarge]
    exact_mod_cast hr
  have hL : 2 ≤ (Q i).length := by rcases (hproper i).2 with h | h <;> omega
  have hNreal : (256 : Real) ≤ N := by exact_mod_cast (show 256 ≤ N by omega)
  have hroot0 := Real.sqrt_nonneg (N : Real)
  have hrootsq := Real.sq_sqrt (Nat.cast_nonneg N : (0 : Real) ≤ N)
  have hroot : 16 ≤ Real.sqrt N := by nlinarith only [hNreal, hroot0, hrootsq]
  have hrootprod := mul_nonneg hroot0 (sub_nonneg.mpr hroot)
  have hrootupper : 8 * Real.sqrt N ≤ (N : Real) / 2 := by nlinarith only [hrootsq, hrootprod]
  have hshort : 4 * (Q i).length ≤ N := by
    have hU := hupper i
    have hr : (4 : Real) * (Q i).length ≤ N := by nlinarith only [hU, hrootupper, hNreal]
    exact_mod_cast hr
  have hr : ((Q i).length : Real) ≤ (l : Real) + 1 := by
    exact_mod_cast (show (Q i).length ≤ l + 1 by rcases (hproper i).2 with h | h <;> omega)
  obtain ⟨M, hM, hMlower, hMupper, hdisc, hnew⟩ :=
    (Q i).exists_prime_model_of_nonuniform (phaseTwist f phi) beta ((l : Real) + 1)
      (hproper i).1 hL hshort (phaseTwist_discValued hf phi) hβ.le hr
      (by simpa only [Nat.cast_add, Nat.cast_one] using hi)
  letI : NeZero M := ⟨hM.ne_zero⟩
  have hM8 : M ≤ 8 * (Q i).length := by omega
  have hMhalf : (M : Real) ≤ (N : Real) / 2 := by
    have hMr : (M : Real) ≤ 8 * (Q i).length := by exact_mod_cast hM8
    have hU := hupper i
    nlinarith only [hMr, hU, hrootupper]
  have hconstant : beta / (2 * (2 + 2 : Nat) : Real) ^ (2 + 2) =
      (2 : Real) ^ (-(70 : Int)) * alpha ^ 2 * (alpha / 2) ^ ((2 : Nat) ^ 76) := by
    dsimp [beta]
    generalize (alpha / 2) ^ ((2 : Nat) ^ 76) = a
    norm_num
    ring
  refine ⟨phi, Q i, hpoly, (hproper i).1, ?_, M, hM, hMlower, ?_, hMhalf, hdisc, ?_⟩
  · have hli : l ≤ (Q i).length := by rcases (hproper i).2 with h | h <;> omega
    exact hlength.trans (by exact_mod_cast hli)
  · exact hM8
  · simpa only [hconstant] using hnew

end LeanProofs.GowersSzemeredi

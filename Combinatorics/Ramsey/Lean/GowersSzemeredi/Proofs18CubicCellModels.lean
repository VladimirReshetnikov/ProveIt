import GowersSzemeredi.Proofs17CubicLocalization
import GowersSzemeredi.Proofs18PartitionPrimeModels

/-! Cubic localization on a positive mass of cells, with prime models above
any prescribed threshold. This retains the mass needed for local discrepancy. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Filter
open scoped BigOperators

/-- Fraction of ambient mass retained when selecting cubic localization cells. -/
def cubicLocalizedMassParameter (alpha : Real) : Real :=
  (2 : Real) ^ (-(59 : Int)) * alpha ^ 2 * (alpha / 2) ^ ((2 : Nat) ^ 76)

/-- Common quadratic parameter in all the selected comparable prime models. -/
def cubicLocalQuadraticParameter (alpha : Real) : Real :=
  (2 : Real) ^ (-(71 : Int)) * alpha ^ 2 * (alpha / 2) ^ ((2 : Nat) ^ 76)

theorem cubicLocalQuadraticParameter_pos {alpha : Real} (hα : 0 < alpha) :
    0 < cubicLocalQuadraticParameter alpha := by
  unfold cubicLocalQuadraticParameter
  positivity

theorem cubicLocalQuadraticParameter_le_one {alpha : Real}
    (hα : 0 ≤ alpha) (hαone : alpha ≤ 1) : cubicLocalQuadraticParameter alpha ≤ 1 := by
  have hs : alpha ^ 2 ≤ 1 := pow_le_one₀ hα hαone
  have hp : (alpha / 2) ^ ((2 : Nat) ^ 76) ≤ 1 :=
    pow_le_one₀ (by positivity) (by linarith)
  have hc : (2 : Real) ^ (-(71 : Int)) ≤ 1 := by norm_num
  exact (mul_le_mul (mul_le_mul hc hs (by positivity) zero_le_one) hp
    (by positivity) (by positivity)).trans (by norm_num)

/-- Cubic nonuniformity supplies a proper partition with a positive mass of
cells admitting quadratic obstructions. The new prime moduli can all be
forced above a prescribed threshold without losing the explicit parameters. -/
theorem cubic_nonuniformity_many_prime_models (alpha T : Real)
    (hα : 0 < alpha) (hαone : alpha ≤ 1) : ∃ N₀ : Nat,
    ∀ (N : Nat) [NeZero N] [Fact N.Prime], N₀ ≤ N →
      ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha 3 →
      ∃ phi : ZMod N → ZMod N, ∃ K l : Nat, ∃ Q : Fin K → ModAP N,
        PolynomialOn 3 Finset.univ phi ∧
        IsPartition (fun i => (Q i).carrier) Finset.univ ∧
        (∀ i, (Q i).IsProper ∧ ((Q i).length = l ∨ (Q i).length = l + 1)) ∧
        (N : Real) ^ ((1 / 2 : Real) ^ ((2 / alpha) ^ ((2 : Nat) ^ 88))) / 12 ≤ l ∧
        ∃ B : Finset (Fin K),
          cubicLocalizedMassParameter alpha * N < ∑ i ∈ B, ((Q i).carrier.card : Real) ∧
          ∀ i ∈ B, ∃ M : Nat, ∃ hM : M.Prime,
            letI : NeZero M := ⟨hM.ne_zero⟩
            T ≤ (M : Real) ∧ 4 * (Q i).length < M ∧ M ≤ 8 * (Q i).length ∧
            (M : Real) ≤ (N : Real) / 2 ∧
            DiscValued (intervalExtension M ((Q i).pullbackFunction (phaseTwist f phi))) ∧
            ¬ UniformOfDegree (intervalExtension M ((Q i).pullbackFunction (phaseTwist f phi)))
              (cubicLocalQuadraticParameter alpha) 2 := by
  let e := (1 / 2 : Real) ^ ((2 / alpha) ^ ((2 : Nat) ^ 88))
  let beta := (2 : Real) ^ (-(58 : Int)) * alpha ^ 2 * (alpha / 2) ^ ((2 : Nat) ^ 76)
  have hβ : 0 < beta := by dsimp [beta]; positivity
  obtain ⟨he, _⟩ := section13_explicit_exponent_bounds hα hαone
  obtain ⟨N₁, hN₁⟩ := cubic_nonuniformity_localized_phase_removal_with_upper alpha hα hαone
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp
    (eventually_nat_mul_rpow_le (C := 12 * max 2 T) (D := 1) he zero_lt_one)
  refine ⟨max 256 (max N₁ N₂), fun N _ _ hN f hf hnot => ?_⟩
  obtain ⟨phi, K, l, Q, hpoly, hpart, hproper, hlength, hupper, hfail⟩ :=
    hN₁ N (by omega) f hf hnot
  have hlarge : 12 * max 2 T ≤ (N : Real) ^ e := by
    simpa only [Real.rpow_zero, mul_one, one_mul] using hN₂ N (by omega)
  change (N : Real) ^ e / 12 ≤ (l : Real) at hlength
  have hlmax : max 2 T ≤ (l : Real) := by linarith only [hlarge, hlength]
  have hl : 2 ≤ l := by exact_mod_cast ((le_max_left 2 T).trans hlmax)
  have hlT : T ≤ (l : Real) := (le_max_right 2 T).trans hlmax
  have hNreal : (256 : Real) ≤ N := by exact_mod_cast (show 256 ≤ N by omega)
  have hroot0 := Real.sqrt_nonneg (N : Real)
  have hrootsq := Real.sq_sqrt (Nat.cast_nonneg N : (0 : Real) ≤ N)
  have hroot : 16 ≤ Real.sqrt N := by nlinarith only [hNreal, hroot0, hrootsq]
  have hrootprod := mul_nonneg hroot0 (sub_nonneg.mpr hroot)
  have hrootupper : 8 * Real.sqrt N ≤ (N : Real) / 2 := by nlinarith only [hrootsq, hrootprod]
  have hgeom (i : Fin K) : 2 ≤ (Q i).length ∧ (Q i).length ≤ l + 1 ∧
      (2 + 2) * (Q i).length ≤ N := by
    have hU := hupper i
    have hs : (4 : Real) * (Q i).length ≤ N := by nlinarith only [hU, hrootupper, hNreal]
    have hs' : 4 * (Q i).length ≤ N := by exact_mod_cast hs
    rcases (hproper i).2 with hi | hi <;> omega
  obtain ⟨B, hmass, hB⟩ := partition_nonuniformity_prime_models
    (phaseTwist f phi) Q beta (phaseTwist_discValued hf phi) hβ.le
    (by omega) hpart (fun i => (hproper i).1) hgeom hfail
  have hmassparam : beta / 2 = cubicLocalizedMassParameter alpha := by
    dsimp [beta, cubicLocalizedMassParameter]
    generalize (alpha / 2) ^ ((2 : Nat) ^ 76) = a
    norm_num
    ring
  have hparam : (beta / 2) / (2 * (2 + 2 : Nat) : Real) ^ (2 + 2) =
      cubicLocalQuadraticParameter alpha := by
    dsimp [beta, cubicLocalQuadraticParameter]
    generalize (alpha / 2) ^ ((2 : Nat) ^ 76) = a
    norm_num
    ring
  refine ⟨phi, K, l, Q, hpoly, hpart, hproper, hlength, B, ?_, ?_⟩
  · simpa only [hmassparam] using hmass
  · intro i hi
    obtain ⟨M, hM, hMlow, hMup, hdisc, hnew⟩ := hB i hi
    letI : NeZero M := ⟨hM.ne_zero⟩
    have hM8 : M ≤ 8 * (Q i).length := by omega
    have hMhalf : (M : Real) ≤ (N : Real) / 2 := by
      have hMr : (M : Real) ≤ 8 * (Q i).length := by exact_mod_cast hM8
      have hU := hupper i
      nlinarith only [hMr, hU, hrootupper]
    have hlM : l ≤ M := by
      have hli : l ≤ (Q i).length := by rcases (hproper i).2 with h | h <;> omega
      omega
    refine ⟨M, hM, hlT.trans (by exact_mod_cast hlM), hMlow, hM8, hMhalf, hdisc, ?_⟩
    simpa only [hparam] using hnew

end LeanProofs.GowersSzemeredi

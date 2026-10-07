import GowersSzemeredi.Proofs18CubicCellModels
import GowersSzemeredi.Proofs17ExplicitCubicLocalization

/-! Explicit old-modulus threshold forcing every selected local prime above
any prescribed bound while retaining the positive-mass cubic localization. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open scoped BigOperators

def cubicPrimeModelThreshold (alpha T : Real) : Real :=
  max 256 (max (section13OddSquareThreshold alpha)
    (positivePowerThreshold (12 * max 2 T) 1
      ((1 / 2 : Real) ^ ((2 / alpha) ^ ((2 : Nat) ^ 88)))))

theorem cubic_nonuniformity_many_prime_models_explicit (alpha T : Real)
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    ∀ (N : Nat) [NeZero N] [Fact N.Prime], cubicPrimeModelThreshold alpha T ≤ N →
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
  intro N _ _ hN f hf hnot
  have hNloc : section13OddSquareThreshold alpha ≤ (N : Real) :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  obtain ⟨phi, K, l, Q, hpoly, hpart, hproper, hlength, hupper, hfail⟩ :=
    cubic_nonuniformity_localized_phase_removal_explicit alpha hα hαone N hNloc f hf hnot
  have hlarge : 12 * max 2 T ≤ (N : Real) ^ e := by
    simpa only [one_mul] using positivePowerThreshold_spec zero_lt_one he
      ((le_max_right _ _).trans ((le_max_right _ _).trans hN) :
        positivePowerThreshold (12 * max 2 T) 1 e ≤ (N : Real))
  change (N : Real) ^ e / 12 ≤ (l : Real) at hlength
  have hlmax : max 2 T ≤ (l : Real) := by linarith only [hlarge, hlength]
  have hl : 2 ≤ l := by exact_mod_cast ((le_max_left 2 T).trans hlmax)
  have hlT : T ≤ (l : Real) := (le_max_right 2 T).trans hlmax
  have hNreal : (256 : Real) ≤ N := (le_max_left _ _).trans hN
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

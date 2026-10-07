import GowersSzemeredi.Proofs18CubicCellModels
import GowersSzemeredi.Proofs18SelectedRefinement

/-! Full global discrepancy of a cubic polynomial twist, assembled from
quadratic inverse theorems on a positive mass of its localization cells. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open scoped BigOperators

def cubicLocalizationExponent (alpha : Real) : Real :=
  (1 / 2 : Real) ^ ((2 / alpha) ^ ((2 : Nat) ^ 88))

def cubicLocalCountExponent (alpha : Real) : Real :=
  quadraticDiscrepancyExponent (cubicLocalQuadraticParameter alpha) / 16

def cubicLocalCountConstant (alpha : Real) : Real :=
  max 1 (2 * boundaryRefinementConstant (1 / 16) * (8 : Real) ^ (1 - cubicLocalCountExponent alpha))

def cubicTwistedDiscrepancyParameter (alpha : Real) : Real :=
  cubicLocalizedMassParameter alpha * quadraticDiscrepancyParameter (cubicLocalQuadraticParameter alpha)

theorem cubicLocalCountExponent_bounds {alpha : Real} (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    0 < cubicLocalCountExponent alpha ∧ cubicLocalCountExponent alpha ≤ 1 := by
  have ha := cubicLocalQuadraticParameter_pos hα
  have haone := cubicLocalQuadraticParameter_le_one hα.le hαone
  obtain ⟨he, heone⟩ := quadratic_frequency_exponent_bounds ha haone
  dsimp [cubicLocalCountExponent, quadraticDiscrepancyExponent]
  constructor <;> linarith

/-- Cubic nonuniformity yields a full proper discrepancy partition for one
cubic twist. The explicit count is scaled by the common original cell
length, which retains the Section 13 positive-power lower bound. -/
theorem cubic_nonuniformity_twisted_discrepancy (alpha : Real)
    (hα : 0 < alpha) (hαone : alpha ≤ 1) : ∃ N₀ : Nat,
    ∀ (N : Nat) [NeZero N] [Fact N.Prime], N₀ ≤ N →
      ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha 3 →
      ∃ phi : ZMod N → ZMod N, ∃ l J : Nat, ∃ R : Fin J → ModAP N,
        PolynomialOn 3 Finset.univ phi ∧
        (N : Real) ^ cubicLocalizationExponent alpha / 12 ≤ l ∧
        IsPartition (fun j => (R j).carrier) Finset.univ ∧
        (∀ j, (R j).IsProper) ∧
        (J : Real) ≤ cubicLocalCountConstant alpha * N / (l : Real) ^ cubicLocalCountExponent alpha ∧
        cubicTwistedDiscrepancyParameter alpha * N ≤ ∑ j, ‖∑ x ∈ (R j).carrier, phaseTwist f phi x‖ := by
  let a := cubicLocalQuadraticParameter alpha
  let b := quadraticDiscrepancyParameter a
  let t := cubicLocalCountExponent alpha
  let D := cubicLocalCountConstant alpha
  have ha : 0 < a := cubicLocalQuadraticParameter_pos hα
  have haone : a ≤ 1 := cubicLocalQuadraticParameter_le_one hα.le hαone
  have hb : 0 < b := by dsimp [b, quadraticDiscrepancyParameter]; positivity
  obtain ⟨ht, htone⟩ := cubicLocalCountExponent_bounds hα hαone
  have hD : 1 ≤ D := le_max_left _ _
  have hC : 0 < boundaryRefinementConstant (1 / 16) := section5LocalRefinementConstant_pos _ _
  obtain ⟨N₀, hN₀⟩ := cubic_nonuniformity_many_prime_models alpha
    (max 4 (quadraticExponentialThreshold a)) hα hαone
  refine ⟨N₀, fun N _ _ hN f hf hnot => ?_⟩
  obtain ⟨phi, K, l, Q, hpoly, hQ, hproper, hlength, B, hmass, hB⟩ := hN₀ N hN f hf hnot
  have hNr : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hlpos : (0 : Real) < l := (by positivity : 0 < (N : Real) ^ cubicLocalizationExponent alpha / 12).trans_le hlength
  have hlone : (1 : Real) ≤ l := by
    have hl : 0 < l := by exact_mod_cast hlpos
    exact_mod_cast (show 1 ≤ l by omega)
  have hli (i : Fin K) : (l : Real) ≤ (Q i).carrier.card := by
    rw [(hproper i).1]
    exact_mod_cast (show l ≤ (Q i).length by rcases (hproper i).2 with h | h <;> omega)
  let budget : Fin K → Real := fun i => D * (Q i).carrier.card / (l : Real) ^ t
  have hbudget (i : Fin K) : 1 ≤ budget i := by
    calc
      _ ≤ ((Q i).carrier.card : Real) / (l : Real) ^ t := one_le_linear_scale hlone (hli i) htone
      _ ≤ _ := by
        dsimp [budget]
        exact div_le_div_of_nonneg_right
          (by nlinarith only [mul_le_mul_of_nonneg_right hD (Nat.cast_nonneg (Q i).carrier.card)])
          (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hlocal (i : Fin K) (hi : i ∈ B) : ∃ J : Nat, ∃ R : Fin J → ModAP N,
      IsPartition (fun j => (R j).carrier) (Q i).carrier ∧
      (∀ j, (R j).IsProper) ∧ (J : Real) ≤ budget i ∧
      b * (Q i).carrier.card ≤ ∑ j, ‖∑ x ∈ (R j).carrier, phaseTwist f phi x‖ := by
    obtain ⟨M, hM, hT, hMlow, hMup, _, _, hnon⟩ := hB i hi
    letI : NeZero M := ⟨hM.ne_zero⟩
    letI : Fact M.Prime := ⟨hM⟩
    have hMfour : 4 ≤ M := by exact_mod_cast ((le_max_left _ _).trans hT : (4 : Real) ≤ M)
    have hthreshold : quadraticExponentialThreshold a ≤ (M : Real) := (le_max_right _ _).trans hT
    obtain ⟨J, R, hR, hRproper, hcount, hdis⟩ :=
      (quadratic_function_discrepancy_bound ha haone).progression_partition
        (Q i) (hproper i).1 hMfour (by omega) hthreshold (phaseTwist f phi) (phaseTwist_discValued hf phi) hnon
    have hMreal : (M : Real) ≤ 8 * (Q i).carrier.card := by rw [(hproper i).1]; exact_mod_cast hMup
    have hpower : (M : Real) ^ (1 - t) ≤ (8 : Real) ^ (1 - t) * ((Q i).carrier.card : Real) ^ (1 - t) := by
      rw [← Real.mul_rpow (by norm_num : (0 : Real) ≤ 8) (Nat.cast_nonneg _)]
      exact Real.rpow_le_rpow (Nat.cast_nonneg _) hMreal (by dsimp [t]; linarith)
    refine ⟨J, R, hR, hRproper, ?_, ?_⟩
    · calc
        (J : Real) ≤ 2 * boundaryRefinementConstant (1 / 16) * (M : Real) ^ (1 - t) := hcount
        _ ≤ 2 * boundaryRefinementConstant (1 / 16) *
            ((8 : Real) ^ (1 - t) * ((Q i).carrier.card : Real) ^ (1 - t)) :=
          mul_le_mul_of_nonneg_left hpower (by positivity)
        _ ≤ D * ((Q i).carrier.card : Real) ^ (1 - t) := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        _ ≤ D * (((Q i).carrier.card : Real) / (l : Real) ^ t) :=
          mul_le_mul_of_nonneg_left (rpow_count_le_linear_scale hlpos (hli i) ht.le) (by linarith)
        _ = budget i := by dsimp [budget]; ring
    · apply le_trans _ hdis
      apply mul_le_mul_of_nonneg_left _ hb.le
      rw [(hproper i).1]
      exact_mod_cast (show (Q i).length ≤ M by omega)
  obtain ⟨J, R, hR, _, hRproper, hcount, hdis⟩ := selected_discrepancy_refinement
    Q (phaseTwist f phi) B budget b hQ (fun i => (hproper i).1) hbudget hlocal
  refine ⟨phi, l, J, R, hpoly, hlength, hR, hRproper, ?_, ?_⟩
  · apply hcount.trans_eq
    dsimp [budget]
    rw [← Finset.sum_div, ← Finset.mul_sum, ← Nat.cast_sum, hQ.sum_card]
    simp [D, t]
  · have hm := mul_le_mul_of_nonneg_left hmass.le hb.le
    have hm' : cubicTwistedDiscrepancyParameter alpha * N ≤
        b * ∑ i ∈ B, ((Q i).carrier.card : Real) := by
      change (cubicLocalizedMassParameter alpha * b) * N ≤ _
      nlinarith only [hm]
    exact hm'.trans hdis

end LeanProofs.GowersSzemeredi

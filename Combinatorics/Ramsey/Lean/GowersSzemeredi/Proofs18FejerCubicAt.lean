import GowersSzemeredi.Proofs18GeneralPhaseInverseAssembly
import GowersSzemeredi.Proofs18FejerCubicParameters
import GowersSzemeredi.Proofs17FejerCubicLocalization

/-! The Fejér cubic chain at any square exponent (Notes L.7c, P4–P9).

The corpus derives the cubic function discrepancy bound
`fejer_cubic_function_discrepancy_bound` from the Fejér square extraction
`theorem_13_12_fejer_extraction_explicit`. Every step in between (the odd
square, cubic localization, the many prime models, the twisted partition and
the untwisting) fixes the exponent
`fejerCubicLocalizationExponent α = (1/2)^((2/α)^(2^53))`. That double
exponential becomes the discrepancy exponent σ of degree three.

None of those steps uses the shape of the exponent. Here the chain starts
from an abstract square extraction:
* `FejerSquareAt α e T`: above `T`, a cubically non-uniform disc-valued
  function has a Fejér square of side at least `N^e`;
* `FejerOddSquareAt α e T`: the odd-square form consumed by the Section 17
  localization.

The chain ends in `FejerSquareAt.functionDiscrepancyBound`:
`FunctionDiscrepancyBound 3 α β σ T'` with the corpus's β and with
`σ = phaseInverseExponent 3 (e·κ)`, where `κ` is the corpus local count
exponent. The corpus bound is the instance at `fejerSquareAt_corpus`.

`fejerSquareAt_corpus` is in `Proofs18FejerCubicAtSide`, outside the final
route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open scoped BigOperators

/-- A smaller exponent is weaker. -/
theorem FejerSquareAt.mono {alpha e e' T : Real} (h : FejerSquareAt alpha e T) (he : e' ≤ e) :
    FejerSquareAt alpha e' (max 1 T) := by
  intro N _ _ hN f hf hnot
  obtain ⟨P, Q, B, phi, h1, h2, h3, h4, h5, hsize, h7, h8, h9, h10⟩ :=
    h N ((le_max_right _ _).trans hN) f hf hnot
  have hN1 : (1 : Real) ≤ N := (le_max_left _ _).trans hN
  exact ⟨P, Q, B, phi, h1, h2, h3, h4, h5,
    (Real.rpow_le_rpow_of_exponent_le hN1 he).trans hsize, h7, h8, h9, h10⟩

def fejerCubicPrimeModelThresholdAt (e T₀ T : Real) : Real :=
  max 256 (max T₀ (positivePowerThreshold (12 * max 2 T) 1 e))

def fejerCubicTwistedThresholdAt (alpha e T₀ : Real) : Real :=
  fejerCubicPrimeModelThresholdAt e T₀
    (max 4 (quadraticExponentialThreshold (fejerCubicLocalQuadraticParameter alpha)))

/-- **The twisted discrepancy partition** at any odd-square exponent. -/
theorem FejerOddSquareAt.twistedDiscrepancy {alpha e T₀ : Real} (h : FejerOddSquareAt alpha e T₀)
    (hα : 0 < alpha) (hαone : alpha ≤ 1) (he : 0 < e) :
    ∀ (N : Nat) [NeZero N] [Fact N.Prime], fejerCubicTwistedThresholdAt alpha e T₀ ≤ (N : Real) →
      ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha 3 →
      ∃ phi : ZMod N → ZMod N, ∃ l J : Nat, ∃ R : Fin J → ModAP N,
        PolynomialOn 3 Finset.univ phi ∧
        (N : Real) ^ e / 12 ≤ l ∧
        IsPartition (fun j => (R j).carrier) Finset.univ ∧
        (∀ j, (R j).IsProper) ∧
        (J : Real) ≤ fejerCubicLocalCountConstant alpha * N /
          (l : Real) ^ fejerCubicLocalCountExponent alpha ∧
        fejerCubicTwistedDiscrepancyParameter alpha * N ≤
          ∑ j, ‖∑ x ∈ (R j).carrier, phaseTwist f phi x‖ := by
  let a := fejerCubicLocalQuadraticParameter alpha
  let eta := (2 : Real) ^ (-(58 : Int)) * alpha ^ 2 * (alpha / 2) ^ ((2 : Nat) ^ 42)
  let T := max 4 (quadraticExponentialThreshold a)
  have ha : 0 < a := fejerCubicLocalQuadraticParameter_pos hα
  obtain ⟨ht, htone⟩ : 0 < quadraticDiscrepancyExponent a / 16 ∧
      quadraticDiscrepancyExponent a / 16 ≤ 1 := fejerCubicLocalCountExponent_bounds hα hαone
  have hparam : (eta / 2) / (2 * (2 + 2 : Nat) : Real) ^ (2 + 2) = a := by
    dsimp [eta, a, fejerCubicLocalQuadraticParameter]
    generalize (alpha / 2) ^ ((2 : Nat) ^ 42) = z
    norm_num
    ring
  have hbound : FunctionDiscrepancyBound 2
      ((eta / 2) / (2 * (2 + 2 : Nat) : Real) ^ (2 + 2)) (quadraticDiscrepancyParameter a)
      (quadraticDiscrepancyExponent a) (quadraticExponentialThreshold a) := by
    rw [hparam]
    exact quadratic_function_discrepancy_bound ha
      (fejerCubicLocalQuadraticParameter_le_one hα.le hαone)
  intro N _ _ hN f hf hnot
  obtain ⟨phi, K, l, Q, hpoly, hQ, hproper, hlength, hupper, hfail⟩ :=
    h.localized hα N ((le_max_left _ _).trans ((le_max_right _ _).trans hN)) f hf hnot
  have hlarge : 12 * max 2 T ≤ (N : Real) ^ e := by
    simpa only [one_mul] using positivePowerThreshold_spec zero_lt_one he
      ((le_max_right _ _).trans ((le_max_right _ _).trans hN) :
        positivePowerThreshold (12 * max 2 T) 1 e ≤ (N : Real))
  have hlmax : max 2 T ≤ (l : Real) := by linarith only [hlarge, hlength]
  have hl : 2 ≤ l := by exact_mod_cast ((le_max_left 2 T).trans hlmax)
  have hT : quadraticExponentialThreshold a ≤ (l : Real) :=
    (le_max_right _ _).trans ((le_max_right 2 T).trans hlmax)
  -- `4 ≤ √N`, so a cell of length at most `√N` fits four times
  have hroot : (4 : Real) ≤ Real.sqrt N :=
    Real.le_sqrt_of_sq_le (by linarith [(le_max_left _ _).trans hN])
  have hgeom (i : Fin K) : l ≤ (Q i).length ∧ (Q i).length ≤ l + 1 ∧
      (2 + 2) * (Q i).length ≤ N := by
    have hs : (4 : Real) * (Q i).length ≤ N := (mul_le_mul hroot (hupper i) (by positivity)
      (by positivity)).trans_eq (Real.mul_self_sqrt (Nat.cast_nonneg _))
    have hs' : 4 * (Q i).length ≤ N := by exact_mod_cast hs
    rcases (hproper i).2 with hi | hi <;> omega
  obtain ⟨J, R, hR, hp, hc, hd⟩ := hbound.localized_partition (by positivity)
    (by unfold quadraticDiscrepancyParameter; positivity) (by linarith) (by linarith)
    (phaseTwist f phi) (phaseTwist_discValued hf phi) Q hQ (fun i => (hproper i).1) hl hT
    (by omega) hgeom hfail
  simp only [show (2 * (2 + 2 : Nat) : Real) = 8 by norm_num] at hc
  have hmass : eta / 2 = fejerCubicLocalizedMassParameter alpha := by
    dsimp [eta, fejerCubicLocalizedMassParameter]
    generalize (alpha / 2) ^ ((2 : Nat) ^ 42) = z
    norm_num
    ring
  refine ⟨phi, l, J, R, hpoly, hlength, hR, hp, hc, ?_⟩
  rwa [mul_div_right_comm, hmass] at hd

/-- The common-cell-length count as a power of the modulus, at any exponent. -/
theorem fejer_cubic_twisted_count_power_at {alpha e : Real} (hα : 0 < alpha)
    (hαone : alpha ≤ 1) {N l J : Nat} [NeZero N]
    (hl : (N : Real) ^ e / 12 ≤ l)
    (hcount : (J : Real) ≤ fejerCubicLocalCountConstant alpha * N /
      (l : Real) ^ fejerCubicLocalCountExponent alpha) :
    (J : Real) ≤ fejerCubicTwistedCountConstant alpha *
      (N : Real) ^ (1 - e * fejerCubicLocalCountExponent alpha) := by
  exact partition_count_power_of_length (fejerCubicLocalCountExponent_bounds hα hαone).1.le
    (zero_le_one.trans (le_max_left _ _)) (by norm_num) hl hcount

/-- The degree-three discrepancy exponent from a square exponent `e`. -/
def fejerCubicDiscrepancyExponentAt (alpha e : Real) : Real :=
  phaseInverseExponent 3 (e * fejerCubicLocalCountExponent alpha)

def fejerCubicInverseThresholdAt (alpha e T₀ : Real) : Real :=
  max (fejerCubicTwistedThresholdAt alpha e T₀)
    (positivePowerThreshold
      (phaseInverseConstant 3 (fejerCubicTwistedDiscrepancyParameter alpha)
        (fejerCubicTwistedCountConstant alpha)) 1
      (fejerCubicDiscrepancyExponentAt alpha e))

/-- **The cubic function discrepancy bound** from an odd square at exponent `e`. -/
theorem FejerOddSquareAt.functionDiscrepancyBound {alpha e T₀ : Real}
    (h : FejerOddSquareAt alpha e T₀) (hα : 0 < alpha) (hαone : alpha ≤ 1) (he : 0 < e) :
    FunctionDiscrepancyBound 3 alpha (fejerCubicDiscrepancyParameter alpha)
      (fejerCubicDiscrepancyExponentAt alpha e) (fejerCubicInverseThresholdAt alpha e T₀) := by
  let et := e * fejerCubicLocalCountExponent alpha
  let beta := fejerCubicTwistedDiscrepancyParameter alpha
  let D := fejerCubicTwistedCountConstant alpha
  have het : 0 < et := mul_pos he (fejerCubicLocalCountExponent_bounds hα hαone).1
  have hβ : 0 < beta := by
    have h2 := fejerCubicDiscrepancyParameter_pos hα
    change 0 < beta / 2 at h2
    linarith only [h2]
  have hD : 0 < D := by
    dsimp [D, fejerCubicTwistedCountConstant, fejerCubicLocalCountConstant]
    positivity
  intro N _ _ hN f hf hnot
  obtain ⟨phi, l, K, Q, hpoly, hlength, hQ, _, hcount, hdis⟩ :=
    h.twistedDiscrepancy hα hαone he N ((le_max_left _ _).trans hN) f hf hnot
  have hcount' : (K : Real) ≤ D * (N : Real) ^ (1 - et) :=
    fejer_cubic_twisted_count_power_at hα hαone hlength hcount
  exact polynomial_phase_inverse_partition (by omega : 1 ≤ 3) het hβ hD f hf
    Q (fun _ => phi) (fun _ => hpoly) hQ hcount' hdis ((le_max_right _ _).trans hN)

/-- **From a square extraction to the cubic discrepancy bound**, at any
square exponent in `(0, 1/2]`. -/
theorem FejerSquareAt.functionDiscrepancyBound {alpha e T : Real} (h : FejerSquareAt alpha e T)
    (hα : 0 < alpha) (hαone : alpha ≤ 1) (he : 0 < e) (hehalf : e ≤ 1 / 2) :
    FunctionDiscrepancyBound 3 alpha (fejerCubicDiscrepancyParameter alpha)
      (fejerCubicDiscrepancyExponentAt alpha e)
      (fejerCubicInverseThresholdAt alpha e (max T (positivePowerThreshold 4 1 e))) :=
  (h.oddSquare hα he hehalf).functionDiscrepancyBound hα hαone he

end LeanProofs.GowersSzemeredi

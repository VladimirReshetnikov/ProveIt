import IPRADerivations.Analysis.Polynomials.RootFinding.DominantTerms.DominantBounds.GaussianDominantPlateauValues
import IPRADerivations.Analysis.Polynomials.RootFinding.DominantTerms.DominantBounds.GaussianTranslatedDominantPlateau

/-!
# Actual geometric squared-score bounds away from the dominant degree

Dominance at the next smaller radius bounds degrees below the winner;
dominance at the previous larger radius bounds degrees above it. The
result is a literal rational comparison with factor 16^|i-k|, the square
of the source's 4^|i-k| norm weight. All original independent denominators
are retained. The final producers derive their comparisons from the
actual plateau, with no incoming geometric-weight premise.

The finite Gaussian sum and its 2/3 norm bound are separate obligations.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianDominantScoreWeights

open_ipra
open LeanProofs.IPRA.Analysis.GaussianDominantSyntax
  (four score numerator denominator score_represents denominator_positive)
open LeanProofs.IPRA.Analysis.GaussianBalancedRadiusSyntax (unit unit_positive input)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (fraction fraction_represents)
open LeanProofs.IPRA.Analysis.GaussianDominantScaleArithmetic (denominator_succ)
open LeanProofs.IPRA.Analysis.GaussianDominantPlateau (center winner)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def weight (d : PTm n) : PTm n := unit (four*d)
def weightedScore (C N E j h i d : PTm n) : PTm n :=
  RationalArithmetic.multiply (fraction (weight d) one) (score C N E j h i)

ipra_subst weight
ipra_subst weightedScore

theorem scale_gap (i k : PTm n) (hik : Γ ⊢[PRAAx] le i k) : Γ ⊢[PRAAx]
    unit (four*k) ≐ unit (four*i)*weight (monus k i) := by
  have ex : Γ ⊢[PRAAx] four*k ≐ four*i+four*monus k i :=
    (congrMul (.eqRefl four) (eq_add_of_le hik)).eqTrans (by ipra_ring)
  exact (congrAp2 powF ex (.eqRefl two)).eqTrans (pw_add two _ _)

theorem weighted_represents (C N E j h i d : PTm n) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (weightedScore C N E j h i d)
      (ZT.ofNat (weight d*numerator C N j i)) (denominator C N E h i) := by
  have raw := RationalRepresentations.represents_multiply (Γ := Γ) _ _ _ _ _ _
    (fraction_represents (weight d) one (le_refl one)) (score_represents C N E j h i)
  apply GaussianRationalHorner.scalar_congr (.eqRefl _) (hAB := one_mul _) (h := raw)
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  ipra_simps

/-- At degrees below k, the comparison one scale later gives the exact
16^(k-i) bound at the original scale. Only a positive scale factor is
cancelled, so zero coefficients remain covered. -/
theorem below_from_next (C N E j h i k : PTm n) (hik : Γ ⊢[PRAAx] le i k)
    (hNext : Γ ⊢[PRAAx] RationalArgmin.rationalLE (score C N E j (succ h) i) (score C N E j (succ h) k)) :
    Γ ⊢[PRAAx] RationalArgmin.rationalLE
      (weightedScore C N E j h i (monus k i)) (score C N E j h k) := by
  have raw := GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _
    (score_represents C N E j (succ h) i) (score_represents C N E j (succ h) k) hNext
  have stepped := le_congr (congrMul (denominator_succ C N E h k) (.eqRefl _))
    (congrMul (.eqRefl _) (denominator_succ C N E h i)) raw
  have split := le_congr (congrMul (congrMul (.eqRefl _) (scale_gap i k hik)) (.eqRefl _))
    (.eqRefl _) stepped
  have cancelled : Γ ⊢[PRAAx] le
      (denominator C N E h k*(weight (monus k i)*numerator C N j i))
      (numerator C N j k*denominator C N E h i) :=
    RationalValueBounds.positive_cancel (unit_positive (four*i))
      (le_congr (by ipra_ring) (by ipra_ring) split)
  exact GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _
    (denominator_positive C N E h i) (denominator_positive C N E h k)
    (weighted_represents C N E j h i (monus k i)) (score_represents C N E j h k) cancelled

/-- At degrees above k, the old comparison gives the exact 16^(i-k)
bound at the next scale. This uses the actual denominator update. -/
theorem above_from_previous (C N E j h i k : PTm n) (hki : Γ ⊢[PRAAx] le k i)
    (hOld : Γ ⊢[PRAAx] RationalArgmin.rationalLE (score C N E j h i) (score C N E j h k)) :
    Γ ⊢[PRAAx] RationalArgmin.rationalLE
      (weightedScore C N E j (succ h) i (monus i k)) (score C N E j (succ h) k) := by
  have raw := GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _
    (score_represents C N E j h i) (score_represents C N E j h k) hOld
  have scaled := mul_le_mul_right (unit (four*k)*weight (monus i k)) raw
  have target : Γ ⊢[PRAAx] le
      (denominator C N E (succ h) k*(weight (monus i k)*numerator C N j i))
      (numerator C N j k*denominator C N E (succ h) i) := by
    apply le_congr (congrMul (denominator_succ C N E h k) (.eqRefl _)).eqSymm
      (congrMul (.eqRefl _) (denominator_succ C N E h i)).eqSymm
    apply le_congr (.eqRefl _) (congrMul (.eqRefl _) (congrMul (.eqRefl _) (scale_gap k i hki))).eqSymm
    exact le_congr (by ipra_ring) (by ipra_ring) scaled
  exact GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _
    (denominator_positive C N E (succ h) i) (denominator_positive C N E (succ h) k)
    (weighted_represents C N E j (succ h) i (monus i k)) (score_represents C N E j (succ h) k) target

def atCenter (C N i d : PTm n) : PTm n := weightedScore C N
  (GaussianBalancedRadiusHeight.E C N) (GaussianBalancedRadiusSearch.radiusIndex C N) (center C N) i d

ipra_subst atCenter

theorem below_weight (C N i : PTm n) (hInput : Γ ⊢[PRAAx] input C N)
    (hi : Γ ⊢[PRAAx] le one i) (hiN : Γ ⊢[PRAAx] le i N) (hik : Γ ⊢[PRAAx] le i (winner C N)) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (atCenter C N i (monus (winner C N) i))
      (GaussianDominantRadiusValues.score C N (center C N) (winner C N)) :=
  below_from_next _ _ _ _ _ _ _ hik (GaussianDominantRadiusValues.dominates_at C N
    (succ (center C N)) (winner C N) i (GaussianDominantPlateauValues.right_dominates C N hInput) hi hiN)

theorem above_weight (C N i : PTm n) (hInput : Γ ⊢[PRAAx] input C N)
    (hi : Γ ⊢[PRAAx] le one i) (hiN : Γ ⊢[PRAAx] le i N) (hki : Γ ⊢[PRAAx] le (winner C N) i) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (atCenter C N i (monus i (winner C N)))
      (GaussianDominantRadiusValues.score C N (center C N) (winner C N)) := by
  have previous := GaussianDominantRadiusValues.dominates_at C N (pred (center C N)) (winner C N) i
    (GaussianDominantPlateauValues.left_dominates C N hInput) hi hiN
  have bound := above_from_previous C N (GaussianBalancedRadiusHeight.E C N)
    (GaussianBalancedRadiusSearch.radiusIndex C N) (pred (center C N)) i (winner C N) hki previous
  have scoreEq (r : PTm n) : Γ ⊢[PRAAx]
      score C N (GaussianBalancedRadiusHeight.E C N) (GaussianBalancedRadiusSearch.radiusIndex C N)
        (succ (pred (center C N))) r ≐ GaussianDominantRadiusValues.score C N (center C N) r :=
    GaussianDominantSelector.score_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _)
      (GaussianDominantPlateauValues.center_succ_pred C N) (.eqRefl _)
  exact RationalArgmin.rationalLE_congr (RationalAlgebra.multiply_congr (.eqRefl _) (scoreEq i))
    (scoreEq (winner C N)) bound

/-- These are the two actual per-coefficient squared geometric bounds.
The equality case is included; every strictly off-dominant degree is
covered by the corresponding branch. -/
def weightBounds (C N : PTm n) : Fm PTm n := .all
  (le one (var 0) ⟶ le (var 0) (Syn.shift N) ⟶
    ((le (var 0) (winner (Syn.shift C) (Syn.shift N)) ⟶
        RationalArgmin.rationalLE
          (atCenter (Syn.shift C) (Syn.shift N) (var 0) (monus (winner (Syn.shift C) (Syn.shift N)) (var 0)))
          (GaussianDominantRadiusValues.score (Syn.shift C) (Syn.shift N)
            (center (Syn.shift C) (Syn.shift N)) (winner (Syn.shift C) (Syn.shift N)))) ⋏
      (le (winner (Syn.shift C) (Syn.shift N)) (var 0) ⟶
        RationalArgmin.rationalLE
          (atCenter (Syn.shift C) (Syn.shift N) (var 0) (monus (var 0) (winner (Syn.shift C) (Syn.shift N))))
          (GaussianDominantRadiusValues.score (Syn.shift C) (Syn.shift N)
            (center (Syn.shift C) (Syn.shift N)) (winner (Syn.shift C) (Syn.shift N))))))

ipra_subst weightBounds [Syn.subst_shift, Syn.shift_subst]

theorem actual_weight_bounds (C N : PTm n) (hInput : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx]
    weightBounds C N := by
  refine .allI (.impI (.impI (.andI (.impI ?_) (.impI ?_))))
  all_goals
    have shifted : Γ.map Fm.shift ⊢[PRAAx] input (Syn.shift C) (Syn.shift N) := by
      simpa only [Fm.shift,GaussianBalancedRadiusSyntax.subst_input,Syn.shift] using hInput.shift
  · exact below_weight (Syn.shift C) (Syn.shift N) (var 0) shifted.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0
  · exact above_weight (Syn.shift C) (Syn.shift N) (var 0) shifted.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

theorem original_input_weights (C N z : PTm n)
    (hInput : Γ ⊢[PRAAx] GaussianTranslatedBalancedRadius.inputContract C N)
    (hPositive : Γ ⊢[PRAAx] le one (GaussianTranslatedBalancedRadius.residual C z)) : Γ ⊢[PRAAx]
    weightBounds (GaussianRationalTranslation.translated C N z) N :=
  actual_weight_bounds _ _ (GaussianTranslatedDominantPlateau.positive_input C N z hInput hPositive)

theorem below_next_scale_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (le (var 5) (var 6) ⟶
      RationalArgmin.rationalLE (score (var 0) (var 1) (var 2) (var 3) (succ (var 4)) (var 5))
        (score (var 0) (var 1) (var 2) (var 3) (succ (var 4)) (var 6)) ⟶
      RationalArgmin.rationalLE
        (weightedScore (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (monus (var 6) (var 5)))
        (score (var 0) (var 1) (var 2) (var 3) (var 4) (var 6))) :=
  closeUniv 7 (.impI (.impI (below_from_next _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem above_previous_scale_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (le (var 6) (var 5) ⟶
      RationalArgmin.rationalLE (score (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
        (score (var 0) (var 1) (var 2) (var 3) (var 4) (var 6)) ⟶
      RationalArgmin.rationalLE
        (weightedScore (var 0) (var 1) (var 2) (var 3) (succ (var 4)) (var 5) (monus (var 5) (var 6)))
        (score (var 0) (var 1) (var 2) (var 3) (succ (var 4)) (var 6))) :=
  closeUniv 7 (.impI (.impI (above_from_previous _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_geometric_score_weights_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (input (var 0) (var 1) ⟶ weightBounds (var 0) (var 1)) :=
  closeUniv 2 (.impI (actual_weight_bounds _ _ Prf.hyp0))

theorem original_geometric_score_weights_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (GaussianTranslatedBalancedRadius.inputContract (var 0) (var 1) ⟶
      le one (GaussianTranslatedBalancedRadius.residual (var 0) (var 2)) ⟶
      weightBounds (GaussianRationalTranslation.translated (var 0) (var 1) (var 2)) (var 1)) :=
  closeUniv 3 (.impI (.impI (original_input_weights _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianDominantScoreWeights

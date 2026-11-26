import IPRADerivations.Analysis.Polynomials.RootFinding.DominantTerms.GaussianDominantAlpha
import IPRADerivations.Analysis.Polynomials.RootFinding.DominantTerms.GaussianDominantMagnitude
import IPRADerivations.Analysis.RationalArithmetic.Directions.GaussianRationalDirection

/-!
# Actual selected data for the dominant-term direction

The original positive-residual coefficient list determines b0, bk, the
positive winning degree, radius, phase, direction, and normalizer data.
The existing strict dominant bound supplies the lower radial comparison.
All generic alpha and direction inputs are derived from the original
balanced-radius input; none is supplied as a new phase or score premise.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianDominantDirectionData

open_ipra
open LeanProofs.IPRA.Analysis.GaussianBalancedRadiusSyntax (input coefficient unit unit_positive)
open LeanProofs.IPRA.Analysis.GaussianDominantPlateau (winner)
open LeanProofs.IPRA.Analysis.GaussianOffDominantTerms (radiusNumerator radiusDenominator)
open LeanProofs.IPRA.Analysis.GaussianOffDominantSum (selectedScore)
open LeanProofs.IPRA.Analysis.GaussianRationalDirectionNormalizer (norm)
open LeanProofs.IPRA.Analysis.GaussianDescentClockArithmetic (descentD)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def base (C N : PTm n) : PTm n := coefficient C N zero
def chosen (C N : PTm n) : PTm n := coefficient C N (winner C N)
def phase (C N : PTm n) : PTm n := GaussianDominantAlpha.phase (base C N) (chosen C N)
def precision (C N : PTm n) : PTm n := GaussianRationalDirectionClock.height (winner C N) (num 16)
def direction (C N : PTm n) : PTm n := GaussianRationalDirectionConstruction.direction (phase C N) (winner C N) (num 16)
def target (C N : PTm n) : PTm n := GaussianRationalDirectionNormalizer.target (phase C N) (precision C N)
def P (C N : PTm n) : PTm n := GaussianDominantAlpha.P (base C N) (chosen C N) (radiusNumerator C N) (winner C N) (precision C N)
def Q (C N : PTm n) : PTm n := GaussianDominantAlpha.Q (base C N) (chosen C N) (radiusDenominator C N) (winner C N) (precision C N)

ipra_subst base
ipra_subst chosen
ipra_subst phase
ipra_subst precision
ipra_subst direction
ipra_subst target
ipra_subst P
ipra_subst Q

theorem base_positive (C N : PTm n) (h : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx] le one (norm (base C N)) :=
  Prf.andE₁ (Prf.andE₂ (Prf.andE₂ h))

theorem chosen_positive (C N : PTm n) (h : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx] le one (norm (chosen C N)) :=
  GaussianDominantPlateauValues.winner_raw_positive C N h

theorem phase_positive (C N : PTm n) (h : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx] le one (norm (phase C N)) :=
  GaussianDominantAlpha.phase_positive _ _ (base_positive C N h) (chosen_positive C N h)

theorem numerator_positive (C N : PTm n) : Γ ⊢[PRAAx] le one (radiusNumerator C N) := unit_positive _
theorem denominator_positive (C N : PTm n) : Γ ⊢[PRAAx] le one (radiusDenominator C N) := unit_positive _

theorem degree_positive (C N : PTm n) (h : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx] le one (winner C N) :=
  Prf.andE₁ (GaussianDominantPlateau.winner_bounds C N h)

theorem clock_positive (N : PTm n) : Γ ⊢[PRAAx] le one (descentD N) :=
  le_congr (.eqRefl _) (GaussianDominantMagnitude.descent_dyadic N).eqSymm (unit_positive _)

theorem precision_large (C N : PTm n) : Γ ⊢[PRAAx] le GaussianRationalDirectionNormalizer.sixtyFour (precision C N) :=
  GaussianRationalDirectionConstruction.grid_large _ _

theorem source_input (C N : PTm n) (h : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx]
    GaussianRationalDirection.input (phase C N) (winner C N) one (num 16) :=
  .andI (phase_positive C N h) (.andI (degree_positive C N h) (.andI (le_refl one)
    (le_congr (by ipra_ring) (.eqRefl _) (le_refl (num 16)))))

theorem source_direction (C N : PTm n) (h : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx]
    GaussianRationalDirection.certificate (phase C N) (winner C N) one (num 16) :=
  GaussianRationalDirection.rational_direction _ _ _ _ (source_input C N h)

theorem direction_unit (C N : PTm n) : Γ ⊢[PRAAx] GaussianRationalHalfAngle.unit (direction C N) :=
  GaussianRationalDirectionConstruction.output_unit _ _ _

theorem direction_error (C N : PTm n) (h : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx]
    GaussianRationalMetric.distanceBounded (GaussianRationalReciprocal.power (direction C N) (winner C N))
      (target C N) one (GaussianDominantSyntax.four*(num 16)) :=
  GaussianRationalDirectionConstruction.power_close_normalized _ _ _ (phase_positive C N h) (degree_positive C N h)
    (le_of_eq_add (d := num 15) (by ipra_ring))

theorem radial_score (C N : PTm n) : Γ ⊢[PRAAx]
    GaussianDominantAlpha.radialScore (chosen C N) (radiusNumerator C N) (radiusDenominator C N) (winner C N) ≐ selectedScore C N :=
  (RationalAlgebra.multiply_commutative _ _).eqTrans
    ((GaussianOffDominantTerms.reference_norm_general C N (radiusNumerator C N) (radiusDenominator C N) (winner C N)
      (denominator_positive C N)).eqSymm.eqTrans (GaussianOffDominantTerms.selected_reference_norm C N))

theorem radial_upper (C N : PTm n) (h : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx]
    GaussianDominantAlpha.radialUpper (base C N) (chosen C N) (radiusNumerator C N) (radiusDenominator C N) (winner C N) :=
  RationalArgmin.rationalLE_congr (radial_score C N).eqSymm (.eqRefl _) (GaussianDominantMagnitude.dominant_upper C N h)

theorem radial_lower (C N : PTm n) (h : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx]
    GaussianDominantAlpha.radialLower (base C N) (chosen C N) (radiusNumerator C N) (radiusDenominator C N) (winner C N) (descentD N) := by
  have strict := GaussianDominantMagnitude.dominant_lower C N h
  have ordered : Γ ⊢[PRAAx] RationalArgmin.rationalLE (GaussianDominantMagnitude.constantScore C N)
      (GaussianDominantMagnitude.multiple (GaussianDominantMagnitude.squaredBudget N) (selectedScore C N)) :=
    .orE (RationalArgmin.total _ _) (.botE _ (.impE strict.wk Prf.hyp0)) Prf.hyp0
  exact RationalArgmin.rationalLE_congr (.eqRefl _)
    (RationalAlgebra.multiply_congr (.eqRefl _) (radial_score C N).eqSymm) ordered

def alphaCertificate (C N : PTm n) : Fm PTm n := le one (Q C N) ⋏
  (le one (P C N) ⋏ (le (P C N) (Q C N) ⋏
    le (GaussianRationalDirectionNormalizer.sixtyFour*Q C N)
      (GaussianRationalDirectionNormalizer.sixtyFive*descentD N*P C N)))
ipra_subst alphaCertificate

/-- The selected original polynomial data discharge all generic alpha
assumptions, including both radial comparisons and phase nonzeroness. -/
theorem alpha_correct (C N : PTm n) (h : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx] alphaCertificate C N :=
  GaussianDominantAlpha.alpha_bounds _ _ _ _ _ _ _ (numerator_positive C N) (denominator_positive C N)
    (precision_large C N) (clock_positive N) (base_positive C N h) (chosen_positive C N h)
    (radial_upper C N h) (radial_lower C N h)

theorem alpha_denominator_positive (C N : PTm n) (h : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx] le one (Q C N) :=
  Prf.andE₁ (alpha_correct C N h)
theorem alpha_numerator_positive (C N : PTm n) (h : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx] le one (P C N) :=
  Prf.andE₁ (Prf.andE₂ (alpha_correct C N h))
theorem alpha_le_one (C N : PTm n) (h : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx] le (P C N) (Q C N) :=
  Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (alpha_correct C N h)))
theorem alpha_lower_bound (C N : PTm n) (h : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx]
    le (GaussianRationalDirectionNormalizer.sixtyFour*Q C N)
      (GaussianRationalDirectionNormalizer.sixtyFive*descentD N*P C N) :=
  Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (alpha_correct C N h)))

theorem radial_relative (C N : PTm n) (h : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE
      (RationalArithmetic.multiply (GaussianEuclideanDistanceName.fraction
        ((GaussianRationalDirectionNormalizer.sixtyFour*Q C N)*(GaussianRationalDirectionNormalizer.sixtyFour*Q C N)) one)
        (selectedScore C N))
      (RationalArithmetic.multiply (GaussianEuclideanDistanceName.fraction
        ((GaussianRationalDirectionNormalizer.sixtyFive*P C N)*(GaussianRationalDirectionNormalizer.sixtyFive*P C N)) one)
        (GaussianRationalMetric.qnormSq (base C N))) :=
  RationalArgmin.rationalLE_congr (RationalAlgebra.multiply_congr (.eqRefl _) (radial_score C N)) (.eqRefl _)
    (GaussianDominantAlpha.radial_relative_alpha _ _ _ _ _ _ (denominator_positive C N)
      (base_positive C N h) (chosen_positive C N h) (precision_large C N))

def output (C N : PTm n) : PTm n := pairT (P C N) (pairT (Q C N) (pairT (direction C N)
  (pairT (phase C N) (pairT (target C N) (pairT (chosen C N) (pairT (winner C N)
    (pairT (radiusNumerator C N) (radiusDenominator C N))))))))
def outputF : PR 2 := PTm.toPR (output (var 0) (var 1))
def run (C N : PTm n) : PTm n := ap2 outputF C N

ipra_subst output
ipra_subst run
theorem program_at (C N : PTm n) : Γ ⊢[PRAAx] run C N ≐ output C N := by
  simpa [run,outputF,ap2] using toPR_eq (Γ := Γ) (output (var 0) (var 1) : PTm 2) ![C,N]

theorem returned_numerator (C N : PTm n) : Γ ⊢[PRAAx] fstT (run C N) ≐ P C N :=
  (program_at C N).fstE

theorem returned_denominator (C N : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run C N)) ≐ Q C N :=
  (program_at C N).sndE.fstE

theorem returned_direction (C N : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run C N))) ≐ direction C N :=
  (program_at C N).sndE.sndE.fstE

theorem returned_phase (C N : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (run C N)))) ≐ phase C N :=
  (program_at C N).sndE.sndE.sndE.fstE

theorem returned_target (C N : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (sndT (run C N))))) ≐ target C N :=
  (program_at C N).sndE.sndE.sndE.sndE.fstE

theorem returned_coefficient (C N : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (sndT (sndT (run C N)))))) ≐ chosen C N :=
  (program_at C N).sndE.sndE.sndE.sndE.sndE.fstE

theorem returned_degree (C N : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (sndT (sndT (sndT (run C N))))))) ≐ winner C N :=
  (program_at C N).sndE.sndE.sndE.sndE.sndE.sndE.fstE

theorem returned_radiusNumerator (C N : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (sndT (sndT (sndT (sndT (run C N)))))))) ≐ radiusNumerator C N :=
  (program_at C N).sndE.sndE.sndE.sndE.sndE.sndE.sndE.fstE

theorem returned_radiusDenominator (C N : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (sndT (sndT (sndT (sndT (sndT (run C N)))))))) ≐ radiusDenominator C N :=
  (program_at C N).sndE.sndE.sndE.sndE.sndE.sndE.sndE.sndE

theorem selected_direction_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (input (var 0) (var 1) ⟶ GaussianRationalDirection.certificate
      (phase (var 0) (var 1)) (winner (var 0) (var 1)) one (num 16)) :=
  closeUniv 2 (.impI (source_direction _ _ Prf.hyp0))
theorem selected_alpha_bounds_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (input (var 0) (var 1) ⟶ alphaCertificate (var 0) (var 1)) :=
  closeUniv 2 (.impI (alpha_correct _ _ Prf.hyp0))
theorem selected_direction_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (run (var 0) (var 1) ≐ output (var 0) (var 1)) := closeUniv 2 (program_at _ _)

end LeanProofs.IPRA.Analysis.GaussianDominantDirectionData

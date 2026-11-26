import IPRADerivations.Analysis.Geometry.GeometricBounds.GaussianGeometricSumBound
import IPRADerivations.Analysis.Polynomials.RootFinding.DominantTerms.GaussianOffDominantTerms

/-!
# The actual off-dominant Gaussian sum at the computed plateau

The original coefficient list and displacement determine both lists of
off-dominant terms. Genuine adjacent-scale dominance supplies every
geometric comparison, and the computed common-denominator sum theorem
gives the literal bound 9*normSq(otherSum) <= 4*selectedScore.

The only displacement assumption is the legitimate local disk condition
|delta| <= the computed central radius. No individual term, weight, prefix,
sum, denominator, search-success or desired output bound is supplied.
This proves the norm estimate needed for the source contraction, uniformly
in the displacement; the polynomial decomposition and direction are separate.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianOffDominantSum

open_ipra
open LeanProofs.IPRA.Analysis.GaussianBalancedRadiusSyntax (input)
open LeanProofs.IPRA.Analysis.GaussianDominantPlateau (center winner)
open LeanProofs.IPRA.Analysis.GaussianOffDominantTerms (withinRadius selectedReference)
open LeanProofs.IPRA.Analysis.GaussianRationalNormClearing (weightedNorm nine)
open LeanProofs.IPRA.Analysis.GaussianDominantSyntax (four)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (fraction)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def lower (C N delta : PTm n) : PTm n := GaussianOffDominantTerms.lowerList C N delta (winner C N)
def upper (C N delta : PTm n) : PTm n := GaussianOffDominantTerms.upperList C N delta (winner C N)
def otherSum (C N delta : PTm n) : PTm n := GaussianGeometricSumBound.otherSum (lower C N delta) (upper C N delta)
def selectedScore (C N : PTm n) : PTm n := GaussianDominantRadiusValues.score C N (center C N) (winner C N)
def denominator (C N delta : PTm n) : PTm n := GaussianRationalNormalization.commonD
  (lower C N delta) (upper C N delta) (selectedReference C N)
def bound (C N delta : PTm n) : Fm PTm n := RationalArgmin.rationalLE
  (weightedNorm nine (otherSum C N delta)) (RationalArithmetic.multiply (fraction four one) (selectedScore C N))

ipra_subst lower
ipra_subst upper
ipra_subst otherSum
ipra_subst selectedScore
ipra_subst denominator
ipra_subst bound

theorem lower_bounds_formula (N k S T ref : PTm n) :
    GaussianGeometricSumBound.entryBounds .source N k S T ref = .all
      (lt (var 0) (PTm.pred (Syn.shift k)) ⟶ RationalArgmin.rationalLE
        (GaussianOffDominantTerms.weightedNorm (Foundations.MasterCertificate.entry (Syn.shift S) (var 0))
          (PTm.monus (Syn.shift k) (succ (var 0)))) (GaussianRationalMetric.qnormSq (Syn.shift ref))) := rfl

theorem upper_bounds_formula (N k S T ref : PTm n) :
    GaussianGeometricSumBound.entryBounds .target N k S T ref = .all
      (lt (var 0) (PTm.monus (Syn.shift N) (Syn.shift k)) ⟶ RationalArgmin.rationalLE
        (GaussianOffDominantTerms.weightedNorm (Foundations.MasterCertificate.entry (Syn.shift T) (var 0))
          (succ (var 0))) (GaussianRationalMetric.qnormSq (Syn.shift ref))) := rfl

theorem lower_bounds (C N delta : PTm n) (hInput : Γ ⊢[PRAAx] input C N)
    (hDelta : Γ ⊢[PRAAx] withinRadius C N delta) : Γ ⊢[PRAAx]
    GaussianGeometricSumBound.entryBounds .source N (winner C N) (lower C N delta) (upper C N delta) (selectedReference C N) := by
  rw [lower_bounds_formula]
  simp only [Syn.shift,subst_lower,GaussianDominantPlateau.subst_winner,GaussianOffDominantTerms.subst_selectedReference]
  refine .allI (.impI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] input (Syn.shift C) (Syn.shift N) := by
    simpa only [Fm.shift,GaussianBalancedRadiusSyntax.subst_input,Syn.shift] using hInput.shift
  have hd : Γ.map Fm.shift ⊢[PRAAx] withinRadius (Syn.shift C) (Syn.shift N) (Syn.shift delta) := by
    simpa only [Fm.shift,GaussianOffDominantTerms.subst_withinRadius,Syn.shift] using hDelta.shift
  exact GaussianOffDominantTerms.lower_norm_bound (Syn.shift C) (Syn.shift N) (Syn.shift delta) (var 0) hs.wk hd.wk Prf.hyp0

theorem upper_bounds (C N delta : PTm n) (hInput : Γ ⊢[PRAAx] input C N)
    (hDelta : Γ ⊢[PRAAx] withinRadius C N delta) : Γ ⊢[PRAAx]
    GaussianGeometricSumBound.entryBounds .target N (winner C N) (lower C N delta) (upper C N delta) (selectedReference C N) := by
  rw [upper_bounds_formula]
  simp only [Syn.shift,subst_upper,GaussianDominantPlateau.subst_winner,GaussianOffDominantTerms.subst_selectedReference]
  refine .allI (.impI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] input (Syn.shift C) (Syn.shift N) := by
    simpa only [Fm.shift,GaussianBalancedRadiusSyntax.subst_input,Syn.shift] using hInput.shift
  have hd : Γ.map Fm.shift ⊢[PRAAx] withinRadius (Syn.shift C) (Syn.shift N) (Syn.shift delta) := by
    simpa only [Fm.shift,GaussianOffDominantTerms.subst_withinRadius,Syn.shift] using hDelta.shift
  exact GaussianOffDominantTerms.upper_norm_bound (Syn.shift C) (Syn.shift N) (Syn.shift delta) (var 0) hs.wk hd.wk Prf.hyp0

/-- The full actual 2/3 norm estimate from the source input and local disk
guard alone. All pointwise and finite-sum premises are discharged. -/
theorem off_dominant_sum (C N delta : PTm n) (hInput : Γ ⊢[PRAAx] input C N)
    (hDelta : Γ ⊢[PRAAx] withinRadius C N delta) : Γ ⊢[PRAAx] bound C N delta := by
  have hk := GaussianDominantPlateau.winner_bounds C N hInput
  have actual := GaussianGeometricSumBound.geometric_sum_bound N (winner C N)
    (lower C N delta) (upper C N delta) (selectedReference C N) (Prf.andE₁ hk) (Prf.andE₂ hk)
    (GaussianOffDominantTerms.lower_length C N delta (winner C N))
    (GaussianOffDominantTerms.upper_length C N delta (winner C N))
    (lower_bounds C N delta hInput hDelta) (upper_bounds C N delta hInput hDelta)
  exact RationalArgmin.rationalLE_congr (.eqRefl _)
    (RationalAlgebra.multiply_congr (.eqRefl _) (GaussianOffDominantTerms.selected_reference_norm C N)) actual

theorem denominator_positive (C N delta : PTm n) : Γ ⊢[PRAAx] le one (denominator C N delta) :=
  GaussianRationalNormalization.commonD_positive _ _ _

/-- Original monic polynomial frontend: the translated input and every
geometric premise are derived, under the original positive-residual branch. -/
theorem original_input_bound (C N z delta : PTm n)
    (hInput : Γ ⊢[PRAAx] GaussianTranslatedBalancedRadius.inputContract C N)
    (hPositive : Γ ⊢[PRAAx] le one (GaussianTranslatedBalancedRadius.residual C z))
    (hDelta : Γ ⊢[PRAAx] withinRadius (GaussianRationalTranslation.translated C N z) N delta) : Γ ⊢[PRAAx]
    bound (GaussianRationalTranslation.translated C N z) N delta :=
  off_dominant_sum _ _ _ (GaussianTranslatedDominantPlateau.positive_input C N z hInput hPositive) hDelta

def output (C N delta : PTm n) : PTm n := pairT (otherSum C N delta)
  (pairT (selectedScore C N) (pairT (selectedReference C N)
    (pairT (lower C N delta) (pairT (upper C N delta) (denominator C N delta)))))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (C N delta : PTm n) : PTm n := ap3 outputF C N delta

ipra_subst output
ipra_subst run

theorem program_at (C N delta : PTm n) : Γ ⊢[PRAAx] run C N delta ≐ output C N delta := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![C,N,delta]

theorem returned_sum (C N delta : PTm n) : Γ ⊢[PRAAx] fstT (run C N delta) ≐ otherSum C N delta :=
  (program_at C N delta).fstE
theorem returned_score (C N delta : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run C N delta)) ≐ selectedScore C N :=
  (program_at C N delta).sndE.fstE
theorem returned_reference (C N delta : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run C N delta))) ≐ selectedReference C N :=
  (program_at C N delta).sndE.sndE.fstE
theorem returned_lower (C N delta : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (run C N delta)))) ≐ lower C N delta :=
  (program_at C N delta).sndE.sndE.sndE.fstE
theorem returned_upper (C N delta : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (sndT (run C N delta))))) ≐ upper C N delta :=
  (program_at C N delta).sndE.sndE.sndE.sndE.fstE
theorem returned_denominator (C N delta : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (sndT (sndT (run C N delta))))) ≐ denominator C N delta :=
  (program_at C N delta).sndE.sndE.sndE.sndE.sndE

theorem returned_denominator_positive (C N delta : PTm n) : Γ ⊢[PRAAx]
    le one (sndT (sndT (sndT (sndT (sndT (run C N delta)))))) :=
  le_congr (.eqRefl _) (returned_denominator C N delta).eqSymm (denominator_positive C N delta)

theorem returned_bound (C N delta : PTm n) (hInput : Γ ⊢[PRAAx] input C N)
    (hDelta : Γ ⊢[PRAAx] withinRadius C N delta) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (weightedNorm nine (fstT (run C N delta)))
      (RationalArithmetic.multiply (fraction four one) (fstT (sndT (run C N delta)))) :=
  RationalArgmin.rationalLE_congr
    (RationalAlgebra.multiply_congr (.eqRefl _) (GaussianRationalProductWitness.qnormSq_congr (returned_sum C N delta))).eqSymm
    (RationalAlgebra.multiply_congr (.eqRefl _) (returned_score C N delta)).eqSymm
    (off_dominant_sum C N delta hInput hDelta)

theorem actual_off_dominant_sum_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (input (var 0) (var 1) ⟶ withinRadius (var 0) (var 1) (var 2) ⟶ bound (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (.impI (off_dominant_sum _ _ _ Prf.hyp1 Prf.hyp0)))

theorem original_off_dominant_sum_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (GaussianTranslatedBalancedRadius.inputContract (var 0) (var 1) ⟶
      le one (GaussianTranslatedBalancedRadius.residual (var 0) (var 2)) ⟶
      withinRadius (GaussianRationalTranslation.translated (var 0) (var 1) (var 2)) (var 1) (var 3) ⟶
      bound (GaussianRationalTranslation.translated (var 0) (var 1) (var 2)) (var 1) (var 3)) :=
  closeUniv 4 (.impI (.impI (.impI (original_input_bound _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

theorem actual_off_dominant_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) ⋏
      ((fstT (run (var 0) (var 1) (var 2)) ≐ otherSum (var 0) (var 1) (var 2)) ⋏
        ((fstT (sndT (run (var 0) (var 1) (var 2))) ≐ selectedScore (var 0) (var 1)) ⋏
          fstT (sndT (sndT (run (var 0) (var 1) (var 2)))) ≐ selectedReference (var 0) (var 1)))) :=
  closeUniv 3 (.andI (program_at _ _ _) (.andI (returned_sum _ _ _) (.andI (returned_score _ _ _) (returned_reference _ _ _))))

theorem returned_off_dominant_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (input (var 0) (var 1) ⟶ withinRadius (var 0) (var 1) (var 2) ⟶
      RationalArgmin.rationalLE (weightedNorm nine (fstT (run (var 0) (var 1) (var 2))))
        (RationalArithmetic.multiply (fraction four one) (fstT (sndT (run (var 0) (var 1) (var 2)))))) :=
  closeUniv 3 (.impI (.impI (returned_bound _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_off_dominant_lists_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((fstT (sndT (sndT (sndT (run (var 0) (var 1) (var 2))))) ≐ lower (var 0) (var 1) (var 2)) ⋏
      ((fstT (sndT (sndT (sndT (sndT (run (var 0) (var 1) (var 2)))))) ≐ upper (var 0) (var 1) (var 2)) ⋏
        ((sndT (sndT (sndT (sndT (sndT (run (var 0) (var 1) (var 2)))))) ≐ denominator (var 0) (var 1) (var 2)) ⋏
          le one (sndT (sndT (sndT (sndT (sndT (run (var 0) (var 1) (var 2)))))))))) :=
  closeUniv 3 (.andI (returned_lower _ _ _) (.andI (returned_upper _ _ _)
    (.andI (returned_denominator _ _ _) (returned_denominator_positive _ _ _))))

end LeanProofs.IPRA.Analysis.GaussianOffDominantSum

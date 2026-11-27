import IPRADerivations.Analysis.Stirling.Binet.StirlingBounds.Logarithms.GaussianBinetDigammaLogBound

/-!
# Uniform smallness of the first-order Stirling expression

The literal C27 digamma minus the canonical logarithm contributes
1/Re(z), and the exact half reciprocal contributes 1/(2 Re(z)).
Pass this sum bound to the normalized name with independent clocks.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBinetStirlingSlopeBound

open_ipra
open ComplexLogarithmRemainder (normSq normSq_one oneCode)
open GaussianCoefficientNameBounds (bounded_radius_mono unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianLogGammaEulerHead (argument)
open GaussianNameArithmetic (addF addData add_fast sum_distance)
open GaussianNameRingLaws (add_sample_error three)
open GaussianNamedInverseRate (diagonal_rate independentRate)
open GaussianNamedLipschitzRate (diagonalEnvelope diagonalNumerator diagonalDenominator)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (positive_product ofGaussian_represents qadd qmul qzero)
open GaussianRationalMetric (bounded bounded_of_cleared distanceBounded qsub)
open GaussianRationalPowerDifference (bounded_sum_same distance_refl_zero)
open GaussianRationalReciprocal (bounded_product reciprocal)
open GaussianReconstructionRoots (distance_zero_iff)
open GaussianRightHalfPlaneLogarithm (source)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "L" => GaussianRightHalfPlaneLogarithm.nameF
local notation "ld" => GaussianRightHalfPlaneLogarithm.data
local notation "P" => GaussianLogGammaEulerDigammaFractionsCofinal.nameF
local notation "pd" => GaussianLogGammaEulerDigammaFractionsCofinal.data
local notation "F" => GaussianNamedDifference.nameF P L

def diffData (A B D neg : PTm n) : PTm n := GaussianNamedDifference.data (pd A B D neg) (ld A B D neg)
def correction (A B D neg : PTm n) : PTm n := qmul (fraction one two) (reciprocal (argument A B D neg))
def nameF : PR 2 := addF F constantF
def data (A B D neg : PTm n) : PTm n := addData (diffData A B D neg) (correction A B D neg)

ipra_subst data [diffData, correction, one, two, GaussianLogGammaEulerRepresentation.subst_argument]

private theorem diff_regular (A B D neg : PTm n) (h : Γ ⊢[PRAAx] source A D neg) :
    Γ ⊢[PRAAx] pointCN F (diffData A B D neg) :=
  GaussianNamedDifference.name_regular P L _ _
    (GaussianLogGammaEulerDigammaFractionsCofinal.regular A B D neg h)
    (GaussianRightHalfPlaneLogarithm.regular A B D neg h)

theorem regular (A B D neg : PTm n) (h : Γ ⊢[PRAAx] source A D neg) :
    Γ ⊢[PRAAx] pointCN nameF (data A B D neg) :=
  add_fast F constantF _ _ (diff_regular A B D neg h) (constant_regular _)

theorem correction_bound (A B D neg : PTm n) (h : Γ ⊢[PRAAx] source A D neg) :
    Γ ⊢[PRAAx] bounded (correction A B D neg) D (two*A) := by
  let z := argument A B D neg
  let half := fraction (one : PTm n) two
  have ht : Γ ⊢[PRAAx] le one two := le_succ_self one
  have halfNorm : Γ ⊢[PRAAx] bounded half one two := by
    let a : PTm n := ComplexLogarithmRemainder.scale one oneCode
    have e : Γ ⊢[PRAAx] normSq a ≐ one := by
      unfold a
      exact (ComplexLogarithmRemainder.normSq_scale one oneCode).eqTrans
        ((congrMul (.eqRefl _) normSq_one).eqTrans (by ipra_ring))
    exact bounded_of_cleared half a two one two ht ht (ofGaussian_represents a two ht)
      (le_congr (congrMul (.eqRefl _) e.eqSymm) (.eqRefl _) (by ipra_le 0))
  have recNorm := GaussianRationalLowerBounds.inverse_bound z A D h.andE₁.andE₁ h.andE₂
    (GaussianBinetReciprocalRows.real_part_lower A B D neg h)
  exact GaussianRationalReciprocal.bound_congr (.eqRefl _) (one_mul D) (.eqRefl _)
    (bounded_product half (reciprocal z) one two D A ht h.andE₁.andE₁ halfNorm recNorm)

private theorem diagonal (p A B D neg : PTm n) (h : Γ ⊢[PRAAx] source A D neg) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data A B D neg)) (ap2 constantF p qzero)
      (diagonalNumerator (num 3*D) (two*A) (num 11) p) (diagonalDenominator (two*A) p) := by
  let u := unit p
  let N := two*A
  let E := N*u
  let x := pd A B D neg
  let y := ld A B D neg
  let z := correction A B D neg
  let a := ap2 P p x
  let b := ap2 L p y
  let d := ap2 F p (diffData A B D neg)
  let r := ap2 nameF p (data A B D neg)
  have hu := unit_positive (Γ := Γ) p
  have hn := positive_product two A (le_succ_self one) h.andE₁.andE₁
  have he := positive_product N u hn hu
  have hAU := positive_product A u h.andE₁.andE₁ hu
  have hd : Γ ⊢[PRAAx] bounded (qsub a b) (two*D*u+num 4*A) E :=
    bounded_radius_mono _ _ _ _ _ hAU he (by dsimp only [E,N]; ipra_le 0)
      (diagonal_rate P L x y D A p h.andE₁.andE₁ (GaussianBinetDigammaLogBound.independent_rate A B D neg h))
  have hz : Γ ⊢[PRAAx] bounded z (D*u) E :=
    bounded_radius_mono _ _ _ _ _ hn he (by dsimp only [E,N]; ipra_le 0) (correction_bound A B D neg h)
  have raw : Γ ⊢[PRAAx] distanceBounded (qadd (qsub a b) z) qzero (two*D*u+num 4*A+D*u) E :=
    (distance_zero_iff _ _ _ he).iffMpr (bounded_sum_same _ _ _ _ _ he hd hz)
  have first : Γ ⊢[PRAAx] distanceBounded r (qadd d z) (three*N) E := by
    have e := add_sample_error F constantF (diffData A B D neg) z p
      (diff_regular A B D neg h) (constant_regular z)
    exact distance_radius_mono _ _ _ _ _ _ hu he (by dsimp only [E]; ipra_le 0)
      (distance_congr (.eqRefl _) (GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _) (constant_at p z))
        (.eqRefl _) (.eqRefl _) e)
  have diff := GaussianNamedDifference.sample_error P L x y p
    (GaussianLogGammaEulerDigammaFractionsCofinal.regular A B D neg h)
    (GaussianRightHalfPlaneLogarithm.regular A B D neg h)
  have second : Γ ⊢[PRAAx] distanceBounded (qadd d z) (qadd (qsub a b) z) (num 6*N+zero) E :=
    sum_distance d (qsub a b) z z _ _ E he
      (distance_radius_mono _ _ _ _ _ _ hu he (by dsimp only [E]; ipra_le 0) diff)
      (distance_refl_zero z E he)
  have chain := distance_triangle_same r (qadd (qsub a b) z) qzero _ _ E he
    (distance_triangle_same r (qadd d z) (qadd (qsub a b) z) _ _ E he first second) raw
  exact distance_congr (.eqRefl _) (constant_at p qzero).eqSymm
    (by dsimp only [diagonalNumerator,N,u,three]; ipra_ring) (.eqRefl _) chain

theorem independent_rate (A B D neg : PTm n) (h : Γ ⊢[PRAAx] source A D neg) :
    Γ ⊢[PRAAx] independentRate nameF constantF (data A B D neg) qzero (num 3*D) (two*A) := by
  apply GaussianNamedLipschitzRate.independent_rate nameF constantF _ qzero _ _ (num 11)
    (positive_product two A (le_succ_self one) h.andE₁.andE₁) (regular A B D neg h) (constant_regular qzero)
  refine .allI ?_
  let s (w : PTm n) := Syn.shift w
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (s A) (s D) (s neg) :=
    by simpa [s,Fm.shift,Syn.shift,source,GaussianRightHalfPlaneArgument.source] using h.shift
  simpa only [diagonalEnvelope,s,Syn.shift,subst_data,PTm.subst_mul,PTm.subst_num,
    GaussianRationalHorner.subst_qzero,two,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    diagonal (var 0) (s A) (s B) (s D) (s neg) hs

theorem actual_complex_Stirling_first_order_expression_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 2) (var 3) ⟶ independentRate nameF constantF
      (data (var 0) (var 1) (var 2) (var 3)) qzero (num 3*var 2) (two*var 0)) :=
  closeUniv 4 (.impI (independent_rate _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBinetStirlingSlopeBound

import IPRADerivations.Analysis.Polynomials.Horner.GaussianRationalHornerPrefixTaylor
import IPRADerivations.Analysis.Gamma.EulerProducts.OriginalPrefixes.GaussianGammaDeflatedPrefixTaylor

/-!
# A scale-sensitive all-order tail for the actual deflated P polynomials

The original full coefficient mass bounds the actual Horner prefix that
drops the zero constant. Every retained coefficient is compared with its
original canonical c_(e+1) name. The full physical shrinking factor is
retained before any passage to the shifted reciprocal name.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaDeflatedFiniteTaylor

open_ipra
open GaussianGammaOriginalC19Prefix (buffer totalDegree stage degree_dominates)
open GaussianGammaOriginalPrefixCoefficientNames (reader original_reader_to_canonical)
open GaussianGammaOriginalPrefixCoefficientVariation (cap)
open GaussianGammaDeflatedPrefixTaylor (prefixValue deflatedTaylor)
open GaussianRationalPowerExpansion (partialSum prefix_succ)
open GaussianOffDominantTerms (term)
open GaussianRationalHorner (horner positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)

open GaussianCoefficientNameBounds (unit unit_positive)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def coefficients (q R d : PTm n) : PTm n := buffer q R (succ d)
def degree (q R d : PTm n) : PTm n := two*(two*R)+
  GaussianGammaCofinalCoefficientName.exponentialCutoff (stage q (succ d)) (two*R)*
    GaussianGammaReciprocalDegreeCells.degree (GaussianGammaCofinalCoefficientName.degreeCutoff (stage q (succ d)) (two*R))
def rowNumerator (q r R d : PTm n) : PTm n := cap R (succ d)*unit r+unit q
def rowDenominator (q r : PTm n) : PTm n := unit q*unit r
def prefixLaw (q r R d w k : PTm n) : Fm PTm n := le k (succ d) ⟶
  distanceBounded (partialSum (coefficients q R d) (degree q R d) w k) (prefixValue r w k)
    (k*rowNumerator q r R d) (rowDenominator q r)
def numerator (q r R d a b : PTm n) : PTm n :=
  GaussianGammaUnitCoefficientMass.budget (two*R)*pw a (succ d)*unit q*unit r+
    pw b (succ d)*(succ d*rowNumerator q r R d)
def denominator (q r d b : PTm n) : PTm n := pw b (succ d)*(unit q*unit r)

ipra_subst coefficients
ipra_subst degree [stage, GaussianGammaCofinalCoefficientName.exponentialCutoff, GaussianGammaCofinalCoefficientName.degreeCutoff, GaussianGammaCofinalCoefficientName.exponentClock, GaussianGammaCofinalCoefficientName.inputClock, GaussianGammaCofinalCoefficientName.outerClock]
ipra_subst rowNumerator
ipra_subst rowDenominator
ipra_subst prefixLaw
ipra_subst numerator
ipra_subst denominator

theorem original_degree (q R d : PTm n) : Γ ⊢[PRAAx] totalDegree q R (succ d) ≐ succ (degree q R d) := by
  unfold totalDegree GaussianGammaFiniteCoefficientPolynomial.totalDegree degree
  ipra_ring

theorem degree_guard (q R d : PTm n) : Γ ⊢[PRAAx] le d (degree q R d) :=
  (succ_monus_succ _ _).eqSymm.eqTrans
    (le_congr (.eqRefl _) (original_degree q R d) (degree_dominates q R (succ d)))

theorem original_length (q R d : PTm n) : Γ ⊢[PRAAx] length (coefficients q R d) ≐ succ (succ (degree q R d)) :=
  (GaussianGammaFiniteCoefficientPolynomial.polynomial_length
    (GaussianGammaCofinalCoefficientName.coefficientPrecision (stage q (succ d)) (two*R)) (two*R)
    (GaussianGammaCofinalCoefficientName.degreeCutoff (stage q (succ d)) (two*R))
    (GaussianGammaCofinalCoefficientName.exponentialCutoff (stage q (succ d)) (two*R))).eqTrans
      (congrSucc (original_degree q R d))

theorem shifted_reader (q R d e : PTm n) (he : Γ ⊢[PRAAx] le e d) : Γ ⊢[PRAAx]
    reader q R (succ d) (succ e) ≐ GaussianBalancedRadiusSyntax.coefficient (coefficients q R d) (degree q R d) e :=
  (GaussianRationalLowCoefficientConvolution.exponent_inside _ _ _
    (le_trans ((succ_monus_succ _ _).eqTrans he) (degree_dominates q R (succ d)))).eqTrans
      (Foundations.SequenceComposition.entry_congr (.eqRefl _)
        ((congrMonus (original_degree q R d) (.eqRefl _)).eqTrans (succ_monus_succ _ _)))

theorem original_term_error (q r R d w e : PTm n) (hR : Γ ⊢[PRAAx] le one R)
    (he : Γ ⊢[PRAAx] le e d) (hw : Γ ⊢[PRAAx] bounded w one one) : Γ ⊢[PRAAx]
    distanceBounded (term (coefficients q R d) (degree q R d) w e) (GaussianGammaDeflatedPrefixTaylor.term r w e)
      (rowNumerator q r R d) (rowDenominator q r) := by
  have raw := GaussianNamedDifferenceQuotient.scale_distance (GaussianRationalReciprocal.power w e)
    (reader q R (succ d) (succ e)) (GaussianGammaHigherCoefficientName.sample r (succ e))
    one (rowNumerator q r R d) (rowDenominator q r)
    (positive_product _ _ (unit_positive q) (unit_positive r)) (GaussianGammaCanonicalPrefixTaylor.unit_power_bound w e hw)
    (original_reader_to_canonical q r R (succ d) (succ e) hR ((succ_monus_succ _ _).eqTrans he))
  exact distance_congr
    ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
      (GaussianRationalSyntheticDivision.qmul_congr (shifted_reader q R d e he) (.eqRefl _)))
    (GaussianRationalPowerAlgebra.qmul_commutative _ _) (one_mul _) (.eqRefl _) raw

theorem prefix_step (q r R d w k : PTm n) (hR : Γ ⊢[PRAAx] le one R)
    (hw : Γ ⊢[PRAAx] bounded w one one) (hk : Γ ⊢[PRAAx] le k d)
    (ih : Γ ⊢[PRAAx] distanceBounded (partialSum (coefficients q R d) (degree q R d) w k)
      (prefixValue r w k) (k*rowNumerator q r R d) (rowDenominator q r)) : Γ ⊢[PRAAx]
    distanceBounded (partialSum (coefficients q R d) (degree q R d) w (succ k)) (prefixValue r w (succ k))
      (succ k*rowNumerator q r R d) (rowDenominator q r) :=
  distance_congr (prefix_succ _ _ _ _ (le_trans hk (degree_guard q R d))).eqSymm
    (GaussianGammaDeflatedPrefixTaylor.prefix_succ r w k).eqSymm (succ_mul _ _).eqSymm (.eqRefl _)
    (GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _ (positive_product _ _ (unit_positive q) (unit_positive r))
      ih (original_term_error q r R d w k hR hk hw))

theorem original_prefix_error (q r R d w : PTm n) (hR : Γ ⊢[PRAAx] le one R)
    (hw : Γ ⊢[PRAAx] bounded w one one) : Γ ⊢[PRAAx]
    distanceBounded (partialSum (coefficients q R d) (degree q R d) w (succ d)) (deflatedTaylor r d w)
      (succ d*rowNumerator q r R d) (rowDenominator q r) := by
  have rs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift R) := by simpa [Fm.shift,Syn.shift] using hR.shift
  have ws : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift w) one one := by simpa [Fm.shift,Syn.shift] using hw.shift
  refine GaussianGammaCanonicalPrefixTaylor.power_prefix_distance GaussianGammaDeflatedPrefixTaylor.body (coefficients q R d) (degree q R d) w (succ d) (GaussianGammaDeflatedPrefixTaylor.data r w)
    (rowNumerator q r R d) (rowDenominator q r) ((succ_monus_succ _ _).eqTrans (degree_guard q R d))
    (positive_product _ _ (unit_positive q) (unit_positive r)) ?_
  let Δ := lt (var 0) (succ (Syn.shift d)) :: Γ.map Fm.shift
  have row := original_term_error (Γ := Δ) (Syn.shift q) (Syn.shift r) (Syn.shift R) (Syn.shift d)
    (Syn.shift w) (var 0) rs.wk ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0) ws.wk
  simpa only [Δ, Syn.shift, ConciseIPRA.PTm.subst_succ, subst_coefficients, subst_degree,
    GaussianGammaDeflatedPrefixTaylor.subst_data, subst_rowNumerator, subst_rowDenominator] using
    distance_congr (.eqRefl _) (GaussianGammaDeflatedPrefixTaylor.body_at (Γ := Δ) _ _ _).eqSymm (.eqRefl _) (.eqRefl _) row

/-- Full original coefficient mass, with no native inverse factor in the tail. -/
theorem original_finite_taylor (q r R d w a b : PTm n) (hR : Γ ⊢[PRAAx] le one R)
    (hb : Γ ⊢[PRAAx] le one b) (hab : Γ ⊢[PRAAx] le a b) (hw : Γ ⊢[PRAAx] bounded w a b) : Γ ⊢[PRAAx]
    distanceBounded (horner (coefficients q R d) w (totalDegree q R (succ d))) (deflatedTaylor r d w)
      (numerator q r R d a b) (denominator q r d b) := by
  have mass := GaussianGammaUnitCoefficientMass.original_coefficient_mass
    (GaussianGammaCofinalCoefficientName.coefficientPrecision (stage q (succ d)) (two*R)) (two*R)
    (GaussianGammaCofinalCoefficientName.degreeCutoff (stage q (succ d)) (two*R))
    (GaussianGammaCofinalCoefficientName.exponentialCutoff (stage q (succ d)) (two*R))
    (GaussianGammaExponentCoefficientPolynomial.original_cutoff_positive R hR)
  have count : Γ ⊢[PRAAx] le (succ (degree q R d)) (length (coefficients q R d)) :=
    le_congr (.eqRefl _) (original_length q R d).eqSymm (le_succ_self _)
  have tail := GaussianRationalHornerPrefixTaylor.original_prefix_tail (coefficients q R d) (degree q R d) d w
    (GaussianGammaUnitCoefficientMass.budget (two*R)) one a b count (degree_guard q R d) (le_refl one) hb hab mass hw
  have actual := distance_congr (congrAp3 GaussianRationalHorner.hornerF (original_degree q R d).eqSymm (.eqRefl _) (.eqRefl _))
    (.eqRefl _) (.eqRefl _) (.eqRefl _) tail
  have lastBound := original_prefix_error q r R d w hR (GaussianShrinkingPolynomialTail.shrinking_disk_unit w a b hb hab hw)
  have hd := positive_product (Γ := Γ) _ _ (unit_positive q) (unit_positive r)
  have hp := GaussianFactorBudget.power_positive b (succ d) hb
  have joined := GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _
    (positive_product _ _ (le_refl one) hp) hd actual lastBound
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold numerator; ipra_ring)
    (congrMul (one_mul _) (.eqRefl _)) joined

theorem actual_original_deflated_polynomial_shrinking_taylor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((le one (var 2) ⋏ (le one (var 6) ⋏ (le (var 5) (var 6) ⋏ bounded (var 4) (var 5) (var 6)))) ⟶
      distanceBounded (horner (coefficients (var 0) (var 2) (var 3)) (var 4) (totalDegree (var 0) (var 2) (succ (var 3))))
        (deflatedTaylor (var 1) (var 3) (var 4))
        (numerator (var 0) (var 1) (var 2) (var 3) (var 5) (var 6)) (denominator (var 0) (var 1) (var 3) (var 6))) :=
  closeUniv 7 (.impI (original_finite_taylor _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaDeflatedFiniteTaylor

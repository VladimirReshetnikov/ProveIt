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

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaOriginalC19Prefix (buffer totalDegree stage degree_dominates)
open GaussianGammaOriginalPrefixCoefficientNames (reader original_reader_to_canonical)
open GaussianGammaOriginalPrefixCoefficientVariation (cap)
open GaussianGammaDeflatedPrefixTaylor (prefixValue deflatedTaylor)
open GaussianRationalPowerExpansion (partialSum prefix_zero prefix_succ)
open GaussianOffDominantTerms (term)
open GaussianRationalHorner (horner qzero positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

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

@[simp] theorem subst_coefficients {m : ℕ} (σ : Fin n → PTm m) (q R d : PTm n) :
    Syn.subst σ (coefficients q R d) = coefficients (Syn.subst σ q) (Syn.subst σ R) (Syn.subst σ d) := by simp [coefficients]
@[simp] theorem subst_degree {m : ℕ} (σ : Fin n → PTm m) (q R d : PTm n) :
    Syn.subst σ (degree q R d) = degree (Syn.subst σ q) (Syn.subst σ R) (Syn.subst σ d) := by
  simp [degree,stage,GaussianGammaCofinalCoefficientName.exponentialCutoff,GaussianGammaCofinalCoefficientName.degreeCutoff,
    GaussianGammaCofinalCoefficientName.exponentClock,GaussianGammaCofinalCoefficientName.inputClock,GaussianGammaCofinalCoefficientName.outerClock]
@[simp] theorem subst_rowNumerator {m : ℕ} (σ : Fin n → PTm m) (q r R d : PTm n) :
    Syn.subst σ (rowNumerator q r R d) = rowNumerator (Syn.subst σ q) (Syn.subst σ r) (Syn.subst σ R) (Syn.subst σ d) := by simp [rowNumerator]
@[simp] theorem subst_rowDenominator {m : ℕ} (σ : Fin n → PTm m) (q r : PTm n) :
    Syn.subst σ (rowDenominator q r) = rowDenominator (Syn.subst σ q) (Syn.subst σ r) := by simp [rowDenominator]
@[simp] theorem subst_prefixLaw {m : ℕ} (σ : Fin n → PTm m) (q r R d w k : PTm n) :
    (prefixLaw q r R d w k).subst σ = prefixLaw (Syn.subst σ q) (Syn.subst σ r) (Syn.subst σ R)
      (Syn.subst σ d) (Syn.subst σ w) (Syn.subst σ k) := by simp [prefixLaw]
@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (q r R d a b : PTm n) :
    Syn.subst σ (numerator q r R d a b) = numerator (Syn.subst σ q) (Syn.subst σ r) (Syn.subst σ R)
      (Syn.subst σ d) (Syn.subst σ a) (Syn.subst σ b) := by simp [numerator]
@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (q r d b : PTm n) :
    Syn.subst σ (denominator q r d b) = denominator (Syn.subst σ q) (Syn.subst σ r) (Syn.subst σ d) (Syn.subst σ b) := by simp [denominator]

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
  have all : Γ ⊢[PRAAx] .all (prefixLaw (Syn.shift q) (Syn.shift r) (Syn.shift R) (Syn.shift d) (Syn.shift w) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,le_QF _ _⟩ ?_ ?_
    · simp only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI (distance_congr (prefix_zero _ _ _).eqSymm (GaussianGammaDeflatedPrefixTaylor.prefix_zero r w).eqSymm
        (zero_mul _).eqSymm (.eqRefl _) (GaussianRationalPowerDifference.distance_refl_zero qzero _
          (positive_product _ _ (unit_positive q) (unit_positive r))))
    · simp only [subst_prefixLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      exact prefix_step _ _ _ _ _ _ rs.wk.wk ws.wk.wk ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0)
        (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0))
  have done : Γ ⊢[PRAAx] prefixLaw q r R d w (succ d) := by
    simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE (succ d)
  exact .impE done (le_refl _)

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
  have hD := positive_product _ _ hp hd
  have first := distance_radius_mono _ _ _ _
    (GaussianGammaUnitCoefficientMass.budget (two*R)*pw a (succ d)*unit q*unit r) (denominator q r d b)
    (positive_product _ _ (le_refl one) hp) hD (le_of_eq_add (d := zero) (by unfold denominator; ipra_ring)) actual
  have last := distance_radius_mono _ _ _ _ (pw b (succ d)*(succ d*rowNumerator q r R d)) (denominator q r d b)
    hd hD (le_of_eq_add (d := zero) (by dsimp only [denominator,rowDenominator]; ipra_ring)) lastBound
  exact distance_triangle_same _ _ _ _ _ _ hD first last

theorem actual_original_deflated_polynomial_shrinking_taylor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((le one (var 2) ⋏ (le one (var 6) ⋏ (le (var 5) (var 6) ⋏ bounded (var 4) (var 5) (var 6)))) ⟶
      distanceBounded (horner (coefficients (var 0) (var 2) (var 3)) (var 4) (totalDegree (var 0) (var 2) (succ (var 3))))
        (deflatedTaylor (var 1) (var 3) (var 4))
        (numerator (var 0) (var 1) (var 2) (var 3) (var 5) (var 6)) (denominator (var 0) (var 1) (var 3) (var 6))) :=
  closeUniv 7 (.impI (original_finite_taylor _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaDeflatedFiniteTaylor

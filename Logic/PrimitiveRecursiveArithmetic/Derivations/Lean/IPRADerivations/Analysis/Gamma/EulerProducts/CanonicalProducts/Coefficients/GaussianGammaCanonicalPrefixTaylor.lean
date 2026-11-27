import IPRADerivations.Analysis.Gamma.EulerProducts.OriginalPrefixes.GaussianGammaOriginalPrefixCoefficientNames
import IPRADerivations.Analysis.Gamma.Taylor.DegreeTails.GaussianGammaUnitCoefficientMass
import IPRADerivations.Analysis.Polynomials.Taylor.GaussianShrinkingPolynomialTail
import IPRADerivations.Analysis.Integration.RiemannSums.GaussianRationalRiemannRefinement
import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.GaussianNamedDifferenceQuotient

/-!
# Original finite Gamma polynomials versus canonical coefficient prefixes

Every term uses the original independently requested coefficient name and
the actual rational power of the physical input. The finite canonicalPrefix is
compared by a guarded quantifier-free induction, and the original full
coefficient mass retains the complete shrinking factor |w|^(d+1).
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaCanonicalPrefixTaylor

open_ipra
open GaussianGammaOriginalC19Prefix (buffer totalDegree degree_dominates)
open GaussianGammaOriginalPrefixCoefficientNames (reader original_reader_to_canonical)
open GaussianGammaOriginalPrefixCoefficientVariation (cap)
open GaussianGammaHigherCoefficientName (sample)
open GaussianRationalPowerExpansion (partialSum prefix_succ termBody term_body_at)
open GaussianOffDominantTerms (term)
open GaussianRationalFiniteSum (sum)
open GaussianRationalReciprocal (power bounded_power bound_congr)
open GaussianRationalHorner (qmul positive_product evaluate)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalRiemannRefinement (termsDistance sum_distance)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def canonicalTerm (r w e : PTm n) : PTm n := qmul (sample r e) (power w e)
def data (r w : PTm n) : PTm n := pairT r w
def body : PTm 2 := canonicalTerm (fstT (var 1)) (sndT (var 1)) (var 0)
def canonicalPrefix (r w k : PTm n) : PTm n := GaussianRationalFiniteSum.sum body k (data r w)
def taylor (r d w : PTm n) : PTm n := canonicalPrefix r w (succ d)
def rowNumerator (q r R d : PTm n) : PTm n := cap R d*unit r+unit q
def rowDenominator (q r : PTm n) : PTm n := unit q*unit r
def prefixLaw (q r R d w k : PTm n) : Fm PTm n := le k (succ d) ⟶
  distanceBounded (partialSum (buffer q R d) (totalDegree q R d) w k) (canonicalPrefix r w k)
    (k*rowNumerator q r R d) (rowDenominator q r)
def numerator (q r R d a b : PTm n) : PTm n :=
  GaussianGammaUnitCoefficientMass.budget (two*R)*pw a (succ d)*unit q*unit r+
    pw b (succ d)*(succ d*rowNumerator q r R d)
def denominator (q r d b : PTm n) : PTm n := pw b (succ d)*(unit q*unit r)

ipra_subst canonicalTerm
ipra_subst data
@[simp] theorem subst_prefix {m : ℕ} (σ : Fin n → PTm m) (r w k : PTm n) :
    Syn.subst σ (canonicalPrefix r w k) = canonicalPrefix (Syn.subst σ r) (Syn.subst σ w) (Syn.subst σ k) := by simp [canonicalPrefix]
ipra_subst taylor
ipra_subst rowNumerator
ipra_subst rowDenominator
ipra_subst buffer [GaussianGammaOriginalC19Prefix.stage, GaussianGammaCofinalCoefficientName.coefficientPrecision, GaussianGammaCofinalCoefficientName.degreeCutoff, GaussianGammaCofinalCoefficientName.exponentialCutoff, GaussianGammaCofinalCoefficientName.exponentClock, GaussianGammaCofinalCoefficientName.inputClock, GaussianGammaCofinalCoefficientName.outerClock]
ipra_subst totalDegree [GaussianGammaOriginalC19Prefix.stage, GaussianGammaCofinalCoefficientName.degreeCutoff, GaussianGammaCofinalCoefficientName.exponentialCutoff, GaussianGammaCofinalCoefficientName.exponentClock, GaussianGammaCofinalCoefficientName.inputClock, GaussianGammaCofinalCoefficientName.outerClock]
ipra_subst prefixLaw
ipra_subst numerator
ipra_subst denominator

theorem body_at (r w e : PTm n) : Γ ⊢[PRAAx] inst2 body e (data r w) ≐ canonicalTerm r w e := by
  simp only [body,inst2,subst_canonicalTerm,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact GaussianRationalSyntheticDivision.qmul_congr
    (congrAp2 GaussianGammaHigherCoefficientName.nameF (fst_pair r w) (.eqRefl _))
    (congrAp2 GaussianRationalReciprocal.powerF (.eqRefl _) (snd_pair r w))

theorem unit_power_bound (w e : PTm n) (hw : Γ ⊢[PRAAx] bounded w one one) : Γ ⊢[PRAAx]
    bounded (power w e) one one :=
  bound_congr (.eqRefl _) (GaussianPolynomialPerturbation.one_power e)
    (GaussianPolynomialPerturbation.one_power e) (bounded_power w one one e (le_refl one) hw)

/-- The original coefficient reader supplies each actual weighted row. -/
theorem original_term_error (q r R d w e : PTm n) (hR : Γ ⊢[PRAAx] le one R)
    (he : Γ ⊢[PRAAx] le e d) (hw : Γ ⊢[PRAAx] bounded w one one) : Γ ⊢[PRAAx]
    distanceBounded (term (buffer q R d) (totalDegree q R d) w e) (canonicalTerm r w e)
      (rowNumerator q r R d) (rowDenominator q r) := by
  have degree := le_trans he (degree_dominates q R d)
  have coefficient := GaussianRationalLowCoefficientConvolution.exponent_inside (buffer q R d) (totalDegree q R d) e degree
  have raw := GaussianNamedDifferenceQuotient.scale_distance (power w e) (reader q R d e) (sample r e)
    one (rowNumerator q r R d) (rowDenominator q r)
    (positive_product _ _ (unit_positive q) (unit_positive r)) (unit_power_bound w e hw)
    (original_reader_to_canonical q r R d e hR he)
  exact distance_congr
    ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
      (GaussianRationalSyntheticDivision.qmul_congr coefficient (.eqRefl _)))
    (GaussianRationalPowerAlgebra.qmul_commutative _ _) (one_mul _) (.eqRefl _) raw

theorem prefix_step (q r R d w k : PTm n) (hR : Γ ⊢[PRAAx] le one R)
    (hw : Γ ⊢[PRAAx] bounded w one one) (hk : Γ ⊢[PRAAx] le k d)
    (ih : Γ ⊢[PRAAx] distanceBounded (partialSum (buffer q R d) (totalDegree q R d) w k)
      (canonicalPrefix r w k) (k*rowNumerator q r R d) (rowDenominator q r)) : Γ ⊢[PRAAx]
    distanceBounded (partialSum (buffer q R d) (totalDegree q R d) w (succ k)) (canonicalPrefix r w (succ k))
      (succ k*rowNumerator q r R d) (rowDenominator q r) := by
  have combined := GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _
    (positive_product _ _ (unit_positive q) (unit_positive r)) ih (original_term_error q r R d w k hR hk hw)
  exact distance_congr (prefix_succ _ _ _ _ (le_trans hk (degree_dominates q R d))).eqSymm
    ((GaussianRationalFiniteSum.sum_succ body k (data r w)).eqTrans (GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _) (body_at r w k))).eqSymm
    (succ_mul _ _).eqSymm (.eqRefl _) combined

/-- A uniform row error bounds the distance from a stored power prefix to a finite sum. -/
theorem power_prefix_distance (g : PTm 2) (C N w k y A D : PTm n)
    (hk : Γ ⊢[PRAAx] le k (succ N)) (hD : Γ ⊢[PRAAx] le one D)
    (h : (lt (var 0) (Syn.shift k) :: Γ.map Fm.shift) ⊢[PRAAx]
      distanceBounded (term (Syn.shift C) (Syn.shift N) (Syn.shift w) (var 0))
        (inst2 g (var 0) (Syn.shift y)) (Syn.shift A) (Syn.shift D)) :
    Γ ⊢[PRAAx] distanceBounded (partialSum C N w k) (sum g k y) (k*A) D := by
  have rows : Γ ⊢[PRAAx] termsDistance termBody g k (GaussianRationalPowerExpansion.data C N w) y A D := by
    refine .allI (.impI ?_)
    simpa only [Syn.shift, GaussianRationalPowerExpansion.subst_data] using
      distance_congr (term_body_at _ _ _ _).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) h
  exact distance_congr (GaussianRationalFiniteSum.generated_prefix_congr termBody k (succ N)
    (GaussianRationalPowerExpansion.data C N w) k (le_refl _) hk) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (sum_distance termBody g k _ y A D hD rows)

/-- Uniform row errors bound the actual stored prefix. -/
theorem original_prefix_error (q r R d w : PTm n) (hR : Γ ⊢[PRAAx] le one R)
    (hw : Γ ⊢[PRAAx] bounded w one one) : Γ ⊢[PRAAx]
    distanceBounded (partialSum (buffer q R d) (totalDegree q R d) w (succ d)) (taylor r d w)
      (succ d*rowNumerator q r R d) (rowDenominator q r) := by
  have rs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift R) := by simpa [Fm.shift,Syn.shift] using hR.shift
  have ws : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift w) one one := by simpa [Fm.shift,Syn.shift] using hw.shift
  refine power_prefix_distance body (buffer q R d) (totalDegree q R d) w (succ d) (data r w)
    (rowNumerator q r R d) (rowDenominator q r) ((succ_monus_succ _ _).eqTrans (degree_dominates q R d))
    (positive_product _ _ (unit_positive q) (unit_positive r)) ?_
  let Δ := lt (var 0) (succ (Syn.shift d)) :: Γ.map Fm.shift
  have row := original_term_error (Γ := Δ) (Syn.shift q) (Syn.shift r) (Syn.shift R) (Syn.shift d)
    (Syn.shift w) (var 0) rs.wk ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0) ws.wk
  simpa only [Δ, Syn.shift, ConciseIPRA.PTm.subst_succ, subst_buffer, subst_totalDegree,
    subst_data, subst_rowNumerator, subst_rowDenominator] using
    distance_congr (.eqRefl _) (body_at (Γ := Δ) _ _ _).eqSymm (.eqRefl _) (.eqRefl _) row

/-- The entire physical shrinking factor survives all coefficient transport. -/
theorem original_finite_taylor (q r R d w a b : PTm n) (hR : Γ ⊢[PRAAx] le one R)
    (hb : Γ ⊢[PRAAx] le one b) (hab : Γ ⊢[PRAAx] le a b) (hw : Γ ⊢[PRAAx] bounded w a b) : Γ ⊢[PRAAx]
    distanceBounded (evaluate (buffer q R d) w) (taylor r d w)
      (numerator q r R d a b) (denominator q r d b) := by
  have mass := GaussianGammaUnitCoefficientMass.original_coefficient_mass
    (GaussianGammaCofinalCoefficientName.coefficientPrecision (GaussianGammaOriginalC19Prefix.stage q d) (two*R)) (two*R)
    (GaussianGammaCofinalCoefficientName.degreeCutoff (GaussianGammaOriginalC19Prefix.stage q d) (two*R))
    (GaussianGammaCofinalCoefficientName.exponentialCutoff (GaussianGammaOriginalC19Prefix.stage q d) (two*R))
    (GaussianGammaExponentCoefficientPolynomial.original_cutoff_positive R hR)
  have tail := GaussianShrinkingPolynomialTail.finite_coefficient_tail (buffer q R d) (totalDegree q R d) d w
    (GaussianGammaUnitCoefficientMass.budget (two*R)) one a b
    (GaussianGammaFiniteCoefficientPolynomial.polynomial_length _ _ _ _) (degree_dominates q R d)
    (le_refl one) hb hab mass hw
  have prefixError := original_prefix_error q r R d w hR (GaussianShrinkingPolynomialTail.shrinking_disk_unit w a b hb hab hw)
  have hd := positive_product (Γ := Γ) _ _ (unit_positive q) (unit_positive r)
  have hp := GaussianFactorBudget.power_positive b (succ d) hb
  have joined := GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _
    (positive_product _ _ (le_refl one) hp) hd tail prefixError
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold numerator; ipra_ring)
    (congrMul (one_mul _) (.eqRefl _)) joined

def taylorF : PR 3 := PTm.toPR (taylor (var 0) (var 1) (var 2))
theorem original_taylor_program (r d w : PTm n) : Γ ⊢[PRAAx]
    ap3 taylorF r d w ≐ taylor r d w := by
  simpa only [taylorF,ap3,subst_taylor,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons] using
    toPR_eq (Γ := Γ) (taylor (var 0) (var 1) (var 2) : PTm 3) ![r,d,w]

theorem actual_original_canonical_coefficient_prefix_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((le one (var 2) ⋏ bounded (var 4) one one) ⟶
      distanceBounded (partialSum (buffer (var 0) (var 2) (var 3)) (totalDegree (var 0) (var 2) (var 3)) (var 4) (succ (var 3)))
        (taylor (var 1) (var 3) (var 4)) (succ (var 3)*rowNumerator (var 0) (var 1) (var 2) (var 3)) (rowDenominator (var 0) (var 1))) :=
  closeUniv 5 (.impI (original_prefix_error _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_original_all_order_shrinking_finite_taylor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((le one (var 2) ⋏ (le one (var 6) ⋏ (le (var 5) (var 6) ⋏ bounded (var 4) (var 5) (var 6)))) ⟶
      distanceBounded (evaluate (buffer (var 0) (var 2) (var 3)) (var 4)) (taylor (var 1) (var 3) (var 4))
        (numerator (var 0) (var 1) (var 2) (var 3) (var 5) (var 6)) (denominator (var 0) (var 1) (var 3) (var 6))) :=
  closeUniv 7 (.impI (original_finite_taylor _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

theorem actual_original_all_order_canonical_taylor_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap3 taylorF (var 0) (var 1) (var 2) ≐ taylor (var 0) (var 1) (var 2)) :=
  closeUniv 3 (original_taylor_program _ _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaCanonicalPrefixTaylor

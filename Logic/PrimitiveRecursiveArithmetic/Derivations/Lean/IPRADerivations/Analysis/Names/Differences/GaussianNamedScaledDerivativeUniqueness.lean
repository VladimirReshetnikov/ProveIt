import IPRADerivations.Analysis.Trigonometry.Arctangent.GaussianArctangentExponentialPeriod
import IPRADerivations.Analysis.Names.Rates.GaussianBoundedConstantProductRate
import IPRADerivations.Analysis.Gamma.FunctionalEquations.ReciprocalGamma.GaussianGammaAdjacentCutoff
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateRadius
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateTransport
import IPRADerivations.Analysis.Trigonometry.Hyperbolic.GaussianSineProductImaginaryLogDerivativeTail

/-!
# Uniqueness of a derivative from dyadically scaled names

The two first-order terms may be compared before division by the step.
When their actual named distance has a uniform quadratic bound on
steps `1 / (D * 2^s)`, the derivative names are cross-equivalent.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianNamedScaledDerivativeUniqueness

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open ComplexLogarithmRemainder (mul scale oneCode eval_re_code eval_im_code)
open GaussianBoundedConstantProductName (constantF constant_at constant_regular)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans)
open GaussianNameRingLaws (oneF one_at one_fast)
open GaussianNamedInverseRate (independentRate rate_at rateNumerator rateDenominator)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (qmul ofGaussian_represents ofGaussian_canonical qmul_represents
  qmul_canonical positive_product canonical_unique represents_congr)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalSyntheticDivision (qone)
open GaussianRootAlgebra (equal equal_of_values re_mul im_mul re_scale im_scale re_one im_one)
open GaussianSineProductImaginaryLogDerivative (rationalReal realNumerator)
open GaussianSineProductImaginaryLogDerivativeTail (rational_real_bound)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def step (D s : PTm n) : PTm n := rationalReal one (D*unit s)
def inverseStep (D s : PTm n) : PTm n := rationalReal (D*unit s) one
def weightedF (F : PR 2) : PR 2 := multiplyF constantF F
def weightedData (F : PR 2) (x D s : PTm n) : PTm n := multiplyData constantF F (step D s) x

ipra_subst step [one]

ipra_subst weightedData

theorem inverse_product (D s : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] qmul (inverseStep D s) (step D s) ≐ qone := by
  let E := D*unit s
  have hE : Γ ⊢[PRAAx] le one E := positive_product _ _ hD (unit_positive s)
  have raw := qmul_represents _ _ _ _ _ _ (le_refl one) hE
    (ofGaussian_represents (Γ := Γ) (realNumerator E) one (le_refl one))
    (ofGaussian_represents (realNumerator one) E hE)
  have e : Γ ⊢[PRAAx] equal (mul (realNumerator E) (realNumerator one)) (scale E oneCode) := by
    apply equal_of_values <;>
      simp only [realNumerator, re_mul, im_mul, eval_re_code, eval_im_code, ZT.toZ_ofNat,
        re_scale, im_scale, re_one, im_one] <;>
      ipra_simps <;> ring
  exact canonical_unique _ _ _ E (qmul_canonical _ _) (ofGaussian_canonical _ _ (le_refl one)) hE
    (represents_congr (.eqRefl _) e (one_mul E) raw) (GaussianRationalReciprocal.qone_represents_scaled E)

theorem inverse_bound (D s : PTm n) : Γ ⊢[PRAAx] bounded (inverseStep D s) (D*unit s) one :=
  rational_real_bound _ _ _ _ (le_refl one) (le_refl one)
    (le_of_eq_add (d := zero) (by ipra_ring))

private theorem constant_one (c x : PTm n) (h : Γ ⊢[PRAAx] c ≐ qone) :
    Γ ⊢[PRAAx] crossEquivalent constantF oneF c x := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _ (constant_regular c) (one_fast x)
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] Syn.shift c ≐ qone := by simpa [Fm.shift, Syn.shift] using h.shift
  exact (constant_at (var 0) (Syn.shift c)).eqTrans (hs.eqTrans (one_at (var 0) (Syn.shift x)).eqSymm)

theorem inverse_weight (F : PR 2) (x D s : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hF : Γ ⊢[PRAAx] pointCN F x) : Γ ⊢[PRAAx]
    crossEquivalent (GaussianBoundedConstantProductName.nameF (weightedF F)) F
      (GaussianBoundedConstantProductName.data (D*unit s) (inverseStep D s) (weightedData F x D s)) x := by
  let a := inverseStep D s
  let b := step D s
  have ha := constant_regular (Γ := Γ) a
  have hb := constant_regular (Γ := Γ) b
  have hw := multiply_fast constantF F b x hb hF
  have scaled := GaussianBoundedConstantProductName.ordinary_product_identity
    (weightedF F) (D*unit s) a (weightedData F x D s) (.andI hw (inverse_bound D s))
  have assoc := GaussianNameRingLaws.multiply_associative constantF constantF F a b x ha hb hF
  have c₁ := GaussianArctangentExponentialPeriod.constant_product (Γ := Γ) a b
  have c₂ := constant_one (qmul a b) x (inverse_product D s hD)
  have c := cross_trans (multiplyF constantF constantF) constantF oneF
    (multiplyData constantF constantF a b) (qmul a b) x c₁ c₂
  have lift := GaussianGammaAdjacentCutoff.multiply_cross (multiplyF constantF constantF) oneF F F
    (multiplyData constantF constantF a b) x x x (multiply_fast _ _ _ _ ha hb) (one_fast x) hF hF c
    (GaussianNameEquivalence.cross_refl F x hF)
  exact cross_trans _ _ _ _ _ _ scaled (cross_trans _ _ _ _ _ _
    (cross_symm _ _ _ _ assoc) (cross_trans _ _ _ _ _ _ lift (GaussianNameRingLaws.multiply_one_left F x hF)))

theorem amplify (F G : PR 2) (x y D C s : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hF : Γ ⊢[PRAAx] pointCN F x) (hG : Γ ⊢[PRAAx] pointCN G y)
    (h : Γ ⊢[PRAAx] independentRate (weightedF F) (weightedF G)
      (weightedData F x D s) (weightedData G y D s) C ((D*unit s)*(D*unit s))) :
    Γ ⊢[PRAAx] independentRate F G x y C (unit s) := by
  let E := D*unit s
  have hE : Γ ⊢[PRAAx] le one E := positive_product _ _ hD (unit_positive s)
  have hE₂ := positive_product _ _ hE hE
  have hm := GaussianBoundedConstantProductRate.original_rate (weightedF F) (weightedF G) E (inverseStep D s)
    (weightedData F x D s) (weightedData G y D s) C (E*E) hE₂ (inverse_bound D s) h
  have transported := GaussianNamedRateTransport.transport _ _ F G _ _ x y (E*C) (E*E) hE₂ hm
    (cross_symm _ _ _ _ (inverse_weight F x D s hD hF))
    (cross_symm _ _ _ _ (inverse_weight G y D s hD hG))
  apply GaussianNamedRateRadius.weaken F G x y (E*C) (E*E) C (unit s) hE₂ (unit_positive s) _ transported
  dsimp only [E]
  ipra_le (𝔞 D)*(𝔞 C)*(𝔞 (unit s))^2*sl hD

def family (F G : PR 2) (x y D C : PTm n) : Fm PTm n := .all
  (independentRate (weightedF F) (weightedF G)
    (weightedData F (Syn.shift x) (Syn.shift D) (var 0)) (weightedData G (Syn.shift y) (Syn.shift D) (var 0))
    (Syn.shift C) ((Syn.shift D*unit (var 0))*(Syn.shift D*unit (var 0))))

@[simp] theorem subst_family {m : ℕ} (σ : Fin n → PTm m) (F G : PR 2) (x y D C : PTm n) :
    (family F G x y D C).subst σ = family F G (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ D) (Syn.subst σ C) := by
  simp only [family, Fm.subst_all, GaussianNamedInverseRate.subst_independentRate, subst_weightedData,
    PTm.subst_mul, GaussianCoefficientNameBounds.subst_unit, Syn.subst_var, Syn.up_zero, Syn.up_succ, Syn.subst_shift,
    Syn.shift_subst]

theorem family_at (F G : PR 2) (x y D C s : PTm n) (h : Γ ⊢[PRAAx] family F G x y D C) : Γ ⊢[PRAAx]
    independentRate (weightedF F) (weightedF G) (weightedData F x D s) (weightedData G y D s)
      C ((D*unit s)*(D*unit s)) := by
  simpa only [family, GaussianNamedInverseRate.subst_independentRate, subst_weightedData, PTm.subst_mul,
    GaussianCoefficientNameBounds.subst_unit, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using h.allE s

theorem observation (F G : PR 2) (x y D C p q : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hF : Γ ⊢[PRAAx] pointCN F x) (hG : Γ ⊢[PRAAx] pointCN G y) (h : Γ ⊢[PRAAx] family F G x y D C) :
    Γ ⊢[PRAAx] distanceBounded (ap2 F p x) (ap2 G q y) (unit p+unit q) (unit p*unit q) := by
  let z := qsub (ap2 F p x) (ap2 G q y)
  let A := unit p+unit q
  let B := unit p*unit q
  let s := GaussianRationalSlackRemoval.precision z A B C
  apply GaussianRationalSlackRemoval.slack_removal_at z A B C
    (positive_product _ _ (unit_positive p) (unit_positive q))
  have rate := amplify F G x y D C s hD hF hG (family_at F G x y D C s h)
  change Γ ⊢[PRAAx] distanceBounded (ap2 F p x) (ap2 G q y) (A*unit s+C*B) (B*unit s)
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by dsimp only [rateNumerator,A,B]; ipra_ring) (by dsimp only [rateDenominator,B]; ipra_ring)
    (rate_at F G x y C (unit s) p q rate)

theorem unique (F G : PR 2) (x y D C : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hF : Γ ⊢[PRAAx] pointCN F x) (hG : Γ ⊢[PRAAx] pointCN G y) (h : Γ ⊢[PRAAx] family F G x y D C) :
    Γ ⊢[PRAAx] crossEquivalent F G x y := by
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  have hd : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (sh D) := by simpa [Fm.shift,Syn.shift,sh,one] using hD.shift.shift
  have hf : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] pointCN F (sh x) := by simpa [Fm.shift,Syn.shift,sh] using hF.shift.shift
  have hg : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] pointCN G (sh y) := by simpa [Fm.shift,Syn.shift,sh] using hG.shift.shift
  have hr : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] family F G (sh x) (sh y) (sh D) (sh C) := by
    simpa [Fm.shift,Syn.shift,sh] using h.shift.shift
  exact .allI (.allI (observation F G (sh x) (sh y) (sh D) (sh C) (var 1) (var 0) hd hf hg hr))

theorem actual_dyadic_scaled_derivative_uniqueness_closed (F G : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      ((le one (var 2) ⋏ (pointCN F (var 0) ⋏ (pointCN G (var 1) ⋏ family F G (var 0) (var 1) (var 2) (var 3)))) ⟶
        crossEquivalent F G (var 0) (var 1)) :=
  closeUniv 4 (.impI (unique F G _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianNamedScaledDerivativeUniqueness

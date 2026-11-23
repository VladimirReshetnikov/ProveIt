import IPRADerivations.Analysis.GaussianEulerBetaPoleGuard
import IPRADerivations.Analysis.GaussianGammaRepeatedShift

/-!
# The original finite Euler head as the Beta endpoint candidate

A true numerical QF induction binds N! times the ORIGINAL Euler head to
its literal rising linear-factor product. The original reciprocal head
therefore satisfies the cleared N!/rising-product formula and the exact
integration-by-parts recurrence z*Beta_(N+1)(z)=(N+1)*Beta_N(z+1).
Every reciprocal identity follows from the original positive-real margin.

This is exact finite product algebra. Identification with the stored
Beta polynomial primitive at one, finite integration, and analytic
endpoint errors remain separate; no integral value is assumed here.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerBetaProductValue

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qmul ofGaussian represents canonical positive_product)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRationalNaturalScale (natScale naturalPoint natScale_congr natScale_as_product natScale_product natScale_multiply)
open GaussianRationalReciprocal (qone reciprocal)
open GaussianRationalPowerAlgebra (qmul_commutative qmul_shuffle)
open GaussianReciprocalHorner (qmul_associative qmul_one_right)
open GaussianGammaEulerHead (head factor head_zero head_succ)
open GaussianGammaEulerHeadShift (linear shifted)
open GaussianGammaRepeatedShift (risingProduct prefix_zero prefix_succ prefix_canonical)
open GaussianEulerBetaPoleGuard (source)
open Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def value (z B N : PTm n) : PTm n := reciprocal (head z B N)
def factorialLaw (z B N : PTm n) : Fm PTm n := natScale (fact N) (head z B N) ≐ risingProduct z B (succ N)
@[simp] theorem subst_value {m : ℕ} (σ : Fin n → PTm m) (z B N : PTm n) :
    Syn.subst σ (value z B N) = value (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) := by simp [value]
@[simp] theorem subst_factorialLaw {m : ℕ} (σ : Fin n → PTm m) (z B N : PTm n) :
    (factorialLaw z B N).subst σ = factorialLaw (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) := by simp [factorialLaw,fact]

theorem scaled_left_product (t a b : PTm n) : Γ ⊢[PRAAx] natScale t (qmul a b) ≐ qmul (natScale t a) b :=
  (natScale_congr (.eqRefl _) (qmul_commutative a b)).eqTrans
    ((natScale_product t b a).eqSymm.eqTrans (qmul_commutative _ _))

theorem factor_clearing (z B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    natScale (succ N) (factor N z B) ≐ linear z B (succ N) := by
  let a := GaussianGammaEulerHeadLower.translated z B (succ N)
  let D := B*succ N
  have hD := positive_product (Γ := Γ) _ _ hB (zero_lt_succ N)
  exact GaussianRationalHorner.canonical_unique _ _ (ComplexLogarithmRemainder.scale (succ N) a) D
    (GaussianRationalNaturalScale.natScale_canonical _ _) (GaussianRationalHorner.ofGaussian_canonical _ _ hB) hD
    (GaussianRationalNaturalScale.natScale_represents _ _ _ _ hD (GaussianGammaEulerHeadLower.factor_represents N z B hB))
    (GaussianRationalHorner.represents_rescale _ _ B (succ N) (GaussianRationalHorner.ofGaussian_represents a B hB))

theorem factorial_zero (z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx] factorialLaw z B zero := by
  have point := GaussianRationalHorner.ofGaussian_canonical (Γ := Γ) z B hB
  have linearZero : Γ ⊢[PRAAx] linear z B zero ≐ ofGaussian z B :=
    GaussianRationalHorner.canonical_unique _ _ z B
      (GaussianRationalHorner.ofGaussian_canonical _ _ hB) point hB
      (GaussianRationalHorner.represents_congr (.eqRefl _) (GaussianGammaEulerHeadLower.translated_zero z B) (.eqRefl _)
        (GaussianRationalHorner.ofGaussian_represents _ _ hB))
      (GaussianRationalHorner.ofGaussian_represents z B hB)
  have rising := (prefix_succ z B zero).eqTrans
    ((qmul_congr (prefix_zero z B) linearZero).eqTrans ((qmul_commutative _ _).eqTrans (qmul_one_right _ point)))
  exact (natScale_congr (fact_zero zero) (head_zero z B hB)).eqTrans
    ((GaussianRationalNaturalScale.natScale_one_canonical _ point).eqTrans rising.eqSymm)

theorem factorial_step (z B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) (ih : Γ ⊢[PRAAx] factorialLaw z B N) : Γ ⊢[PRAAx]
    factorialLaw z B (succ N) := by
  have factStep : Γ ⊢[PRAAx] fact (succ N) ≐ fact N*succ N := fact_succ N zero
  exact (natScale_congr factStep (head_succ z B N)).eqTrans
    ((natScale_multiply (fact N) (succ N) _).eqSymm.eqTrans
      ((natScale_congr (.eqRefl _) ((natScale_product (succ N) _ _).eqSymm.eqTrans
        (qmul_congr (.eqRefl _) (factor_clearing z B N hB)))).eqTrans
          ((scaled_left_product _ _ _).eqTrans ((qmul_congr ih (.eqRefl _)).eqTrans (prefix_succ z B (succ N)).eqSymm))))

theorem factorial_head (z B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx] factorialLaw z B N := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hB.shift
  have all : Γ ⊢[PRAAx] .all (factorialLaw (Syn.shift z) (Syn.shift B) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_factorialLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact factorial_zero z B hB
    · simp only [subst_factorialLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact factorial_step _ _ _ hs.wk Prf.hyp0
  simpa only [subst_factorialLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N

theorem head_canonical (z B N : PTm n) : Γ ⊢[PRAAx] canonical (head z B N) := GaussianRationalHorner.qmul_canonical _ _
theorem value_canonical (z B N : PTm n) : Γ ⊢[PRAAx] canonical (value z B N) := GaussianRationalReciprocal.reciprocal_canonical _

theorem value_inverse (z B A N : PTm n) (h : Γ ⊢[PRAAx] source z B A) : Γ ⊢[PRAAx]
    qmul (head z B N) (value z B N) ≐ qone := by
  let D := pw A (succ N)*fact N
  have hD := GaussianGammaEulerHeadLower.prefix_denominator_positive (Γ := Γ) A N h.andE₂.andE₁
  have lower := GaussianGammaEulerHeadLower.prefix_lower z B one A N h.andE₁ h.andE₂.andE₁
    (GaussianEulerBetaPoleGuard.all_finite_guards z B A N h.andE₂.andE₂)
  have actual : Γ ⊢[PRAAx] GaussianRationalLowerBounds.lower (head z B N) one D :=
    GaussianRationalLowerBounds.lower_congr (.eqRefl _) (GaussianPolynomialPerturbation.one_power (succ N)) (.eqRefl _) lower
  exact GaussianRationalReciprocal.reciprocal_identity _ (GaussianNameReciprocal.lower_norm_positive _ D hD
    (GaussianRationalLowerBounds.name_lower _ one D (le_refl one) hD actual))

theorem natural_scale_one (t : PTm n) : Γ ⊢[PRAAx] natScale t qone ≐ naturalPoint t :=
  (natScale_as_product t qone).eqTrans (qmul_one_right _ (GaussianRationalHorner.ofGaussian_canonical _ _ (le_refl one)))

/-- The reciprocal ORIGINAL head is exactly N! over the actual rising
product in the genuine multiplicative, cleared sense. -/
theorem cleared_product_value (z B A N : PTm n) (h : Γ ⊢[PRAAx] source z B A) : Γ ⊢[PRAAx]
    qmul (risingProduct z B (succ N)) (value z B N) ≐ naturalPoint (fact N) :=
  (qmul_congr (factorial_head z B N h.andE₁).eqSymm (.eqRefl _)).eqTrans
    ((scaled_left_product _ _ _).eqSymm.eqTrans
      ((natScale_congr (.eqRefl _) (value_inverse z B A N h)).eqTrans (natural_scale_one _)))

theorem shifted_source (z B A : PTm n) (h : Γ ⊢[PRAAx] source z B A) : Γ ⊢[PRAAx] source (shifted z B) B A :=
  .andI h.andE₁ (.andI h.andE₂.andE₁ (by
    exact PolynomialBisection.zle_congr rfl
      (by simp only [shifted,GaussianRootAlgebra.re_scale,ZT.toZ_mul,ZT.toZ_ofNat])
      (GaussianEulerBetaPoleGuard.translated_real_margin z B A one h.andE₂.andE₂)))

theorem head_IBP_balance (z B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    qmul (ofGaussian z B) (head (shifted z B) B N) ≐ qmul (naturalPoint (succ N)) (head z B (succ N)) := by
  have cleared : Γ ⊢[PRAAx] natScale (succ N) (head z B (succ N)) ≐ qmul (head z B N) (linear z B (succ N)) :=
    (natScale_congr (.eqRefl _) (head_succ z B N)).eqTrans
      ((natScale_product (succ N) _ _).eqSymm.eqTrans (qmul_congr (.eqRefl _) (factor_clearing z B N hB)))
  exact (GaussianGammaEulerHeadShift.shift_identity z B N hB).eqTrans
    (cleared.eqSymm.eqTrans (natScale_as_product _ _))

/-- Genuine finite integration-by-parts recurrence of the ORIGINAL
product-side Beta value, valid at every internal N. -/
theorem product_value_IBP (z B A N : PTm n) (h : Γ ⊢[PRAAx] source z B A) : Γ ⊢[PRAAx]
    qmul (ofGaussian z B) (value z B (succ N)) ≐ natScale (succ N) (value (shifted z B) B N) := by
  let a := ofGaussian z B
  let b := head (shifted z B) B N
  let c := naturalPoint (succ N)
  let d := head z B (succ N)
  let x := value z B (succ N)
  let y := value (shifted z B) B N
  have bx : Γ ⊢[PRAAx] qmul b y ≐ qone := value_inverse (shifted z B) B A N (shifted_source z B A h)
  have dx : Γ ⊢[PRAAx] qmul d x ≐ qone := value_inverse z B A (succ N) h
  have left : Γ ⊢[PRAAx] qmul (qmul a b) (qmul x y) ≐ qmul a x :=
    (qmul_shuffle a b x y).eqTrans ((qmul_congr (.eqRefl _) bx).eqTrans (qmul_one_right _ (GaussianRationalHorner.qmul_canonical _ _)))
  have right : Γ ⊢[PRAAx] qmul (qmul c d) (qmul x y) ≐ qmul c y :=
    (qmul_congr (.eqRefl _) (qmul_commutative x y)).eqTrans
      ((qmul_shuffle c d y x).eqTrans ((qmul_congr (.eqRefl _) dx).eqTrans (qmul_one_right _ (GaussianRationalHorner.qmul_canonical _ _))))
  exact left.eqSymm.eqTrans ((qmul_congr (head_IBP_balance z B N h.andE₁) (.eqRefl _)).eqTrans
    (right.eqTrans (natScale_as_product _ _).eqSymm))

/-- Concrete amplification radius for finite endpoint errors. -/
def denominator (A N : PTm n) : PTm n := pw A (succ N)*fact N
@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (A N : PTm n) :
    Syn.subst σ (denominator A N) = denominator (Syn.subst σ A) (Syn.subst σ N) := by simp [denominator,fact]
theorem denominator_positive (A N : PTm n) (hA : Γ ⊢[PRAAx] le one A) : Γ ⊢[PRAAx] le one (denominator A N) :=
  GaussianGammaEulerHeadLower.prefix_denominator_positive A N hA

theorem source_head_lower (z B A N : PTm n) (h : Γ ⊢[PRAAx] source z B A) : Γ ⊢[PRAAx]
    GaussianRationalLowerBounds.lower (head z B N) one (denominator A N) :=
  GaussianRationalLowerBounds.lower_congr (.eqRefl _) (GaussianPolynomialPerturbation.one_power (succ N)) (.eqRefl _)
    (GaussianGammaEulerHeadLower.prefix_lower z B one A N h.andE₁ h.andE₂.andE₁
      (GaussianEulerBetaPoleGuard.all_finite_guards z B A N h.andE₂.andE₂))
theorem value_bound (z B A N : PTm n) (h : Γ ⊢[PRAAx] source z B A) : Γ ⊢[PRAAx]
    GaussianRationalMetric.bounded (value z B N) (denominator A N) one :=
  GaussianRationalLowerBounds.inverse_bound _ one _ (le_refl one) (denominator_positive A N h.andE₂.andE₁) (source_head_lower z B A N h)

theorem natural_point_lower (t : PTm n) : Γ ⊢[PRAAx] GaussianRationalLowerBounds.lower (naturalPoint t) t one := by
  have norm : Γ ⊢[PRAAx] ComplexLogarithmRemainder.normSq (ComplexLogarithmRemainder.scale t ComplexLogarithmRemainder.oneCode) ≐ t*t :=
    (ComplexLogarithmRemainder.normSq_scale t _).eqTrans
      ((congrMul (.eqRefl _) ComplexLogarithmRemainder.normSq_one).eqTrans (by ipra_ring))
  exact GaussianRationalLowerBounds.lower_from_representation _ _ one t one (le_refl one) (le_refl one)
    (GaussianRationalNaturalScale.natural_point_represents t)
    (le_congr (by ipra_ring) ((by ipra_ring : Γ ⊢[PRAAx] one*one*ComplexLogarithmRemainder.normSq (ComplexLogarithmRemainder.scale t ComplexLogarithmRemainder.oneCode) ≐
      ComplexLogarithmRemainder.normSq (ComplexLogarithmRemainder.scale t ComplexLogarithmRemainder.oneCode)).eqTrans norm).eqSymm (le_refl (t*t)))

theorem rising_lower (z B A N : PTm n) (h : Γ ⊢[PRAAx] source z B A) : Γ ⊢[PRAAx]
    GaussianRationalLowerBounds.lower (risingProduct z B (succ N)) (fact N) (denominator A N) := by
  have raw := GaussianRationalLowerBounds.product_lower _ _ (fact N) one one (denominator A N) (le_refl one)
    (denominator_positive A N h.andE₂.andE₁) (natural_point_lower (Γ := Γ) (fact N)) (source_head_lower z B A N h)
  exact GaussianRationalLowerBounds.lower_congr
    ((natScale_as_product (fact N) (head z B N)).eqSymm.eqTrans (factorial_head z B N h.andE₁))
    (by ipra_ring) (by ipra_ring) raw

theorem rising_inverse (z B A N : PTm n) (h : Γ ⊢[PRAAx] source z B A) : Γ ⊢[PRAAx]
    qmul (risingProduct z B (succ N)) (reciprocal (risingProduct z B (succ N))) ≐ qone :=
  GaussianRationalReciprocal.reciprocal_identity _ (GaussianNameReciprocal.lower_norm_positive _ (denominator A N)
    (denominator_positive A N h.andE₂.andE₁) (GaussianRationalLowerBounds.name_lower _ _ _
      (GaussianRationalPolynomialExponential.factorial_positive N) (denominator_positive A N h.andE₂.andE₁) (rising_lower z B A N h)))

/-- Literal actual rational quotient, using the SAME original head and
SAME actual rising product, not a stipulated symbolic quotient. -/
theorem quotient_formula (z B A N : PTm n) (h : Γ ⊢[PRAAx] source z B A) : Γ ⊢[PRAAx]
    value z B N ≐ qmul (naturalPoint (fact N)) (reciprocal (risingProduct z B (succ N))) := by
  let r := risingProduct z B (succ N)
  let v := value z B N
  let u := reciprocal r
  have inverse : Γ ⊢[PRAAx] qmul u r ≐ qone := (qmul_commutative _ _).eqTrans (rising_inverse z B A N h)
  have unit : Γ ⊢[PRAAx] qmul qone v ≐ v := (qmul_commutative _ _).eqTrans (qmul_one_right _ (value_canonical z B N))
  exact unit.eqSymm.eqTrans ((qmul_congr inverse.eqSymm (.eqRefl _)).eqTrans
    ((qmul_associative _ _ _).eqTrans ((qmul_congr (.eqRefl _) (cleared_product_value z B A N h)).eqTrans (qmul_commutative _ _))))

theorem original_value_IBP (z R B A N : PTm n) (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R B A) : Γ ⊢[PRAAx]
    qmul (ofGaussian z B) (value z B (succ N)) ≐ natScale (succ N) (value (shifted z B) B N) :=
  product_value_IBP z B A N (GaussianEulerBetaPoleGuard.original_integral_source z R B A N h).andE₁

def output (z B N : PTm n) : PTm n := pairT (value z B N)
  (pairT (risingProduct z B (succ N)) (pairT (qmul (risingProduct z B (succ N)) (value z B N)) (naturalPoint (fact N))))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (z B N : PTm n) : PTm n := ap3 outputF z B N
theorem program_at (z B N : PTm n) : Γ ⊢[PRAAx] run z B N ≐ output z B N := by
  simpa [run,outputF,output,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![z,B,N]

theorem original_factorial_Euler_head_rising_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ factorialLaw (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (factorial_head _ _ _ Prf.hyp0))
theorem original_Beta_cleared_product_value_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) ⟶
      qmul (risingProduct (var 0) (var 1) (succ (var 3))) (value (var 0) (var 1) (var 3)) ≐ naturalPoint (fact (var 3))) :=
  closeUniv 4 (.impI (cleared_product_value _ _ _ _ Prf.hyp0))
theorem original_Beta_literal_quotient_formula_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) ⟶ value (var 0) (var 1) (var 3) ≐
      qmul (naturalPoint (fact (var 3))) (reciprocal (risingProduct (var 0) (var 1) (succ (var 3))))) :=
  closeUniv 4 (.impI (quotient_formula _ _ _ _ Prf.hyp0))
theorem original_Beta_product_value_IBP_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) ⟶ qmul (ofGaussian (var 0) (var 1)) (value (var 0) (var 1) (succ (var 3))) ≐
      natScale (succ (var 3)) (value (shifted (var 0) (var 1)) (var 1) (var 3))) :=
  closeUniv 4 (.impI (product_value_IBP _ _ _ _ Prf.hyp0))
theorem original_Beta_endpoint_error_amplification_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) ⟶ GaussianRationalMetric.bounded (value (var 0) (var 1) (var 3)) (denominator (var 2) (var 3)) one) :=
  closeUniv 4 (.impI (value_bound _ _ _ _ Prf.hyp0))
theorem actual_Beta_product_value_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) :=
  closeUniv 3 (program_at _ _ _)

end LeanProofs.IPRA.Analysis.GaussianEulerBetaProductValue

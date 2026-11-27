import IPRADerivations.Analysis.Stirling.Binet.ExponentialIntegrals.GaussianBinetExponentialPanel
import IPRADerivations.Analysis.Stirling.Binet.Laplace.Strips.GaussianBinetLaplaceStrip
import IPRADerivations.Analysis.Integration.CompactGrids.Splits.GaussianCompactZeroWidth
import IPRADerivations.Analysis.Integration.CompactGrids.Splits.GaussianCompactRiemannSplit
import IPRADerivations.Analysis.Integration.Quadrature.SquareSubstitution.GaussianRationalQuadratureSquareCells
import IPRADerivations.Analysis.Gamma.EulerProducts.CanonicalProducts.Tails.GaussianGammaCanonicalTailExponential

/-!
# Actual equally spaced rows of the complex Laplace antiderivative

The compact interval has coordinate `1+t`, with physical time from
zero to the integer horizon. The original constant-input exponential
is used at every tag, including the endpoints.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianBinetExponentialIntegralGrid

open_ipra
open GaussianBinetExponentialPanel (sample nonpositive)
open GaussianBinetLaplaceStrip (tagNumerator)
open GaussianCompactRiemannName (sampleBody sampleData quadrature grid sample_body_at)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalCoefficientScaling (qmul_add)
open GaussianRationalHorner (qmul qmul_canonical qzero positive_product)
open GaussianRationalMetric (bounded qnegative)
open GaussianRationalReciprocal (bounded_product bound_congr bounded_product_one)
open GaussianRationalSyntheticDivision (qmul_congr qone qmul_zero_right)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def exponent (q A B : PTm n) : PTm n := qmul q (fraction A B)
def row (p q S A B : PTm n) : PTm n := sample p (exponent q A B) S
def evaluatorTerm (p t x : PTm n) : PTm n := row p (fstT x) (sndT x) (tagNumerator t) (sndT t)
def evaluatorF : PR 3 := PTm.toPR (evaluatorTerm (var 0) (var 1) (var 2))
def value (p q S T N : PTm n) : PTm n := quadrature evaluatorF p N one T one (pairT q S)

ipra_subst exponent

ipra_subst row

ipra_subst evaluatorTerm

ipra_subst value [one]

private theorem row_congr (p q S A A' B B' : PTm n)
    (ha : Γ ⊢[PRAAx] A ≐ A') (hb : Γ ⊢[PRAAx] B ≐ B') :
    Γ ⊢[PRAAx] row p q S A B ≐ row p q S A' B' := by
  simpa only [subst_row,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (row (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
      (σ := ![p,q,S,A,B]) (σ' := ![p,q,S,A',B'])
      (fun i => by fin_cases i; exact .eqRefl _; exact .eqRefl _; exact .eqRefl _; exact ha; exact hb)

theorem evaluator_at (p t q S : PTm n) :
    Γ ⊢[PRAAx] ap3 evaluatorF p t (pairT q S) ≐ row p q S (tagNumerator t) (sndT t) := by
  have read := toPR_pairVector3_eq (Γ := Γ) (k := 1)
    (row (var 0) (var 2) (var 3) (tagNumerator (var 1)) (sndT (var 1))) p t ![q, S]
  simp only [subst_row,
    GaussianBinetLaplaceStrip.subst_tagNumerator, subst_sndT, Syn.subst_var] at read
  exact read

theorem cell_at (j p q S T N : PTm n) :
    Γ ⊢[PRAAx] inst2 (sampleBody evaluatorF) j (sampleData p N one T one (pairT q S)) ≐ row p q S (T*j) N := by
  let t := grid j N one T one
  have hd : Γ ⊢[PRAAx] sndT t ≐ N := (snd_pair _ _).eqTrans (one_mul N)
  have hn : Γ ⊢[PRAAx] fstT t ≐ T*j+N := (fst_pair _ _).eqTrans (by ipra_ring)
  have ht : Γ ⊢[PRAAx] tagNumerator t ≐ T*j := (congrMonus hn hd).eqTrans (add_monus _ _)
  exact (sample_body_at evaluatorF j p N one T one _).eqTrans
    ((evaluator_at p t q S).eqTrans (row_congr p q S _ _ _ _ ht hd))

theorem step_coefficient (q T j N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] GaussianRationalHorner.qadd (exponent q (T*j) N) (exponent q T N) ≐ exponent q (T*succ j) N :=
  (qmul_add q _ _).eqSymm.eqTrans
    (qmul_congr (.eqRefl _) ((GaussianRationalQuadratureSquareCells.fraction_add_same (T*j) T N hN).eqTrans
      (GaussianCompactRiemannName.fraction_congr _ _ _ _ (by ipra_ring) (.eqRefl _))))

theorem step_bound (q R T N : PTm n) (hb : Γ ⊢[PRAAx] bounded q R one) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] bounded (exponent q T N) (R*T) N := by
  have f := bound_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point T N hN).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianDominantPairAlgebra.radius_bounded T N hN)
  exact GaussianRationalReciprocal.bounded_product_one_left hN hb f

theorem exponent_input (q R T j N : PTm n) (hb : Γ ⊢[PRAAx] bounded q R one)
    (hN : Γ ⊢[PRAAx] le one N) (hj : Γ ⊢[PRAAx] le j N) :
    Γ ⊢[PRAAx] GaussianRadiusExponentialName.input constantF (R*T) (exponent q (T*j) N) := by
  have hB : Γ ⊢[PRAAx] le (T*j) (T*N) :=
    le_congr (mul_comm j T) (mul_comm N T) (mul_le_mul_right T hj)
  have frac := GaussianEulerExponentCompactBounds.fraction_bound (T*j) N T hN hB
  exact GaussianSignedNameExponentialOrder.constant_input _ _
    (bounded_product_one hb frac)

theorem right_endpoint (p q S T N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] row p q S (T*N) N ≐ row p q S T one := by
  have e : Γ ⊢[PRAAx] fraction (T*N) N ≐ fraction T one :=
    (GaussianCompactRiemannName.fraction_congr _ _ _ _ (mul_comm T N) (by ipra_ring)).eqTrans
      (GaussianCompactRiemannSplit.fraction_cancel N T one hN (le_refl one))
  have ed : Γ ⊢[PRAAx] exponent q (T*N) N ≐ exponent q T one := qmul_congr (.eqRefl _) e
  exact congrAp2 GaussianBinetExponentialPanel.expoF (.eqRefl p) (congrPairT (.eqRefl S) ed)

theorem left_endpoint (p q S T N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] row p q S (T*zero) N ≐ qone := by
  let z := exponent q (T*zero) N
  let K := GaussianRadiusExponentialName.index S p
  let Q := GaussianRadiusExponentialName.query constantF S p z
  let U := GaussianRationalPolynomialExponential.scalarSum Q K
  have ef : Γ ⊢[PRAAx] fraction (T*zero) N ≐ qzero :=
    (GaussianCompactRiemannName.fraction_congr _ _ _ _ (by ipra_ring) (.eqRefl _)).eqTrans
      (GaussianCompactZeroWidth.zero_fraction N hN)
  have e : Γ ⊢[PRAAx] z ≐ qzero :=
    (qmul_congr (.eqRefl q) ef).eqTrans (qmul_zero_right q)
  have read : Γ ⊢[PRAAx] row p q S (T*zero) N ≐ U := GaussianRadiusExponentialName.sample_at constantF S p z
  have eg : Γ ⊢[PRAAx] Q ≐ qzero :=
    (constant_at (GaussianRadiusExponentialName.inputPrecision S p) z).eqTrans e
  have clear : Γ ⊢[PRAAx] U ≐ GaussianRationalPolynomialExponential.scalarSum qzero K :=
    GaussianNameConjugation.scalar_sum_congr K eg
  exact read.eqTrans (clear.eqTrans (GaussianGammaCanonicalTailExponential.scalar_zero_point K))

end LeanProofs.IPRA.Analysis.GaussianBinetExponentialIntegralGrid

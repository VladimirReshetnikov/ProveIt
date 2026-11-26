import IPRADerivations.Analysis.Integration.GaussianMonomialDecayMajorant
import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerUpperTailLeftNorm
import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerLowerTransformedIntegrand
import IPRADerivations.Core.CongruenceTactic

/-!
# Actual monomial-decay quadrature with the exact factorial leading constant

The evaluator is the literal canonical rational monomial times the original
named decay. The old scalar half-decay reference and exact compact weights
are reused. The leading upper-integral budget is exactly 2^(d+1)d!, with
all original finite mesh and observation errors retained separately.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianMonomialDecayQuadrature

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianMonomialDecayMajorant (sample)
open GaussianEulerCompactUpperTail (scalarBody reference_row scaledF scaled_quadrature halfEvaluator)
open RationalGaussianRealPart (embedBody)
open GaussianEulerWeightedHalfDecay (majorant)
open GaussianEulerUpperTailScalar (budget scalarMajorant)
open GaussianCompactRiemannName (sampleBody sampleData sample_body_at quadrature)
open GaussianRationalSumMajorant (majorized termsMajorized majorized_congr)
open GaussianRationalRiemannRefinement (termsDistance)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianDominantPairAlgebra (radius_bounded)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def evaluator (p t d : PTm n) : PTm n := sample p d (fstT t) (sndT t)
def evaluatorF : PR 3 := PTm.toPR (evaluator (var 0) (var 1) (var 2))
@[simp] theorem subst_evaluator {m : ℕ} (σ : Fin n → PTm m) (p t d : PTm n) :
    Syn.subst σ (evaluator p t d) = evaluator (Syn.subst σ p) (Syn.subst σ t) (Syn.subst σ d) := by simp [evaluator]

theorem evaluator_at (p a b d : PTm n) : Γ ⊢[PRAAx]
    ap3 evaluatorF p (pairT a b) d ≐ sample p d a b := by
  have program : Γ ⊢[PRAAx] ap3 evaluatorF p (pairT a b) d ≐ evaluator p (pairT a b) d := by
    simpa [evaluatorF,ap3] using toPR_eq (Γ := Γ) (evaluator (var 0) (var 1) (var 2) : PTm 3) ![p,pairT a b,d]
  apply program.eqTrans
  change Γ ⊢[PRAAx] sample p d (fstT (pairT a b)) (sndT (pairT a b)) ≐ sample p d a b
  ipra_congr (sample (var 0) (var 1) (var 2) (var 3) : PTm 4) with [.eqRefl p, .eqRefl d, fst_pair a b, snd_pair a b]

theorem point_majorized (p d a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hab : Γ ⊢[PRAAx] le b a) : Γ ⊢[PRAAx]
    majorized (sample p d a b) (scalarMajorant p d a b) := by
  have den := GaussianEulerUpperTailPointwise.majorant_bottom_positive (Γ := Γ) p p a b
  have rep := GaussianEuclideanDistanceName.fraction_represents
    (GaussianEulerUpperTailPointwise.majorantTop p p d a b) (GaussianEulerUpperTailPointwise.majorantBottom p p a b) den
  exact GaussianRationalSumMajorant.from_representation _ _ _ _ den
    (GaussianRationalL1.nonnegative_of_representation _ _ _ den rep) rep
    (GaussianMonomialDecayMajorant.original_upper_tail_pointwise p p d a b (.andI hb hab))

theorem majorized_row (i p N a C E d : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hE : Γ ⊢[PRAAx] le one E) (hea : Γ ⊢[PRAAx] le E a) : Γ ⊢[PRAAx]
    majorized (inst2 (sampleBody evaluatorF) i (sampleData p N a C E d))
      (inst2 scalarBody i (sampleData p N a C E d)) := by
  let u := a*N+C*i
  let v := E*N
  have hv : Γ ⊢[PRAAx] le one v := positive_product _ _ hE hN
  have hle : Γ ⊢[PRAAx] le v u := le_trans (mul_le_mul_right N hea) (le_add_right _ _)
  exact majorized_congr ((sample_body_at evaluatorF i p N a C E d).eqTrans (evaluator_at p u v d)).eqSymm
    (GaussianEulerCompactUpperTail.scalar_body_at i p N a C E d).eqSymm (point_majorized p d u v hv hle)

theorem original_grid_bound_from_half (p N a C E d U V : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hE : Γ ⊢[PRAAx] le one E) (hea : Γ ⊢[PRAAx] le E a) (hV : Γ ⊢[PRAAx] le one V)
    (hHalf : Γ ⊢[PRAAx] bounded (quadrature halfEvaluator p N a C E zero) U V) :
    Γ ⊢[PRAAx] bounded (quadrature evaluatorF p N a C E (d))
      ((C*budget d)*V+(majorant d*U)*(E*unit p)) ((E*unit p)*V) := by
  let x := d
  let X := sampleData p N a C E x
  let Y := sampleData p N a C E d
  let M := majorant d
  let Z := sampleData p N a C E M
  have hm : Γ ⊢[PRAAx] termsMajorized (sampleBody evaluatorF) scalarBody N X Y := by
    refine .allI (.impI ?_)
    have n' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hN.shift
    have e' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift E) := by simpa [Fm.shift,Syn.shift] using hE.shift
    have ea' : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift E) (Syn.shift a) := by simpa [Fm.shift,Syn.shift] using hea.shift
    simpa only [termsMajorized,X,Y,x,Syn.shift,GaussianCompactRiemannName.subst_sampleData] using
      majorized_row (var 0) (Syn.shift p) (Syn.shift N) (Syn.shift a) (Syn.shift C) (Syn.shift E)
        (Syn.shift d) n'.wk e'.wk ea'.wk
  have er : Γ ⊢[PRAAx] termsDistance (embedBody scalarBody) (sampleBody scaledF) N Y Z (budget d) (unit p) := by
    refine .allI (.impI ?_)
    have n' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hN.shift
    have e' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift E) := by simpa [Fm.shift,Syn.shift] using hE.shift
    simpa only [termsDistance,Y,Z,M,Syn.shift,GaussianCompactRiemannName.subst_sampleData,
      GaussianEulerWeightedHalfDecay.subst_majorant,GaussianEulerUpperTailScalar.subst_budget,GaussianCoefficientNameBounds.subst_unit] using
      reference_row (var 0) (Syn.shift p) (Syn.shift N) (Syn.shift a) (Syn.shift C) (Syn.shift E)
        (Syn.shift d) n'.wk e'.wk
  have ref : Γ ⊢[PRAAx] bounded (quadrature scaledF p N a C E M) (M*U) V :=
    GaussianRationalReciprocal.bound_congr (scaled_quadrature p N a C E M).eqSymm (.eqRefl _) (one_mul V)
      (GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ (le_refl one) hV (radius_bounded M one (le_refl one)) hHalf)
  exact GaussianCompactScalarMajorant.compact_majorant_bound evaluatorF scaledF scalarBody
    p p N a C E x Y M (budget d) (unit p) (M*U) V hN hE (unit_positive p) hV hm er ref

def errorDenominator (p q N E : PTm n) : PTm n := GaussianEulerHalfDecayLeftNorm.errorDenominator p q N E
def errorNumerator (p q N C E d : PTm n) : PTm n :=
  num 3*majorant d*C*C*unit p*unit q+two*E*N*C*(majorant d+budget d)*unit q+num 40*majorant d*E*E*N*unit p
def cap (d : PTm n) : PTm n := GaussianGammaIntegralCutoffs.tailCoefficient d

theorem original_grid_uniform_bound (p q N C E d : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hC : Γ ⊢[PRAAx] le one C) (hE : Γ ⊢[PRAAx] le one E)
    (hstep : Γ ⊢[PRAAx] le C ((two*E)*N)) : Γ ⊢[PRAAx]
    bounded (quadrature evaluatorF p N E C E d)
      (cap d*errorDenominator p q N E+errorNumerator p q N C E d) (errorDenominator p q N E) := by
  let Q := unit q
  let U := GaussianEulerHalfDecayLeftNorm.numerator p q N C E (Q+two) Q
  let V := GaussianEulerHalfDecayLeftNorm.denominator p q N E Q
  have left := GaussianEulerLowerTransformedIntegrand.decay_bound E (two*E) q hE (positive_product _ _ (le_succ_self one) hE)
  have half := GaussianEulerHalfDecayLeftNorm.original_half_decay_left_norm p q N E C E zero (Q+two) Q
    (.andI hE (.andI hN (.andI hE (.andI hC (.andI (unit_positive q) hstep))))) left
  have hV : Γ ⊢[PRAAx] le one V := positive_product _ _ (unit_positive q)
    (GaussianEulerHalfDecayLeftNorm.error_denominator_positive p q N E hN hE)
  have actual := original_grid_bound_from_half p N E C E d U V hN hE (le_refl E) hV half
  have coef := natEq (GaussianEulerUpperTailLeftNorm.original_coefficient (Γ := Γ) d)
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ (positive_product _ _ hE (unit_positive p)) hV)
    (GaussianEulerHalfDecayLeftNorm.error_denominator_positive p q N E hN hE)
    (le_of_eq_add (d := zero) (by
      apply deriveNat
      dsimp only [U,V,Q,cap,errorNumerator,errorDenominator,GaussianEulerHalfDecayLeftNorm.numerator,
        GaussianEulerHalfDecayLeftNorm.denominator,GaussianEulerHalfDecayLeftNorm.errorNumerator,GaussianEulerHalfDecayLeftNorm.errorDenominator]
      ipra_simps
      rw [coef]
      ring)) actual

theorem original_literal_monomial_upper_integral_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((le one (var 2) ⋏ le one (var 3) ⋏ le one (var 4) ⋏ le (var 3) ((two*var 4)*var 2)) ⟶
      bounded (quadrature evaluatorF (var 0) (var 2) (var 4) (var 3) (var 4) (var 5))
        (cap (var 5)*errorDenominator (var 0) (var 1) (var 2) (var 4)+errorNumerator (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
        (errorDenominator (var 0) (var 1) (var 2) (var 4))) :=
  closeUniv 6 (.impI (original_grid_uniform_bound _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianMonomialDecayQuadrature

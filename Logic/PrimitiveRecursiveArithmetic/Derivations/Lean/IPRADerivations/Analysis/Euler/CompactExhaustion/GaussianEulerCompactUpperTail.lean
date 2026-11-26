import IPRADerivations.Analysis.Euler.PositiveAxis.UpperBounds.GaussianEulerUpperTailScalar
import IPRADerivations.Analysis.Euler.PositiveAxis.HalfDecay.GaussianEulerHalfDecayTailBound
import IPRADerivations.Core.CongruenceTactic

/-!
# Original compact Euler quadrature at the upper cutoff

The pointwise factorial majorants are summed on the actual compact
grid. The scaled reference is proved to be the same weighted
half-decay quadrature multiplied by the factorial constant, with
no change to the mesh or to the Euler evaluator.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerCompactUpperTail

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerUpperPowerCoefficients (source)
open GaussianEulerWeightedHalfDecay (majorant)
open GaussianEulerUpperTailScalar (budget scalarMajorant)
open GaussianEulerIntegrandName (evaluatorF fixedData sample)
open GaussianCompactRiemannName (sampleBody sampleData sample_body_at quadrature
  field0 field1 field2 field3 field4 field5 field0_at field1_at field2_at field3_at field4_at field5_at)
open GaussianRationalSumMajorant (majorized termsMajorized majorized_congr)
open GaussianRationalRiemannRefinement (termsDistance weight)
open GaussianRationalFiniteSum (sum termsEqual multiplyBody multiply_body_at)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianDominantPairAlgebra (radiusPoint radius_bounded)
open RationalGaussianEmbedding (embed)
open RationalGaussianRealPart (embedBody)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def scalarBody : PTm 2 :=
  scalarMajorant (field0 (var 1)) (field5 (var 1))
    (field2 (var 1)*field1 (var 1)+field3 (var 1)*var 0) (field4 (var 1)*field1 (var 1))
abbrev halfEvaluator : PR 3 := GaussianEulerHalfDecayQuadrature.halfF
def scaledEval (p t M : PTm n) : PTm n := qmul (radiusPoint M one) (ap3 halfEvaluator p t zero)
def scaledF : PR 3 := PTm.toPR (scaledEval (var 0) (var 1) (var 2))

@[simp] theorem subst_scaledEval {m : ℕ} (σ : Fin n → PTm m) (p t M : PTm n) :
    Syn.subst σ (scaledEval p t M) = scaledEval (Syn.subst σ p) (Syn.subst σ t) (Syn.subst σ M) :=
  by simp [scaledEval]

theorem scalar_body_at (i p N a C E R : PTm n) : Γ ⊢[PRAAx]
    inst2 scalarBody i (sampleData p N a C E R) ≐ scalarMajorant p R (a*N+C*i) (E*N) := by
  let x := sampleData p N a C E R
  have hint := congrAdd (congrMul (field2_at p N a C E R) (field1_at p N a C E R))
    (congrMul (field3_at p N a C E R) (Prf.eqRefl (Γ := Γ) i))
  have denom : Γ ⊢[PRAAx] field4 x*field1 x ≐ E*N :=
    congrMul (field4_at p N a C E R) (field1_at p N a C E R)
  ipra_congr (scalarMajorant (var 0) (var 1) (var 2) (var 3) : PTm 4) with
    [field0_at p N a C E R, field5_at p N a C E R, hint, denom] using [scalarBody, inst2, x]

theorem scaled_at (p t M : PTm n) : Γ ⊢[PRAAx]
    ap3 scaledF p t M ≐ qmul (radiusPoint M one) (ap3 halfEvaluator p t zero) := by
  have e : Γ ⊢[PRAAx] ap3 scaledF p t M ≐ scaledEval p t M := by
    simpa [scaledF,ap3] using toPR_eq (Γ := Γ) (scaledEval (var 0) (var 1) (var 2) : PTm 3) ![p,t,M]
  exact e

theorem majorized_row (i p N a C E z R B : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hE : Γ ⊢[PRAAx] le one E) (hea : Γ ⊢[PRAAx] le E a) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] majorized
      (inst2 (sampleBody evaluatorF) i (sampleData p N a C E (fixedData z B)))
      (inst2 scalarBody i (sampleData p N a C E R)) := by
  let u := a*N+C*i
  let v := E*N
  have hv : Γ ⊢[PRAAx] le one v := positive_product _ _ hE hN
  have hle : Γ ⊢[PRAAx] le v u := le_trans (mul_le_mul_right N hea) (le_add_right _ _)
  have hs : Γ ⊢[PRAAx] GaussianEulerUpperPowerOrder.source z R B u v :=
    .andI h (.andI (.andI (le_trans hv hle) hv) hle)
  exact majorized_congr (sample_body_at evaluatorF i p N a C E (fixedData z B)).eqSymm
    (scalar_body_at i p N a C E R).eqSymm
    (GaussianEulerUpperTailScalar.original_cell_majorized p z R B u v hs)

theorem reference_row (i p N a C E R : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hE : Γ ⊢[PRAAx] le one E) :
    Γ ⊢[PRAAx] distanceBounded
      (inst2 (embedBody scalarBody) i (sampleData p N a C E R))
      (inst2 (sampleBody scaledF) i (sampleData p N a C E (majorant R))) (budget R) (unit p) := by
  let u := a*N+C*i
  let v := E*N
  let M := majorant R
  have hv : Γ ⊢[PRAAx] le one v := positive_product _ _ hE hN
  have e₁ : Γ ⊢[PRAAx] inst2 (embedBody scalarBody) i (sampleData p N a C E R) ≐ embed (scalarMajorant p R u v) := by
    simpa only [inst2,embedBody,RationalGaussianEmbedding.subst_embed] using
      RationalGaussianRealPart.embed_congr (scalar_body_at i p N a C E R)
  have e₂ := (sample_body_at (Γ := Γ) scaledF i p N a C E M).eqTrans
    ((scaled_at p (pairT u v) M).eqTrans (qmul_congr (.eqRefl _)
      (GaussianEulerHalfDecayReference.actual_half_evaluator p u v zero)))
  exact distance_congr e₁.eqSymm e₂.eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianEulerUpperTailScalar.scalar_majorant_scaled_reference_error p R u v hv)

theorem scaled_quadrature (p N a C E M : PTm n) : Γ ⊢[PRAAx]
    quadrature scaledF p N a C E M ≐
      qmul (radiusPoint M one) (quadrature halfEvaluator p N a C E zero) := by
  let f := sampleBody scaledF
  let g := sampleBody halfEvaluator
  let x := sampleData p N a C E M
  let y := sampleData p N a C E zero
  let r := radiusPoint M one
  let w := weight C E N
  let S := sum g N y
  have rows : Γ ⊢[PRAAx] termsEqual f (multiplyBody g) N x (pairT r y) := by
    refine .allI (.impI ?_)
    let p' := Syn.shift p
    let N' := Syn.shift N
    let a' := Syn.shift a
    let C' := Syn.shift C
    let E' := Syn.shift E
    let M' := Syn.shift M
    let i : PTm (n+1) := var 0
    let grid := GaussianCompactRiemannName.grid i N' a' C' E'
    have e := (sample_body_at (Γ := lt i N' :: Γ.map Fm.shift) scaledF i p' N' a' C' E' M').eqTrans
      ((scaled_at p' grid M').eqTrans (qmul_congr (.eqRefl _)
        (sample_body_at halfEvaluator i p' N' a' C' E' zero).eqSymm))
    simpa only [termsEqual,f,x,y,r,p',N',a',C',E',M',i,Syn.shift,GaussianCompactRiemannName.subst_sampleData,
      GaussianDominantPairAlgebra.subst_radiusPoint,subst_pairT,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
      e.eqTrans (multiply_body_at g (radiusPoint M' one) i (sampleData p' N' a' C' E' zero)).eqSymm
  have sumEq := (GaussianRationalFiniteSum.sum_congr_bounded f (multiplyBody g) N x (pairT r y) rows).eqTrans
    (GaussianRationalFiniteSum.sum_multiply g r N y)
  exact (qmul_congr (.eqRefl w) sumEq).eqTrans
    ((GaussianReciprocalHorner.qmul_associative w r S).eqSymm.eqTrans
      ((qmul_congr (GaussianRationalPowerAlgebra.qmul_commutative w r) (.eqRefl S)).eqTrans
        (GaussianReciprocalHorner.qmul_associative r w S)))

theorem original_grid_bound_from_half (p N a C E z R B U V : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hE : Γ ⊢[PRAAx] le one E) (hea : Γ ⊢[PRAAx] le E a) (h : Γ ⊢[PRAAx] source z R B)
    (hV : Γ ⊢[PRAAx] le one V)
    (hHalf : Γ ⊢[PRAAx] bounded (quadrature halfEvaluator p N a C E zero) U V) :
    Γ ⊢[PRAAx] bounded (quadrature evaluatorF p N a C E (fixedData z B))
      ((C*budget R)*V+(majorant R*U)*(E*unit p)) ((E*unit p)*V) := by
  let x := fixedData z B
  let X := sampleData p N a C E x
  let Y := sampleData p N a C E R
  let M := majorant R
  let Z := sampleData p N a C E M
  have hm : Γ ⊢[PRAAx] termsMajorized (sampleBody evaluatorF) scalarBody N X Y := by
    refine .allI (.impI ?_)
    have n' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hN.shift
    have e' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift E) := by simpa [Fm.shift,Syn.shift] using hE.shift
    have ea' : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift E) (Syn.shift a) := by simpa [Fm.shift,Syn.shift] using hea.shift
    have h' : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) := by
      simpa [Fm.shift,Syn.shift,source] using h.shift
    simpa only [termsMajorized,X,Y,x,Syn.shift,GaussianCompactRiemannName.subst_sampleData,GaussianEulerIntegrandName.subst_fixedData] using
      majorized_row (var 0) (Syn.shift p) (Syn.shift N) (Syn.shift a) (Syn.shift C) (Syn.shift E)
        (Syn.shift z) (Syn.shift R) (Syn.shift B) n'.wk e'.wk ea'.wk h'.wk
  have er : Γ ⊢[PRAAx] termsDistance (embedBody scalarBody) (sampleBody scaledF) N Y Z (budget R) (unit p) := by
    refine .allI (.impI ?_)
    have n' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hN.shift
    have e' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift E) := by simpa [Fm.shift,Syn.shift] using hE.shift
    simpa only [termsDistance,Y,Z,M,Syn.shift,GaussianCompactRiemannName.subst_sampleData,
      GaussianEulerWeightedHalfDecay.subst_majorant,GaussianEulerUpperTailScalar.subst_budget,GaussianCoefficientNameBounds.subst_unit] using
      reference_row (var 0) (Syn.shift p) (Syn.shift N) (Syn.shift a) (Syn.shift C) (Syn.shift E)
        (Syn.shift R) n'.wk e'.wk
  have ref : Γ ⊢[PRAAx] bounded (quadrature scaledF p N a C E M) (M*U) V :=
    GaussianRationalReciprocal.bound_congr (scaled_quadrature p N a C E M).eqSymm (.eqRefl _) (one_mul V)
      (GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ (le_refl one) hV (radius_bounded M one (le_refl one)) hHalf)
  exact GaussianCompactScalarMajorant.compact_majorant_bound evaluatorF scaledF scalarBody
    p p N a C E x Y M (budget R) (unit p) (M*U) V hN hE (unit_positive p) hV hm er ref

open GaussianGammaIntegralCutoffs (height top)
open GaussianEulerHalfDecayTailBound (tailNumerator tailDenominator)

theorem original_upper_cutoff_bound (p q N k A C E z R B : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hC : Γ ⊢[PRAAx] le one C) (hE : Γ ⊢[PRAAx] le one E)
    (hstep : Γ ⊢[PRAAx] le C ((two*E)*N)) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] bounded (quadrature evaluatorF p N (top k A R*E) C E (fixedData z B))
      ((C*budget R)*tailDenominator p q N (height k A R) E+
        (majorant R*tailNumerator p q N (height k A R) C E)*(E*unit p))
      ((E*unit p)*tailDenominator p q N (height k A R) E) := by
  have den : Γ ⊢[PRAAx] le one (tailDenominator p q N (height k A R) E) :=
    positive_product _ _ (positive_product _ _ (positive_product _ _ (positive_product _ _
      (positive_product _ _ (positive_product _ _ (le_succ_self one) hE) hE) hN)
      (unit_positive p)) (unit_positive q)) (unit_positive _)
  have start : Γ ⊢[PRAAx] le E (top k A R*E) :=
    le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right E (GaussianGammaIntegralCutoffs.top_positive k A R))
  exact original_grid_bound_from_half p N _ C E z R B _ _ hN hE start h den
    (GaussianEulerHalfDecayTailBound.actual_cutoff_half_decay_bound p q N k A R C E zero hN hC hE hstep)

theorem original_Euler_compact_upper_cutoff_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (((le one (var 2) ⋏ le one (var 5)) ⋏ le one (var 6)) ⟶
      le (var 5) ((two*var 6)*var 2) ⟶ source (var 7) (var 8) (var 9) ⟶
      bounded (quadrature evaluatorF (var 0) (var 2) (top (var 3) (var 4) (var 8)*var 6)
        (var 5) (var 6) (fixedData (var 7) (var 9)))
        ((var 5*budget (var 8))*tailDenominator (var 0) (var 1) (var 2) (height (var 3) (var 4) (var 8)) (var 6)+
          (majorant (var 8)*tailNumerator (var 0) (var 1) (var 2) (height (var 3) (var 4) (var 8)) (var 5) (var 6))*
            (var 6*unit (var 0)))
        ((var 6*unit (var 0))*tailDenominator (var 0) (var 1) (var 2) (height (var 3) (var 4) (var 8)) (var 6))) :=
  closeUniv 10 (.impI (.impI (.impI (original_upper_cutoff_bound _ _ _ _ _ _ _ _ _ _
    hyp2.andE₁.andE₁ hyp2.andE₁.andE₂ hyp2.andE₂ Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianEulerCompactUpperTail

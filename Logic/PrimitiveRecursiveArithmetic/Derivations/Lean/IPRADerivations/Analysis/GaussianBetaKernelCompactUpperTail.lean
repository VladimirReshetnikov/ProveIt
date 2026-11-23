import IPRADerivations.Analysis.GaussianBetaKernelUpperTail
import IPRADerivations.Analysis.GaussianEulerCompactUpperTail

/-!
# Finite upper-tail quadrature for the literal beta kernel

The original beta replacement evaluator, mesh and weight are preserved.
The two interval endpoint guards derive every actual row's upper-time
and beta-domain guards. Actual scalar majorants are summed and compared
with the independently checked original half-decay quadrature. No kernel
approximation or final quadrature norm is supplied as a premise.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaKernelCompactUpperTail

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerUpperPowerCoefficients (source)
open GaussianBetaKernelGridComparison (evaluatorF sampleDataBeta row_at)
open GaussianBetaKernelUpperTail (scalarMajorant referenceBudget)
open GaussianEulerWeightedHalfDecay (majorant)
open GaussianEulerCompactUpperTail (halfEvaluator scaledF scaled_at scaled_quadrature)
open GaussianCompactRiemannName (sampleBody sampleData sample_body_at quadrature
  field0 field1 field2 field3 field4 field5 field0_at field1_at field2_at field3_at field4_at field5_at)
open GaussianRationalSumMajorant (majorized termsMajorized majorized_congr)
open GaussianRationalRiemannRefinement (termsDistance)
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

def scalarBody : PTm 2 := scalarMajorant (field0 (var 1)) (field5 (var 1))
  (field2 (var 1)*field1 (var 1)+field3 (var 1)*var 0) (field4 (var 1)*field1 (var 1))

theorem scalar_body_at (i p M a C E R : PTm n) : Γ ⊢[PRAAx]
    inst2 scalarBody i (sampleData p M a C E R) ≐ scalarMajorant p R (a*M+C*i) (E*M) := by
  let x := sampleData p M a C E R
  have num := congrAdd (congrMul (field2_at p M a C E R) (field1_at p M a C E R))
    (congrMul (field3_at p M a C E R) (Prf.eqRefl (Γ := Γ) i))
  have den := congrMul (field4_at (Γ := Γ) p M a C E R) (field1_at p M a C E R)
  simpa [scalarBody,inst2,x] using Prf.eqCongr (Γ := Γ) (Ax := PRAAx)
    (scalarMajorant (var 0) (var 1) (var 2) (var 3) : PTm 4)
    (σ := ![field0 x,field5 x,field2 x*field1 x+field3 x*i,field4 x*field1 x])
    (σ' := ![p,R,a*M+C*i,E*M])
    (fun k => by fin_cases k; exact field0_at p M a C E R; exact field5_at p M a C E R; exact num; exact den)

theorem majorized_row (i p M a C E z R B N : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (hE : Γ ⊢[PRAAx] le one E) (hea : Γ ⊢[PRAAx] le E a) (h : Γ ⊢[PRAAx] source z R B)
    (hN : Γ ⊢[PRAAx] le one N) (hRight : Γ ⊢[PRAAx] le (a+C) (E*N)) (hi : Γ ⊢[PRAAx] lt i M) :
    Γ ⊢[PRAAx] majorized
      (inst2 (sampleBody evaluatorF) i (sampleData p M a C E (sampleDataBeta z B N)))
      (inst2 scalarBody i (sampleData p M a C E R)) := by
  let u := a*M+C*i
  let v := E*M
  have hv : Γ ⊢[PRAAx] le one v := positive_product _ _ hE hM
  have hle : Γ ⊢[PRAAx] le v u := le_trans (mul_le_mul_right M hea) (le_add_right _ _)
  have hs : Γ ⊢[PRAAx] GaussianEulerUpperPowerOrder.source z R B u v :=
    .andI h (.andI (.andI (le_trans hv hle) hv) hle)
  have within : Γ ⊢[PRAAx] le u (v*N) :=
    le_trans (add_le_add₂ (le_refl (a*M)) (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl C) (le_of_lt hi)))
      (le_congr (by ipra_ring) (by dsimp only [v]; ipra_ring) (mul_le_mul_right M hRight))
  have point := (sample_body_at (Γ := Γ) evaluatorF i p M a C E (sampleDataBeta z B N)).eqTrans
    (row_at p z B u v N)
  exact majorized_congr point.eqSymm (scalar_body_at i p M a C E R).eqSymm
    (GaussianBetaKernelUpperTail.original_beta_cell_majorized p z R B u v N hs hN within)

theorem reference_row (i p M a C E R : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (hE : Γ ⊢[PRAAx] le one E) : Γ ⊢[PRAAx] distanceBounded
    (inst2 (embedBody scalarBody) i (sampleData p M a C E R))
    (inst2 (sampleBody scaledF) i (sampleData p M a C E (majorant R))) (referenceBudget R) (unit p) := by
  let u := a*M+C*i
  let v := E*M
  let K := majorant R
  have hv : Γ ⊢[PRAAx] le one v := positive_product _ _ hE hM
  have left : Γ ⊢[PRAAx] inst2 (embedBody scalarBody) i (sampleData p M a C E R) ≐ embed (scalarMajorant p R u v) := by
    simpa only [inst2,embedBody,RationalGaussianEmbedding.subst_embed] using
      RationalGaussianRealPart.embed_congr (scalar_body_at (Γ := Γ) i p M a C E R)
  have right := (sample_body_at (Γ := Γ) scaledF i p M a C E K).eqTrans
    ((scaled_at p (pairT u v) K).eqTrans (qmul_congr (.eqRefl _)
      (GaussianEulerHalfDecayReference.actual_half_evaluator p u v zero)))
  exact distance_congr left.eqSymm right.eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianBetaKernelUpperTail.scalar_majorant_reference_error p R u v hv)

theorem original_grid_bound_from_half (p M a C E z R B N U V : PTm n)
    (hM : Γ ⊢[PRAAx] le one M) (hE : Γ ⊢[PRAAx] le one E) (hea : Γ ⊢[PRAAx] le E a)
    (h : Γ ⊢[PRAAx] source z R B) (hN : Γ ⊢[PRAAx] le one N) (hRight : Γ ⊢[PRAAx] le (a+C) (E*N))
    (hV : Γ ⊢[PRAAx] le one V) (hHalf : Γ ⊢[PRAAx] bounded (quadrature halfEvaluator p M a C E zero) U V) :
    Γ ⊢[PRAAx] bounded (quadrature evaluatorF p M a C E (sampleDataBeta z B N))
      ((C*referenceBudget R)*V+(majorant R*U)*(E*unit p)) ((E*unit p)*V) := by
  let x := sampleDataBeta z B N
  let X := sampleData p M a C E x
  let Y := sampleData p M a C E R
  let K := majorant R
  let Z := sampleData p M a C E K
  have hm : Γ ⊢[PRAAx] termsMajorized (sampleBody evaluatorF) scalarBody M X Y := by
    have m' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift M) := by simpa [Fm.shift,Syn.shift] using hM.shift
    have e' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift E) := by simpa [Fm.shift,Syn.shift] using hE.shift
    have ea' : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift E) (Syn.shift a) := by simpa [Fm.shift,Syn.shift] using hea.shift
    have h' : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using h.shift
    have n' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hN.shift
    have r' : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift a+Syn.shift C) (Syn.shift E*Syn.shift N) :=
      by simpa [Fm.shift,Syn.shift] using hRight.shift
    refine .allI (.impI ?_)
    simpa only [termsMajorized,X,Y,x,Syn.shift,GaussianCompactRiemannName.subst_sampleData,
      GaussianBetaKernelGridComparison.subst_sampleDataBeta] using
      majorized_row (var 0) (Syn.shift p) (Syn.shift M) (Syn.shift a) (Syn.shift C) (Syn.shift E)
        (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift N) m'.wk e'.wk ea'.wk h'.wk n'.wk r'.wk Prf.hyp0
  have er : Γ ⊢[PRAAx] termsDistance (embedBody scalarBody) (sampleBody scaledF) M Y Z (referenceBudget R) (unit p) := by
    have m' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift M) := by simpa [Fm.shift,Syn.shift] using hM.shift
    have e' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift E) := by simpa [Fm.shift,Syn.shift] using hE.shift
    refine .allI (.impI ?_)
    simpa only [termsDistance,Y,Z,K,Syn.shift,GaussianCompactRiemannName.subst_sampleData,
      GaussianEulerWeightedHalfDecay.subst_majorant,GaussianBetaKernelUpperTail.subst_referenceBudget,
      GaussianCoefficientNameBounds.subst_unit] using
      reference_row (var 0) (Syn.shift p) (Syn.shift M) (Syn.shift a) (Syn.shift C) (Syn.shift E)
        (Syn.shift R) m'.wk e'.wk
  have ref : Γ ⊢[PRAAx] bounded (quadrature scaledF p M a C E K) (K*U) V :=
    GaussianRationalReciprocal.bound_congr (scaled_quadrature p M a C E K).eqSymm (.eqRefl _) (one_mul V)
      (GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ (le_refl one) hV (radius_bounded K one (le_refl one)) hHalf)
  exact GaussianCompactScalarMajorant.compact_majorant_bound evaluatorF scaledF scalarBody p p M a C E x Y K
    (referenceBudget R) (unit p) (K*U) V hM hE (unit_positive p) hV hm er ref

open GaussianGammaIntegralCutoffs (height top)
open GaussianEulerHalfDecayTailBound (tailNumerator tailDenominator)

theorem original_upper_cutoff_bound (p q M k A C E z R B N : PTm n)
    (hM : Γ ⊢[PRAAx] le one M) (hC : Γ ⊢[PRAAx] le one C) (hE : Γ ⊢[PRAAx] le one E)
    (hstep : Γ ⊢[PRAAx] le C ((two*E)*M)) (h : Γ ⊢[PRAAx] source z R B)
    (hN : Γ ⊢[PRAAx] le one N) (hRight : Γ ⊢[PRAAx] le (top k A R*E+C) (E*N)) :
    Γ ⊢[PRAAx] bounded (quadrature evaluatorF p M (top k A R*E) C E (sampleDataBeta z B N))
      ((C*referenceBudget R)*tailDenominator p q M (height k A R) E+
        (majorant R*tailNumerator p q M (height k A R) C E)*(E*unit p))
      ((E*unit p)*tailDenominator p q M (height k A R) E) := by
  have den : Γ ⊢[PRAAx] le one (tailDenominator p q M (height k A R) E) :=
    positive_product _ _ (positive_product _ _ (positive_product _ _ (positive_product _ _
      (positive_product _ _ (positive_product _ _ (le_succ_self one) hE) hE) hM)
      (unit_positive p)) (unit_positive q)) (unit_positive _)
  have start : Γ ⊢[PRAAx] le E (top k A R*E) :=
    le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right E (GaussianGammaIntegralCutoffs.top_positive k A R))
  exact original_grid_bound_from_half p M _ C E z R B N _ _ hM hE start h hN hRight den
    (GaussianEulerHalfDecayTailBound.actual_cutoff_half_decay_bound p q M k A R C E zero hM hC hE hstep)

theorem original_beta_grid_bound_from_half_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
    ((le one (var 1) ⋏ le one (var 4) ⋏ le (var 4) (var 2)) ⟶
      source (var 5) (var 6) (var 7) ⟶
      (le one (var 8) ⋏ le (var 2+var 3) (var 4*var 8)) ⟶
      (le one (var 10) ⋏ bounded (quadrature halfEvaluator (var 0) (var 1) (var 2) (var 3) (var 4) zero) (var 9) (var 10)) ⟶
      bounded (quadrature evaluatorF (var 0) (var 1) (var 2) (var 3) (var 4) (sampleDataBeta (var 5) (var 7) (var 8)))
        ((var 3*referenceBudget (var 6))*var 10+(majorant (var 6)*var 9)*(var 4*unit (var 0)))
        ((var 4*unit (var 0))*var 10)) :=
  closeUniv 11 (.impI (.impI (.impI (.impI (original_grid_bound_from_half _ _ _ _ _ _ _ _ _ _ _
    hyp2.wk.andE₁ hyp2.wk.andE₂.andE₁ hyp2.wk.andE₂.andE₂ hyp2 Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0.andE₁ Prf.hyp0.andE₂)))))

theorem original_beta_compact_upper_cutoff_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
    ((le one (var 2) ⋏ le one (var 5) ⋏ le one (var 6)) ⟶
      le (var 5) ((two*var 6)*var 2) ⟶ source (var 7) (var 8) (var 9) ⟶
      (le one (var 10) ⋏ le (top (var 3) (var 4) (var 8)*var 6+var 5) (var 6*var 10)) ⟶
      bounded (quadrature evaluatorF (var 0) (var 2) (top (var 3) (var 4) (var 8)*var 6)
        (var 5) (var 6) (sampleDataBeta (var 7) (var 9) (var 10)))
        ((var 5*referenceBudget (var 8))*tailDenominator (var 0) (var 1) (var 2) (height (var 3) (var 4) (var 8)) (var 6)+
          (majorant (var 8)*tailNumerator (var 0) (var 1) (var 2) (height (var 3) (var 4) (var 8)) (var 5) (var 6))*(var 6*unit (var 0)))
        ((var 6*unit (var 0))*tailDenominator (var 0) (var 1) (var 2) (height (var 3) (var 4) (var 8)) (var 6))) :=
  closeUniv 11 (.impI (.impI (.impI (.impI (original_upper_cutoff_bound _ _ _ _ _ _ _ _ _ _ _
    hyp2.wk.andE₁ hyp2.wk.andE₂.andE₁ hyp2.wk.andE₂.andE₂ hyp2 Prf.hyp1 Prf.hyp0.andE₁ Prf.hyp0.andE₂)))))

end LeanProofs.IPRA.Analysis.GaussianBetaKernelCompactUpperTail

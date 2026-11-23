import IPRADerivations.Analysis.GaussianBetaRowMonomialReference
import IPRADerivations.Analysis.GaussianRationalQuadratureDifference

/-!
# Original beta/Euler upper grids transferred to the literal monomial grid

The two original quadratures may have independent observation queries.
Their literal row differences are majorized by the actual scalar radii.
Those radii are compared with the same-grid original monomial-decay
quadrature, scaled by the genuine reciprocal beta degree 1/N.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaUpperGridMonomialComparison

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBetaRowMonomialReference (scalarMajorant scaledMonomial comparisonNumerator comparisonDenominator)
open GaussianCompactRiemannName (sampleBody sampleData sample_body_at quadrature field0 field1 field2 field3 field4 field5
  field0_at field1_at field2_at field3_at field4_at field5_at)
open GaussianRationalFiniteSum (sum termsEqual multiplyBody multiply_body_at)
open GaussianRationalRiemannRefinement (weight leftSum termsDistance)
open GaussianRationalQuadratureDifference (differenceBody difference_body_at weighted_difference)
open GaussianRationalSumMajorant (majorized termsMajorized majorized_congr)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr)
open GaussianDominantPairAlgebra (radiusPoint radius_bounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (z R B a C E T N M : PTm n) : Fm PTm n :=
  GaussianEulerUpperPowerCoefficients.source z R B ⋏ (le one E ⋏ (le one M ⋏ (le E a ⋏
    (le (a+C) (E*T) ⋏ (le one N ⋏ le (two*(a+C)) (E*N))))))

def majorantData (v q R N : PTm n) : PTm n := pairT v (pairT q (pairT R N))
@[simp] theorem subst_majorantData {m : ℕ} (σ : Fin n → PTm m) (v q R N : PTm n) :
    Syn.subst σ (majorantData v q R N) = majorantData (Syn.subst σ v) (Syn.subst σ q) (Syn.subst σ R) (Syn.subst σ N) := by simp [majorantData]

def scalarBody : PTm 2 := scalarMajorant (field0 (var 1)) (fstT (field5 (var 1))) (fstT (sndT (field5 (var 1))))
  (fstT (sndT (sndT (field5 (var 1))))) (field2 (var 1)*field1 (var 1)+field3 (var 1)*var 0)
  (field4 (var 1)*field1 (var 1)) (sndT (sndT (sndT (field5 (var 1)))))

theorem scalar_body_at (i p v q M a C E R N : PTm n) : Γ ⊢[PRAAx]
    inst2 scalarBody i (sampleData p M a C E (majorantData v q R N)) ≐
      scalarMajorant p v q R (a*M+C*i) (E*M) N := by
  let x := sampleData p M a C E (majorantData v q R N)
  have dataRead := field5_at (Γ := Γ) p M a C E (majorantData v q R N)
  have e0 := (congrFst dataRead).eqTrans (fst_pair v (pairT q (pairT R N)))
  have e1 := (congrFst (congrSnd dataRead)).eqTrans ((congrFst (snd_pair v (pairT q (pairT R N)))).eqTrans (fst_pair q (pairT R N)))
  have e2 := (congrFst (congrSnd (congrSnd dataRead))).eqTrans
    ((congrFst (congrSnd (snd_pair v (pairT q (pairT R N))))).eqTrans ((congrFst (snd_pair q (pairT R N))).eqTrans (fst_pair R N)))
  have e3 := (congrSnd (congrSnd (congrSnd dataRead))).eqTrans
    ((congrSnd (congrSnd (snd_pair v (pairT q (pairT R N))))).eqTrans ((congrSnd (snd_pair q (pairT R N))).eqTrans (snd_pair R N)))
  have atTime : Γ ⊢[PRAAx] field2 x*field1 x+field3 x*i ≐ a*M+C*i :=
    congrAdd (congrMul (field2_at p M a C E (majorantData v q R N)) (field1_at p M a C E (majorantData v q R N)))
      (congrMul (field3_at p M a C E (majorantData v q R N)) (.eqRefl i))
  have atDen : Γ ⊢[PRAAx] field4 x*field1 x ≐ E*M :=
    congrMul (field4_at p M a C E (majorantData v q R N)) (field1_at p M a C E (majorantData v q R N))
  have in5 : ![field0 x,fstT (field5 x),fstT (sndT (field5 x)),fstT (sndT (sndT (field5 x))),field2 x*field1 x+field3 x*i,field4 x*field1 x,sndT (sndT (sndT (field5 x)))] (5 : Fin 7) = field4 x*field1 x := rfl
  have in6 : ![field0 x,fstT (field5 x),fstT (sndT (field5 x)),fstT (sndT (sndT (field5 x))),field2 x*field1 x+field3 x*i,field4 x*field1 x,sndT (sndT (sndT (field5 x)))] (6 : Fin 7) = sndT (sndT (sndT (field5 x))) := rfl
  have out5 : ![p,v,q,R,a*M+C*i,E*M,N] (5 : Fin 7) = E*M := rfl
  have out6 : ![p,v,q,R,a*M+C*i,E*M,N] (6 : Fin 7) = N := rfl
  simpa only [scalarBody,inst2,x,GaussianBetaRowMonomialReference.subst_scalarMajorant,
    GaussianCompactRiemannName.subst_field0,GaussianCompactRiemannName.subst_field1,GaussianCompactRiemannName.subst_field2,
    GaussianCompactRiemannName.subst_field3,GaussianCompactRiemannName.subst_field4,GaussianCompactRiemannName.subst_field5,
    subst_fstT,subst_sndT,PTm.subst_add,PTm.subst_mul,in5,in6,out5,out6,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (scalarMajorant (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) : PTm 7)
      (σ := ![field0 x,fstT (field5 x),fstT (sndT (field5 x)),fstT (sndT (sndT (field5 x))),field2 x*field1 x+field3 x*i,field4 x*field1 x,sndT (sndT (sndT (field5 x)))])
      (σ' := ![p,v,q,R,a*M+C*i,E*M,N])
      (fun j => by fin_cases j; exact field0_at p M a C E _; exact e0; exact e1; exact e2; exact atTime; exact atDen; exact e3)

def scaledEval (r t x : PTm n) : PTm n := scaledMonomial r (fstT x) (fstT t) (sndT t) (sndT x)
def scaledF : PR 3 := PTm.toPR (scaledEval (var 0) (var 1) (var 2))
@[simp] theorem subst_scaledEval {m : ℕ} (σ : Fin n → PTm m) (r t x : PTm n) :
    Syn.subst σ (scaledEval r t x) = scaledEval (Syn.subst σ r) (Syn.subst σ t) (Syn.subst σ x) := by simp [scaledEval]

theorem scaled_at (r t d N : PTm n) : Γ ⊢[PRAAx]
    ap3 scaledF r t (pairT d N) ≐ qmul (radiusPoint one N) (ap3 GaussianMonomialDecayQuadrature.evaluatorF r t d) := by
  have raw : Γ ⊢[PRAAx] ap3 scaledF r t (pairT d N) ≐ scaledEval r t (pairT d N) := by
    simpa [scaledF,ap3] using toPR_eq (Γ := Γ) (scaledEval (var 0) (var 1) (var 2) : PTm 3) ![r,t,pairT d N]
  have read : Γ ⊢[PRAAx] scaledEval r t (pairT d N) ≐ scaledMonomial r d (fstT t) (sndT t) N := by
    simpa only [scaledEval,GaussianBetaRowMonomialReference.subst_scaledMonomial,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons] using
      Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (scaledMonomial (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
        (σ := ![r,fstT (pairT d N),fstT t,sndT t,sndT (pairT d N)]) (σ' := ![r,d,fstT t,sndT t,N])
        (fun i => by fin_cases i; exact .eqRefl _; exact fst_pair d N; exact .eqRefl _; exact .eqRefl _; exact snd_pair d N)
  have eta : Γ ⊢[PRAAx] ap3 GaussianMonomialDecayQuadrature.evaluatorF r t d ≐ GaussianMonomialDecayMajorant.sample r d (fstT t) (sndT t) :=
    by simpa [GaussianMonomialDecayQuadrature.evaluatorF,ap3,GaussianMonomialDecayQuadrature.evaluator] using
      toPR_eq (Γ := Γ) (GaussianMonomialDecayQuadrature.evaluator (var 0) (var 1) (var 2) : PTm 3) ![r,t,d]
  exact raw.eqTrans (read.eqTrans (qmul_congr (.eqRefl _) eta.eqSymm))

theorem scaled_quadrature (r M a C E d N : PTm n) : Γ ⊢[PRAAx]
    quadrature scaledF r M a C E (pairT d N) ≐
      qmul (radiusPoint one N) (quadrature GaussianMonomialDecayQuadrature.evaluatorF r M a C E d) := by
  let f := sampleBody scaledF
  let g := sampleBody GaussianMonomialDecayQuadrature.evaluatorF
  let x := sampleData r M a C E (pairT d N)
  let y := sampleData r M a C E d
  let c := radiusPoint one N
  let w := weight C E M
  let S := sum g M y
  have rows : Γ ⊢[PRAAx] termsEqual f (multiplyBody g) M x (pairT c y) := by
    refine .allI (.impI ?_)
    let i : PTm (n+1) := var 0
    let grid := GaussianCompactRiemannName.grid i (Syn.shift M) (Syn.shift a) (Syn.shift C) (Syn.shift E)
    have e := (sample_body_at (Γ := lt i (Syn.shift M) :: Γ.map Fm.shift) scaledF i (Syn.shift r) (Syn.shift M) (Syn.shift a) (Syn.shift C) (Syn.shift E) (pairT (Syn.shift d) (Syn.shift N))).eqTrans
      ((scaled_at (Syn.shift r) grid (Syn.shift d) (Syn.shift N)).eqTrans (qmul_congr (.eqRefl _)
        (sample_body_at GaussianMonomialDecayQuadrature.evaluatorF i (Syn.shift r) (Syn.shift M) (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift d)).eqSymm))
    simpa only [termsEqual,f,x,y,c,i,Syn.shift,GaussianCompactRiemannName.subst_sampleData,
      GaussianDominantPairAlgebra.subst_radiusPoint,subst_pairT,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
      e.eqTrans (multiply_body_at g (radiusPoint one (Syn.shift N)) i (sampleData (Syn.shift r) (Syn.shift M) (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift d))).eqSymm
  have sumEq := (GaussianRationalFiniteSum.sum_congr_bounded f (multiplyBody g) M x (pairT c y) rows).eqTrans
    (GaussianRationalFiniteSum.sum_multiply g c M y)
  exact (qmul_congr (.eqRefl w) sumEq).eqTrans
    ((GaussianReciprocalHorner.qmul_associative w c S).eqSymm.eqTrans
      ((qmul_congr (GaussianRationalPowerAlgebra.qmul_commutative w c) (.eqRefl S)).eqTrans
        (GaussianReciprocalHorner.qmul_associative c w S)))

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (z R B a C E T N M : PTm n) :
    (source z R B a C E T N M).subst σ = source (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ a)
      (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ N) (Syn.subst σ M) := by
  simp [source,GaussianEulerUpperPowerCoefficients.source,ComplexLogarithmRemainder.bounded]

theorem grid_guards (i z R B a C E T N M : PTm n) (hi : Γ ⊢[PRAAx] lt i M)
    (h : Γ ⊢[PRAAx] source z R B a C E T N M) : Γ ⊢[PRAAx]
    GaussianBetaUpperRowDampedError.source z R B (a*M+C*i) (E*M) N ⋏ le (a*M+C*i) (T*(E*M)) := by
  have he := h.andE₂.andE₁
  have hm := h.andE₂.andE₂.andE₁
  have ha := h.andE₂.andE₂.andE₂.andE₁
  have ht := h.andE₂.andE₂.andE₂.andE₂.andE₁
  have hn := h.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁
  have htn := h.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂
  have den := positive_product E M he hm
  have high : Γ ⊢[PRAAx] le (E*M) (a*M+C*i) := le_trans (mul_le_mul_right M ha) (le_add_right _ _)
  have time := le_trans den high
  have first : Γ ⊢[PRAAx] le (a*M+C*i) ((a+C)*M) :=
    le_congr (by ipra_ring) (by ipra_ring) (add_le_add_right (a*M) (mul_le_mul_right C (le_of_lt hi)))
  have last : Γ ⊢[PRAAx] le (a*M+C*i) (T*(E*M)) :=
    le_trans first (le_congr (.eqRefl _) (by ipra_ring) (mul_le_mul_right M ht))
  have small : Γ ⊢[PRAAx] le (two*(a*M+C*i)) ((E*M)*N) :=
    le_trans (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl two) first)
      (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right M htn))
  exact .andI (.andI (.andI h.andE₁ (.andI (.andI time den) high)) (.andI den (.andI hn small))) last

theorem rows_majorized (p v q z R B a C E T N M : PTm n)
    (h : Γ ⊢[PRAAx] source z R B a C E T N M) : Γ ⊢[PRAAx]
    termsMajorized (differenceBody (sampleBody GaussianBetaKernelGridComparison.evaluatorF) (sampleBody GaussianEulerIntegrandName.evaluatorF))
      scalarBody M
      (pairT (sampleData p M a C E (GaussianBetaKernelGridComparison.sampleDataBeta z B N))
        (sampleData v M a C E (GaussianEulerIntegrandName.fixedData z B)))
      (sampleData p M a C E (majorantData v q R N)) := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift M) :: Γ.map Fm.shift
  let i : PTm (n+1) := var 0
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift a) (Syn.shift C)
      (Syn.shift E) (Syn.shift T) (Syn.shift N) (Syn.shift M) := by simpa [Fm.shift,Syn.shift] using h.shift
  have guard := grid_guards (Γ := Δ) i _ _ _ _ _ _ _ _ _ Prf.hyp0 hs.wk
  have left := (sample_body_at (Γ := Δ) GaussianBetaKernelGridComparison.evaluatorF i (Syn.shift p) (Syn.shift M) (Syn.shift a) (Syn.shift C) (Syn.shift E)
    (GaussianBetaKernelGridComparison.sampleDataBeta (Syn.shift z) (Syn.shift B) (Syn.shift N))).eqTrans
      (GaussianBetaKernelGridComparison.row_at (Syn.shift p) (Syn.shift z) (Syn.shift B)
        (Syn.shift a*Syn.shift M+Syn.shift C*i) (Syn.shift E*Syn.shift M) (Syn.shift N))
  have right : Δ ⊢[PRAAx] inst2 (sampleBody GaussianEulerIntegrandName.evaluatorF) i
      (sampleData (Syn.shift v) (Syn.shift M) (Syn.shift a) (Syn.shift C) (Syn.shift E) (GaussianEulerIntegrandName.fixedData (Syn.shift z) (Syn.shift B))) ≐
      GaussianEulerIntegrandName.sample (Syn.shift v) (Syn.shift z) (Syn.shift B)
        (Syn.shift a*Syn.shift M+Syn.shift C*i) (Syn.shift E*Syn.shift M) :=
    sample_body_at _ _ _ _ _ _ _ _
  have literal := (difference_body_at _ _ i _ _).eqTrans (qsub_congr left right)
  have scalar := scalar_body_at (Γ := Δ) i (Syn.shift p) (Syn.shift v) (Syn.shift q) (Syn.shift M) (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift R) (Syn.shift N)
  have actual := GaussianBetaRowMonomialReference.row_majorized (Syn.shift p) (Syn.shift v) (Syn.shift q) (Syn.shift z) (Syn.shift R) (Syn.shift B)
    (Syn.shift a*Syn.shift M+Syn.shift C*i) (Syn.shift E*Syn.shift M) (Syn.shift N) guard.andE₁
  simpa only [termsMajorized,Δ,i,Syn.shift,subst_pairT,GaussianCompactRiemannName.subst_sampleData,
    GaussianBetaKernelGridComparison.subst_sampleDataBeta,GaussianEulerIntegrandName.subst_fixedData,subst_majorantData] using
    majorized_congr literal.eqSymm scalar.eqSymm actual

theorem reference_rows (p v q r z R B a C E T N M : PTm n)
    (h : Γ ⊢[PRAAx] source z R B a C E T N M) : Γ ⊢[PRAAx]
    termsDistance (RationalGaussianRealPart.embedBody scalarBody) (sampleBody scaledF) M
      (sampleData p M a C E (majorantData v q R N)) (sampleData r M a C E (pairT (R+two) N))
      (comparisonNumerator p v q r (R+two) T N) (comparisonDenominator p v q r N) := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift M) :: Γ.map Fm.shift
  let i : PTm (n+1) := var 0
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift a) (Syn.shift C)
      (Syn.shift E) (Syn.shift T) (Syn.shift N) (Syn.shift M) := by simpa [Fm.shift,Syn.shift] using h.shift
  have guard := grid_guards (Γ := Δ) i _ _ _ _ _ _ _ _ _ Prf.hyp0 hs.wk
  have den := guard.andE₁.andE₂.andE₁
  have degree := guard.andE₁.andE₂.andE₂.andE₁
  have scalar := scalar_body_at (Γ := Δ) i (Syn.shift p) (Syn.shift v) (Syn.shift q) (Syn.shift M) (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift R) (Syn.shift N)
  have left := RationalGaussianRealPart.embed_congr scalar
  have right := (sample_body_at (Γ := Δ) scaledF i (Syn.shift r) (Syn.shift M) (Syn.shift a) (Syn.shift C) (Syn.shift E) (pairT (Syn.shift R+two) (Syn.shift N))).eqTrans
    ((scaled_at (Syn.shift r) (GaussianCompactRiemannName.grid i (Syn.shift M) (Syn.shift a) (Syn.shift C) (Syn.shift E)) (Syn.shift R+two) (Syn.shift N)).eqTrans
      (qmul_congr (.eqRefl _) (GaussianMonomialDecayQuadrature.evaluator_at (Syn.shift r)
        (Syn.shift a*Syn.shift M+Syn.shift C*i) (Syn.shift E*Syn.shift M) (Syn.shift R+two))))
  have actual := GaussianBetaRowMonomialReference.original_majorant_monomial_comparison (Syn.shift p) (Syn.shift v) (Syn.shift q) (Syn.shift r) (Syn.shift R)
    (Syn.shift a*Syn.shift M+Syn.shift C*i) (Syn.shift E*Syn.shift M) (Syn.shift N) (Syn.shift T) den degree guard.andE₂
  simpa only [termsDistance,Δ,i,Syn.shift,GaussianCompactRiemannName.subst_sampleData,subst_majorantData,subst_pairT,
    PTm.subst_add,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,
    GaussianBetaRowMonomialReference.subst_comparisonNumerator,GaussianBetaRowMonomialReference.subst_comparisonDenominator,
    RationalGaussianRealPart.embedBody,inst2,RationalGaussianEmbedding.subst_embed] using
    distance_congr left.eqSymm right.eqSymm (.eqRefl _) (.eqRefl _) actual

theorem original_grid_from_monomial_bound (p v q r z R B a C E T N M U V : PTm n)
    (h : Γ ⊢[PRAAx] source z R B a C E T N M) (hV : Γ ⊢[PRAAx] le one V)
    (hMono : Γ ⊢[PRAAx] bounded (quadrature GaussianMonomialDecayQuadrature.evaluatorF r M a C E (R+two)) U V) : Γ ⊢[PRAAx]
    distanceBounded
      (quadrature GaussianBetaKernelGridComparison.evaluatorF p M a C E (GaussianBetaKernelGridComparison.sampleDataBeta z B N))
      (quadrature GaussianEulerIntegrandName.evaluatorF v M a C E (GaussianEulerIntegrandName.fixedData z B))
      ((C*comparisonNumerator p v q r (R+two) T N)*(N*V)+U*(E*comparisonDenominator p v q r N))
      ((E*comparisonDenominator p v q r N)*(N*V)) := by
  let f := sampleBody GaussianBetaKernelGridComparison.evaluatorF
  let g := sampleBody GaussianEulerIntegrandName.evaluatorF
  let X := sampleData p M a C E (GaussianBetaKernelGridComparison.sampleDataBeta z B N)
  let Y := sampleData v M a C E (GaussianEulerIntegrandName.fixedData z B)
  let Z := sampleData p M a C E (majorantData v q R N)
  let W := sampleData r M a C E (pairT (R+two) N)
  let A := comparisonNumerator p v q r (R+two) T N
  let D := comparisonDenominator p v q r N
  have he := h.andE₂.andE₁
  have hm := h.andE₂.andE₂.andE₁
  have hn := h.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁
  have hd : Γ ⊢[PRAAx] le one D := positive_product _ _ (positive_product _ _ (positive_product _ _
    (positive_product _ _ hn (unit_positive q)) (unit_positive r)) (unit_positive p)) (unit_positive v)
  have hnv := positive_product (Γ := Γ) N V hn hV
  have dist := GaussianCompactScalarMajorant.common_mesh_distance (RationalGaussianRealPart.embedBody scalarBody) (sampleBody scaledF)
    M Z W C E A D hm he hd (reference_rows p v q r z R B a C E T N M h)
  have error := distance_congr (GaussianCompactScalarMajorant.scalar_left_embedding scalarBody M Z C E he hm).eqSymm
    (.eqRefl _) (.eqRefl _) (.eqRefl _) dist
  have scaled : Γ ⊢[PRAAx] bounded (quadrature scaledF r M a C E (pairT (R+two) N)) U (N*V) :=
    GaussianRationalReciprocal.bound_congr (scaled_quadrature r M a C E (R+two) N).eqSymm (one_mul _) (.eqRefl _)
      (GaussianRationalReciprocal.bounded_product _ _ one N U V hn hV (radius_bounded one N hn) hMono)
  have norm := GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _ (positive_product _ _ he hd) hnv error scaled
  have major := GaussianCompactScalarMajorant.weighted_majorant (differenceBody f g) scalarBody M (pairT X Y) Z C E hm he
    (rows_majorized p v q z R B a C E T N M h)
  exact GaussianRationalReciprocal.bound_congr (weighted_difference f g M X Y C E).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianRationalSumMajorant.majorant_bound _ _ _ _ (positive_product _ _ (positive_product _ _ he hd) hnv) major norm)

def monomialBoundNumerator (r s R M C E : PTm n) : PTm n :=
  GaussianMonomialDecayQuadrature.cap (R+two)*GaussianMonomialDecayQuadrature.errorDenominator r s M E+
    GaussianMonomialDecayQuadrature.errorNumerator r s M C E (R+two)
def monomialBoundDenominator (r s M E : PTm n) : PTm n := GaussianMonomialDecayQuadrature.errorDenominator r s M E

def numerator (p v q r s R C E T N M : PTm n) : PTm n :=
  (C*comparisonNumerator p v q r (R+two) T N)*(N*monomialBoundDenominator r s M E)+
    monomialBoundNumerator r s R M C E*(E*comparisonDenominator p v q r N)
def denominator (p v q r s E N M : PTm n) : PTm n :=
  (E*comparisonDenominator p v q r N)*(N*monomialBoundDenominator r s M E)

/-- All premises are original input/mesh/cutoff guards. The exact
2^(R+3)*(R+2)! cap comes from the original monomial quadrature. -/
theorem original_upper_grid_monomial_cap (p v q r s z R B C E T N M : PTm n)
    (h : Γ ⊢[PRAAx] source z R B E C E T N M)
    (hC : Γ ⊢[PRAAx] le one C) (hstep : Γ ⊢[PRAAx] le C ((two*E)*M)) : Γ ⊢[PRAAx]
    distanceBounded
      (quadrature GaussianBetaKernelGridComparison.evaluatorF p M E C E (GaussianBetaKernelGridComparison.sampleDataBeta z B N))
      (quadrature GaussianEulerIntegrandName.evaluatorF v M E C E (GaussianEulerIntegrandName.fixedData z B))
      (numerator p v q r s R C E T N M) (denominator p v q r s E N M) := by
  have he := h.andE₂.andE₁
  have hm := h.andE₂.andE₂.andE₁
  have bound := GaussianMonomialDecayQuadrature.original_grid_uniform_bound r s M C E (R+two) hm hC he hstep
  have hd := GaussianEulerHalfDecayLeftNorm.error_denominator_positive r s M E hm he
  exact original_grid_from_monomial_bound p v q r z R B E C E T N M
    (monomialBoundNumerator r s R M C E) (monomialBoundDenominator r s M E) h hd bound

theorem actual_original_upper_shared_grid_monomial_transfer_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 15
      ((source (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) ⋏
        le one (var 14)) ⟶
        bounded (quadrature GaussianMonomialDecayQuadrature.evaluatorF (var 3) (var 12) (var 7) (var 8) (var 9) (var 5+two)) (var 13) (var 14) ⟶
        distanceBounded
          (quadrature GaussianBetaKernelGridComparison.evaluatorF (var 0) (var 12) (var 7) (var 8) (var 9)
            (GaussianBetaKernelGridComparison.sampleDataBeta (var 4) (var 6) (var 11)))
          (quadrature GaussianEulerIntegrandName.evaluatorF (var 1) (var 12) (var 7) (var 8) (var 9) (GaussianEulerIntegrandName.fixedData (var 4) (var 6)))
          (((var 8)*comparisonNumerator (var 0) (var 1) (var 2) (var 3) (var 5+two) (var 10) (var 11))*((var 11)*(var 14))+
            (var 13)*((var 9)*comparisonDenominator (var 0) (var 1) (var 2) (var 3) (var 11)))
          (((var 9)*comparisonDenominator (var 0) (var 1) (var 2) (var 3) (var 11))*((var 11)*(var 14)))) :=
  closeUniv 15 (.impI (.impI (original_grid_from_monomial_bound _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))

theorem original_source_only_upper_beta_Euler_exact_monomial_cap_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 13
      ((source (var 5) (var 6) (var 7) (var 9) (var 8) (var 9) (var 10) (var 11) (var 12) ⋏
        (le one (var 8) ⋏ le (var 8) ((two*var 9)*var 12))) ⟶
        distanceBounded
          (quadrature GaussianBetaKernelGridComparison.evaluatorF (var 0) (var 12) (var 9) (var 8) (var 9)
            (GaussianBetaKernelGridComparison.sampleDataBeta (var 5) (var 7) (var 11)))
          (quadrature GaussianEulerIntegrandName.evaluatorF (var 1) (var 12) (var 9) (var 8) (var 9) (GaussianEulerIntegrandName.fixedData (var 5) (var 7)))
          (numerator (var 0) (var 1) (var 2) (var 3) (var 4) (var 6) (var 8) (var 9) (var 10) (var 11) (var 12))
          (denominator (var 0) (var 1) (var 2) (var 3) (var 4) (var 9) (var 11) (var 12))) :=
  closeUniv 13 (.impI (original_upper_grid_monomial_cap _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBetaUpperGridMonomialComparison

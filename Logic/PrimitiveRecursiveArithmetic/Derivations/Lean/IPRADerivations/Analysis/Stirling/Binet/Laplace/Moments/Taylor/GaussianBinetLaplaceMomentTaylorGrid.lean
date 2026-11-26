import IPRADerivations.Analysis.Stirling.Binet.Laplace.Moments.Taylor.GaussianBinetLaplaceMomentTaylorMajorant
import IPRADerivations.Analysis.Integration.Quadrature.GaussianRationalQuadratureAffineRemainder

/-!
# Taylor bound on an aligned grid of actual Binet moment observations

Use the actual weighted evaluator at one precision and one physical
mesh for three consecutive Taylor terms and the quadratic majorant.
The latter is compared with the same original quadrature two moment
orders higher. The numerical mesh size disappears from the bound.
-/

set_option autoImplicit false
set_option maxHeartbeats 1250000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentTaylorGrid

open_ipra
open GaussianBinetLaplaceIntegrand (input)
open GaussianBinetLaplaceMomentFloor (observation evaluatorF evaluator_at fixedData)
open GaussianBinetLaplaceMomentTaylorMajorant (scalar observation_majorant coefficient errorCost scalar_observation_distance)
open GaussianBinetLaplaceMomentTaylorRows (linearObservation)
open GaussianBinetLaplaceStrip (source tagNumerator tag_inside)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName
  (grid grid_inside inside sampleBody sampleData sample_body_at quadrature
    field0 field1 field2 field3 field4 field5 field0_at field1_at field2_at field3_at field4_at field5_at)
open GaussianDominantPairAlgebra (radiusPoint radius_bounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalFiniteSum (multiplyBody multiply_body_at sum sum_multiply)
open GaussianRationalHorner (qadd qmul positive_product)
open GaussianRationalMetric (qsub qnegative bounded distanceBounded)
open GaussianRationalQuadratureAffineRemainder (rowBody rowData row_at weighted_remainder)
open GaussianRationalReciprocal (bounded_product bound_congr)
open GaussianRationalRiemannRefinement (leftSum weight termsDistance)
open GaussianRationalSumMajorant (termsMajorized majorized majorized_congr majorant_bound)
open GaussianRationalSyntheticDivision (qmul_congr qadd_congr qsub_congr)
open RationalGaussianEmbedding (embed)
open RationalGaussianRealPart (embedBody)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "f" => sampleBody evaluatorF

def scalarEvaluatorTerm (p t x : PTm n) : PTm n :=
  scalar p (field0 x) (field1 x) (field2 x) (field3 x) (field4 x) (field5 x) (tagNumerator t) (sndT t)
def scalarEvaluatorF : PR 3 := PTm.toPR (scalarEvaluatorTerm (var 0) (var 1) (var 2))
abbrev scalarBody : PTm 2 := sampleBody scalarEvaluatorF
def scalarData (p M j X D T H Q A C E : PTm n) : PTm n :=
  sampleData p M (E+A) C E (sampleData j X D T H Q)
def rowInput (p M j X D R T A C E : PTm n) : PTm n :=
  sampleData p M (E+A) C E (fixedData j X D R T)
def residualData (p M j X D R S T H Q A C E : PTm n) : PTm n :=
  rowData (qnegative (radiusPoint H Q)) (rowInput p M j (X*Q+H*D) (D*Q) S T A C E)
    (rowInput p M j X D R T A C E) (rowInput p M (succ j) X D R T A C E)

ipra_subst scalarEvaluatorTerm [GaussianBinetLaplaceStrip.tagNumerator]
ipra_subst scalarData
ipra_subst rowInput
ipra_subst residualData

private theorem val_four {α : Type} (a b c d e x g h i : α) : ![a,b,c,d,e,x,g,h,i] (4 : Fin 9) = e := rfl
private theorem val_five {α : Type} (a b c d e x g h i : α) : ![a,b,c,d,e,x,g,h,i] (5 : Fin 9) = x := rfl
private theorem val_six {α : Type} (a b c d e x g h i : α) : ![a,b,c,d,e,x,g,h,i] (6 : Fin 9) = g := rfl
private theorem val_seven {α : Type} (a b c d e x g h i : α) : ![a,b,c,d,e,x,g,h,i] (7 : Fin 9) = h := rfl
private theorem val_eight {α : Type} (a b c d e x g h i : α) : ![a,b,c,d,e,x,g,h,i] (8 : Fin 9) = i := rfl

private theorem scalar_evaluator_at (p t j X D T H Q : PTm n) :
    Γ ⊢[PRAAx] ap3 scalarEvaluatorF p t (sampleData j X D T H Q) ≐ scalar p j X D T H Q (tagNumerator t) (sndT t) := by
  let x := sampleData j X D T H Q
  have read : Γ ⊢[PRAAx] ap3 scalarEvaluatorF p t x ≐ scalarEvaluatorTerm p t x := by
    simpa only [scalarEvaluatorF,ap3,subst_scalarEvaluatorTerm,Syn.subst_var,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
      toPR_eq (Γ := Γ) (scalarEvaluatorTerm (var 0) (var 1) (var 2) : PTm 3) ![p,t,x]
  apply read.eqTrans
  simpa only [scalarEvaluatorTerm,GaussianBinetLaplaceMomentTaylorMajorant.subst_scalar,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,
    val_four,val_five,val_six,val_seven,val_eight] using
    Prf.eqCongr (scalar (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) : PTm 9)
      (σ := ![p,field0 x,field1 x,field2 x,field3 x,field4 x,field5 x,tagNumerator t,sndT t])
      (σ' := ![p,j,X,D,T,H,Q,tagNumerator t,sndT t]) (fun i => by
        fin_cases i
        exact .eqRefl _
        exact field0_at _ _ _ _ _ _
        exact field1_at _ _ _ _ _ _
        exact field2_at _ _ _ _ _ _
        exact field3_at _ _ _ _ _ _
        exact field4_at _ _ _ _ _ _
        exact field5_at _ _ _ _ _ _
        exact .eqRefl _
        exact .eqRefl _)

private theorem scalar_at (i p M j X D T H Q A C E : PTm n) :
    let t := grid i M (E+A) C E
    Γ ⊢[PRAAx] inst2 scalarBody i (scalarData p M j X D T H Q A C E) ≐
      scalar p j X D T H Q (tagNumerator t) (sndT t) :=
  (sample_body_at scalarEvaluatorF i p M (E+A) C E (sampleData j X D T H Q)).eqTrans (scalar_evaluator_at _ _ _ _ _ _ _ _)

private theorem actual_at (i p M j X D R T A C E : PTm n) :
    let t := grid i M (E+A) C E
    Γ ⊢[PRAAx] inst2 f i (rowInput p M j X D R T A C E) ≐ observation p j X D R T (tagNumerator t) (sndT t) :=
  (sample_body_at evaluatorF i p M (E+A) C E (fixedData j X D R T)).eqTrans (evaluator_at _ _ _ _ _ _ _)

private theorem negative_product (x y : PTm n) : Γ ⊢[PRAAx] qmul (qnegative x) y ≐ qnegative (qmul x y) :=
  (GaussianEulerLowerRationalPowerReference.negative_move x y).eqTrans (GaussianMomentReflection.negative_right_product x y)

private theorem actual_residual_at (i p M j X D R S T H Q A C E : PTm n) :
    let t := grid i M (E+A) C E
    Γ ⊢[PRAAx] inst2 (rowBody f f f) i (residualData p M j X D R S T H Q A C E) ≐
      qsub (observation p j (X*Q+H*D) (D*Q) S T (tagNumerator t) (sndT t))
        (linearObservation p j X D R T H Q (tagNumerator t) (sndT t)) := by
  have read := row_at (Γ := Γ) f f f i (qnegative (radiusPoint H Q))
    (rowInput p M j (X*Q+H*D) (D*Q) S T A C E) (rowInput p M j X D R T A C E) (rowInput p M (succ j) X D R T A C E)
  exact read.eqTrans (qsub_congr (actual_at i p M j _ _ S T A C E)
    (qadd_congr (actual_at i p M j X D R T A C E)
      ((qmul_congr (.eqRefl _) (actual_at i p M (succ j) X D R T A C E)).eqTrans (negative_product _ _))))

private theorem cell_input (i M X D R T A C E : PTm n)
    (h : Γ ⊢[PRAAx] source X zero D zero R T A C E) (hM : Γ ⊢[PRAAx] le one M) (hi : Γ ⊢[PRAAx] lt i M) :
    let t := grid i M (E+A) C E
    Γ ⊢[PRAAx] input X zero D zero R T (tagNumerator t) (sndT t) := by
  let t := grid i M (E+A) C E
  have he := h.andE₂.andE₁
  have ht : Γ ⊢[PRAAx] inside (E+A) C E t :=
    grid_inside _ _ _ _ _ (le_trans he (le_add_right _ _)) he hM (le_of_lt hi)
  exact .andI h.andE₁ (.andI ht.andE₂.andE₁ (tag_inside t A C E T he h.andE₂.andE₂ ht).andE₂)

private theorem cell_majorant (i p M j X D R S T H Q A C E : PTm n)
    (h : Γ ⊢[PRAAx] source X zero D zero R T A C E) (h' : Γ ⊢[PRAAx] source (X*Q+H*D) zero (D*Q) zero S T A C E)
    (hM : Γ ⊢[PRAAx] le one M) (hi : Γ ⊢[PRAAx] lt i M) (hQ : Γ ⊢[PRAAx] le one Q) (hH : Γ ⊢[PRAAx] le H Q) :
    Γ ⊢[PRAAx] majorized (inst2 (rowBody f f f) i (residualData p M j X D R S T H Q A C E))
      (inst2 scalarBody i (scalarData p M j X D T H Q A C E)) := by
  have b := cell_input i M X D R T A C E h hM hi
  have b' := cell_input i M (X*Q+H*D) (D*Q) S T A C E h' hM hi
  exact majorized_congr (actual_residual_at i p M j X D R S T H Q A C E).eqSymm
    (scalar_at i p M j X D T H Q A C E).eqSymm
    (observation_majorant p j X D R S T H Q _ _ b b' hQ hH)

private theorem cell_distance (i p M j X D R T H Q A C E : PTm n)
    (h : Γ ⊢[PRAAx] source X zero D zero R T A C E) (hM : Γ ⊢[PRAAx] le one M)
    (hi : Γ ⊢[PRAAx] lt i M) (hQ : Γ ⊢[PRAAx] le one Q) (hH : Γ ⊢[PRAAx] le H Q) :
    Γ ⊢[PRAAx] distanceBounded (inst2 (embedBody scalarBody) i (scalarData p M j X D T H Q A C E))
      (inst2 (multiplyBody f) i (pairT (coefficient H Q) (rowInput p M (succ (succ j)) X D R T A C E)))
      (errorCost j T) (unit p) := by
  let sc := scalarData p M j X D T H Q A C E
  let x := rowInput p M (succ (succ j)) X D R T A C E
  let t := grid i M (E+A) C E
  have read := RationalGaussianRealPart.embed_congr (scalar_at (Γ := Γ) i p M j X D T H Q A C E)
  have point : Γ ⊢[PRAAx] inst2 (embedBody scalarBody) i sc ≐ embed (scalar p j X D T H Q (tagNumerator t) (sndT t)) := by
    simpa only [embedBody,inst2,RationalGaussianEmbedding.subst_embed,sc,t] using read
  have right := (multiply_body_at (Γ := Γ) f (coefficient H Q) i x).eqTrans
    (qmul_congr (.eqRefl _) (actual_at i p M (succ (succ j)) X D R T A C E))
  exact distance_congr point.eqSymm right.eqSymm (.eqRefl _) (.eqRefl _)
    (scalar_observation_distance p j X D R T H Q _ _ (cell_input i M X D R T A C E h hM hi) hQ hH)

private theorem left_multiply (c M x C E : PTm n) :
    Γ ⊢[PRAAx] leftSum (multiplyBody f) M (pairT c x) C E ≐ qmul c (leftSum f M x C E) := by
  let w := weight C E M
  let v := sum f M x
  exact (qmul_congr (.eqRefl w) (sum_multiply f c M x)).eqTrans
    ((GaussianReciprocalHorner.qmul_associative w c v).eqSymm.eqTrans
      ((qmul_congr (GaussianRationalPowerAlgebra.qmul_commutative w c) (.eqRefl v)).eqTrans
        (GaussianReciprocalHorner.qmul_associative c w v)))

theorem aligned_taylor_bound (p M j X D R S T H Q A C E U V : PTm n)
    (h : Γ ⊢[PRAAx] source X zero D zero R T A C E) (h' : Γ ⊢[PRAAx] source (X*Q+H*D) zero (D*Q) zero S T A C E)
    (hM : Γ ⊢[PRAAx] le one M) (hQ : Γ ⊢[PRAAx] le one Q) (hH : Γ ⊢[PRAAx] le H Q) (hV : Γ ⊢[PRAAx] le one V)
    (hU : Γ ⊢[PRAAx] bounded (quadrature evaluatorF p M (E+A) C E (fixedData (succ (succ j)) X D R T)) U V) :
    let x := quadrature evaluatorF p M (E+A) C E (fixedData j X D R T)
    let y := quadrature evaluatorF p M (E+A) C E (fixedData j (X*Q+H*D) (D*Q) S T)
    let z := quadrature evaluatorF p M (E+A) C E (fixedData (succ j) X D R T)
    Γ ⊢[PRAAx] distanceBounded y (qsub x (qmul (radiusPoint H Q) z))
      ((C*errorCost j T)*((Q*Q)*V)+(num 3*(H*H)*U)*(E*unit p)) ((E*unit p)*((Q*Q)*V)) := by
  let r := residualData p M j X D R S T H Q A C E
  let sc := scalarData p M j X D T H Q A C E
  let higher := rowInput p M (succ (succ j)) X D R T A C E
  let c := coefficient H Q
  let s (x : PTm n) := Syn.shift x
  let Δ := lt (var 0) (s M) :: Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] source (s X) zero (s D) zero (s R) (s T) (s A) (s C) (s E) := by
    simpa only [Δ,s,Fm.shift,Syn.shift,GaussianBinetLaplaceStrip.subst_source,ConciseIPRA.PTm.subst_zero] using h.shift.wk
  have hs' : Δ ⊢[PRAAx] source (s X*s Q+s H*s D) zero (s D*s Q) zero (s S) (s T) (s A) (s C) (s E) := by
    simpa only [Δ,s,Fm.shift,Syn.shift,GaussianBinetLaplaceStrip.subst_source,ConciseIPRA.PTm.subst_zero,PTm.subst_mul,PTm.subst_add]
      using h'.shift.wk
  have ms : Δ ⊢[PRAAx] le one (s M) := (Order.shift_one_le hM).wk
  have qs : Δ ⊢[PRAAx] le one (s Q) := (Order.shift_one_le hQ).wk
  have sm : Δ ⊢[PRAAx] le (s H) (s Q) := by simpa [Δ,s,Fm.shift,Syn.shift] using hH.shift.wk
  have rows : Γ ⊢[PRAAx] termsMajorized (rowBody f f f) scalarBody M r sc := by
    refine .allI (.impI ?_)
    simpa only [Δ,r,sc,s,Syn.shift,subst_scalarData,subst_residualData] using
      cell_majorant (var 0) (s p) (s M) (s j) (s X) (s D) (s R) (s S) (s T) (s H) (s Q) (s A) (s C) (s E)
        hs hs' ms Prf.hyp0 qs sm
  have distances : Γ ⊢[PRAAx] termsDistance (embedBody scalarBody) (multiplyBody f) M sc (pairT c higher)
      (errorCost j T) (unit p) := by
    refine .allI (.impI ?_)
    simpa only [Δ,sc,c,higher,s,Syn.shift,subst_scalarData,subst_rowInput,
      GaussianBinetLaplaceMomentTaylorMajorant.subst_coefficient,GaussianBinetLaplaceMomentTaylorMajorant.subst_errorCost,
      GaussianCoefficientNameBounds.subst_unit,subst_pairT,ConciseIPRA.PTm.subst_succ] using
      cell_distance (var 0) (s p) (s M) (s j) (s X) (s D) (s R) (s T) (s H) (s Q) (s A) (s C) (s E)
        hs ms Prf.hyp0 qs sm
  have hE := h.andE₂.andE₁
  have hp := unit_positive (Γ := Γ) p
  have hQQ := positive_product _ _ hQ hQ
  have hQV := positive_product _ _ hQQ hV
  have hEU := positive_product _ _ hE hp
  have close := GaussianCompactScalarMajorant.common_mesh_distance (embedBody scalarBody) (multiplyBody f)
    M sc (pairT c higher) C E (errorCost j T) (unit p) hM hE hp distances
  have read := GaussianCompactScalarMajorant.scalar_left_embedding scalarBody M sc C E hE hM
  have glue := distance_congr read.eqSymm (left_multiply c M higher C E) (.eqRefl _) (.eqRefl _) close
  have q := bounded_product c (leftSum f M higher C E) (num 3*(H*H)) (Q*Q) U V hQQ hV
    (radius_bounded _ _ hQQ) hU
  have mag := GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _ hEU hQV glue q
  have major := GaussianCompactScalarMajorant.weighted_majorant (rowBody f f f) scalarBody M r sc C E hM hE rows
  have bound := majorant_bound _ _ _ _ (positive_product _ _ hEU hQV) major mag
  have eq := weighted_remainder (Γ := Γ) f f f (qnegative (radiusPoint H Q)) M
    (rowInput p M j (X*Q+H*D) (D*Q) S T A C E) (rowInput p M j X D R T A C E)
    (rowInput p M (succ j) X D R T A C E) C E
  exact bound_congr (eq.eqTrans (qsub_congr (.eqRefl _) (qadd_congr (.eqRefl _) (negative_product _ _))))
    (.eqRefl _) (.eqRefl _) bound

theorem actual_aligned_Binet_moment_Taylor_grid_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 15
    (let p := var 0
     let M := var 1
     let j := var 2
     let X := var 3
     let D := var 4
     let R := var 5
     let S := var 6
     let T := var 7
     let H := var 8
     let Q := var 9
     let A := var 10
     let C := var 11
     let E := var 12
     let U := var 13
     let V := var 14
     let x := quadrature evaluatorF p M (E+A) C E (fixedData j X D R T)
     let y := quadrature evaluatorF p M (E+A) C E (fixedData j (X*Q+H*D) (D*Q) S T)
     let z := quadrature evaluatorF p M (E+A) C E (fixedData (succ j) X D R T)
     let w := quadrature evaluatorF p M (E+A) C E (fixedData (succ (succ j)) X D R T)
     (source X zero D zero R T A C E ⋏ source (X*Q+H*D) zero (D*Q) zero S T A C E) ⟶
       (le one M ⋏ (le one Q ⋏ le H Q)) ⟶ (le one V ⋏ bounded w U V) ⟶
       distanceBounded y (qsub x (qmul (radiusPoint H Q) z))
         ((C*errorCost j T)*((Q*Q)*V)+(num 3*(H*H)*U)*(E*unit p)) ((E*unit p)*((Q*Q)*V))) := by
  apply closeUniv 15
  refine .impI (.impI (.impI ?_))
  exact aligned_taylor_bound _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Prf.hyp0.wk.wk.andE₁ Prf.hyp0.wk.wk.andE₂ Prf.hyp1.andE₁
    Prf.hyp1.andE₂.andE₁ Prf.hyp1.andE₂.andE₂ Prf.hyp0.andE₁ Prf.hyp0.andE₂

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentTaylorGrid

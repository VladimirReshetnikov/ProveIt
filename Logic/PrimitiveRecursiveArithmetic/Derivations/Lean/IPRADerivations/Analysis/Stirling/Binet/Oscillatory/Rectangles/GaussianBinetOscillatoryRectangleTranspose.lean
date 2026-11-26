import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.Arctangent.GaussianBinetArctangentCosineRectangle
import IPRADerivations.Analysis.Integration.Quadrature.GaussianRationalQuadratureMean
import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.GaussianRationalFubini

/-!
# Exact transposition of the original cosine rectangle

Each outer frequency row contains the two actual complex exponential
panel sums. Bring their mean inside and apply the checked finite
Gaussian summation exchange. Both original rational mesh weights are
kept throughout.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianBinetOscillatoryRectangleTranspose

open_ipra
open GaussianBinetArctangentCosineRectangle (body fixedData rowTerm rectangle)
open GaussianBinetArctangentResolvent (pole)
open GaussianBinetArctangentCosineLaplace (mean)
open GaussianBinetLaplaceStrip (tagNumerator)
open GaussianCompactRiemannName (field0 field1 field2 field3 field4 field5 grid sampleBody sampleData)
open GaussianRationalFiniteSum (multiplyBody multiply_body_at sum sum_index_congr sum_multiply)
open GaussianRationalFubini (row rowBody row_entry rowSumBody row_sum_at columnFirst rowFirst)
open GaussianRationalHorner (qmul)
open GaussianRationalMetric (qnegative)
open GaussianRationalRiemannRefinement (leftSum weight)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianReciprocalHorner (qmul_associative)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "F" => GaussianBinetExponentialIntegralGrid.evaluatorF
local notation "f" => sampleBody F
local notation "mF" => GaussianRationalQuadratureMean.body f f
local notation "dM" => GaussianRationalQuadratureMean.data

def outerTag (i d : PTm n) : PTm n := grid i (field1 d) (field2 d) (field3 d) (field4 d)
def panels (d : PTm n) : PTm n := sndT (sndT (field5 (field5 d)))
def horizon (d : PTm n) : PTm n := field2 (field5 d)*fstT (sndT (field5 (field5 d)))
def panelData (s : Bool) (i d : PTm n) : PTm n :=
  let x := field5 d
  let t := outerTag i d
  let T := horizon d
  let q := qnegative (pole s (field0 x) (field1 x) (field2 x) (field3 x) (tagNumerator t) (sndT t))
  let S := (field4 x+fstT (field5 x))*T
  sampleData (field0 d+panels d) (panels d) one T one (pairT q S)
def matrixTerm (i j d : PTm n) : PTm n := inst2 mF j (dM (panelData false i d) (panelData true i d))
def matrix : PTm 3 := matrixTerm (var 0) (var 1) (var 2)
def data (p M X Y D sign A B R U L N : PTm n) : PTm n :=
  sampleData p M (B+zero) A B (fixedData X Y D sign R U L N)

ipra_subst outerTag
ipra_subst panels
ipra_subst horizon
ipra_subst panelData [one]
@[simp] theorem subst_matrixTerm {m : ℕ} (σ : Fin n → PTm m) (i j d : PTm n) :
    Syn.subst σ (matrixTerm i j d) = matrixTerm (Syn.subst σ i) (Syn.subst σ j) (Syn.subst σ d) := by
  simp only [matrixTerm,subst_inst2,subst_panelData,GaussianRationalQuadratureMean.subst_data]
@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (p M X Y D sign A B R U L N : PTm n) :
    Syn.subst σ (data p M X Y D sign A B R U L N) = data (Syn.subst σ p) (Syn.subst σ M)
      (Syn.subst σ X) (Syn.subst σ Y) (Syn.subst σ D) (Syn.subst σ sign) (Syn.subst σ A) (Syn.subst σ B)
      (Syn.subst σ R) (Syn.subst σ U) (Syn.subst σ L) (Syn.subst σ N) := by simp [data]

theorem matrix_at (i j d : PTm n) : inst3 matrix i j d = matrixTerm i j d := by
  simp only [matrix,inst3,subst_matrixTerm,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

private theorem row_samples (i d : PTm n) : Γ ⊢[PRAAx]
    row matrix i (panels d) d ≐ sum mF (panels d) (dM (panelData false i d) (panelData true i d)) := by
  apply GaussianRationalFiniteSum.sum_congr_bounded
  refine .allI (.impI ?_)
  have e := row_entry (Γ := lt (var 0) (Syn.shift (panels d)) :: Γ.map Fm.shift) matrix (Syn.shift i) (var 0) (Syn.shift d)
  rw [matrix_at] at e
  simpa only [GaussianRationalFiniteSum.termsEqual,Syn.shift,subst_pairT,subst_panelData,GaussianRationalQuadratureMean.subst_data,matrixTerm] using e

theorem actual_row_at (i d : PTm n) : Γ ⊢[PRAAx]
    inst2 body i d ≐ qmul (weight (horizon d) one (panels d)) (row matrix i (panels d) d) := by
  let t := outerTag i d
  let x := field5 d
  have read : inst2 body i d = rowTerm (field0 d) t x := by
    simp only [body,inst2,GaussianBinetArctangentCosineRectangle.subst_rowTerm,t,x,outerTag,GaussianCompactRiemannName.subst_grid,
      GaussianCompactRiemannName.subst_field0,GaussianCompactRiemannName.subst_field1,GaussianCompactRiemannName.subst_field2,
      GaussianCompactRiemannName.subst_field3,GaussianCompactRiemannName.subst_field4,GaussianCompactRiemannName.subst_field5,
      Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [read]
  exact (GaussianRationalQuadratureMean.left_mean f f (panels d) (panelData false i d) (panelData true i d) (horizon d) one).eqTrans
    (qmul_congr (.eqRefl _) (row_samples i d).eqSymm)

private theorem field5_congr {x y : PTm n} (e : Γ ⊢[PRAAx] x ≐ y) : Γ ⊢[PRAAx] field5 x ≐ field5 y := by
  simpa only [GaussianCompactRiemannName.subst_field5,Syn.subst_var,Syn.inst_zero] using
    Prf.eqCongr1 (field5 (var 0)) e

theorem panels_at (p M X Y D sign A B R U L N : PTm n) : Γ ⊢[PRAAx]
    panels (data p M X Y D sign A B R U L N) ≐ N := by
  let d := data p M X Y D sign A B R U L N
  have e : Γ ⊢[PRAAx] field5 d ≐ fixedData X Y D sign R U L N := GaussianCompactRiemannName.field5_at _ _ _ _ _ _
  have g : Γ ⊢[PRAAx] field5 (field5 d) ≐ pairT U (pairT L N) :=
    (field5_congr e).eqTrans (GaussianCompactRiemannName.field5_at _ _ _ _ _ _)
  exact (congrSnd ((congrSnd g).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)

theorem horizon_at (p M X Y D sign A B R U L N : PTm n) : Γ ⊢[PRAAx]
    horizon (data p M X Y D sign A B R U L N) ≐ D*L := by
  let d := data p M X Y D sign A B R U L N
  let x := fixedData X Y D sign R U L N
  have e : Γ ⊢[PRAAx] field5 d ≐ x := GaussianCompactRiemannName.field5_at _ _ _ _ _ _
  have readD : Γ ⊢[PRAAx] field2 (field5 d) ≐ field2 x := by
    simpa only [GaussianCompactRiemannName.subst_field2,Syn.subst_var,Syn.inst_zero] using
      Prf.eqCongr1 (field2 (var 0)) e
  have g : Γ ⊢[PRAAx] field5 (field5 d) ≐ pairT U (pairT L N) :=
    (field5_congr e).eqTrans (GaussianCompactRiemannName.field5_at _ _ _ _ _ _)
  exact congrMul (readD.eqTrans (GaussianCompactRiemannName.field2_at _ _ _ _ _ _))
    ((congrFst ((congrSnd g).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _))

private theorem weight_congr {T T' N N' : PTm n} (hT : Γ ⊢[PRAAx] T ≐ T') (hN : Γ ⊢[PRAAx] N ≐ N') :
    Γ ⊢[PRAAx] weight T one N ≐ weight T' one N' := by
  simpa only [GaussianRationalRiemannRefinement.subst_weight,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    one,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (weight (var 0) one (var 1) : PTm 2)
      (σ := ![T,N]) (σ' := ![T',N']) (fun j => by fin_cases j; exact hT; exact hN)

theorem returned_transpose (p M X Y D sign A B R U L N : PTm n) : Γ ⊢[PRAAx]
    rectangle p M X Y D sign A B R U L N ≐
      qmul (qmul (weight A B M) (weight (D*L) one N)) (columnFirst matrix M N (data p M X Y D sign A B R U L N)) := by
  let d := data p M X Y D sign A B R U L N
  let w := weight (D*L) one N
  let other := multiplyBody (rowSumBody matrix)
  let y := pairT w (pairT N d)
  have rows : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual body other M d y := by
    refine .allI (.impI ?_)
    let s (t : PTm n) := Syn.shift t
    let Δ := lt (var 0) (s M) :: Γ.map Fm.shift
    let d' := data (s p) (s M) (s X) (s Y) (s D) (s sign) (s A) (s B) (s R) (s U) (s L) (s N)
    let w' := weight (s D*s L) one (s N)
    have hn := panels_at (Γ := Δ) (s p) (s M) (s X) (s Y) (s D) (s sign) (s A) (s B) (s R) (s U) (s L) (s N)
    have ht := horizon_at (Γ := Δ) (s p) (s M) (s X) (s Y) (s D) (s sign) (s A) (s B) (s R) (s U) (s L) (s N)
    have r : Δ ⊢[PRAAx] row matrix (var 0) (panels d') d' ≐ row matrix (var 0) (s N) d' :=
      sum_index_congr (rowBody matrix) hn (.eqRefl _)
    have a := (actual_row_at (Γ := Δ) (var 0) d').eqTrans (qmul_congr (weight_congr ht hn) r)
    have b := (multiply_body_at (Γ := Δ) (rowSumBody matrix) w' (var 0) (pairT (s N) d')).eqTrans
      (qmul_congr (.eqRefl _) (row_sum_at matrix (var 0) (s N) d'))
    simpa only [GaussianRationalFiniteSum.termsEqual,d,w,other,y,s,Δ,d',w',subst_data,Syn.shift,subst_pairT,PTm.subst_mul,
      GaussianRationalRiemannRefinement.subst_weight,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using a.eqTrans b.eqSymm
  have sums := (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ rows).eqTrans
    (sum_multiply (rowSumBody matrix) w M (pairT N d))
  exact (qmul_congr (.eqRefl _) sums).eqTrans ((qmul_associative _ _ _).eqSymm.eqTrans
    (qmul_congr (.eqRefl _) (GaussianRationalFubini.fubini matrix M N d)))

end LeanProofs.IPRA.Analysis.GaussianBinetOscillatoryRectangleTranspose

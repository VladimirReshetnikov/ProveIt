import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.GaussianBinetOscillatoryRectangleTranspose
import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.GaussianBinetOscillatoryPanelFactor

/-!
# Damping and cosine on the actual transposed rectangle cells

Read both original exponential panel codes on the transposed mesh.
The exact coordinates are shared by the two factors, so the checked
pointwise product estimate applies with its original observation clock.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBinetOscillatoryMatrixCell

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetArctangentResolvent (pole subst_pole)
open GaussianBinetArctangentCosineLaplace (mean)
open GaussianBinetExponentialIntegralGrid (row)
open GaussianBinetImaginaryExponentialIntegral (coefficient)
open GaussianBinetLaplaceStrip (tagNumerator tag_inside)
open GaussianBinetOscillatoryRectangleTranspose (matrix data matrix_at matrixTerm outerTag panelData panels_at horizon_at)
open GaussianBinetOscillatoryPanelFactor (polarity cosine_factor_sample)
open GaussianCoefficientNameBounds (unit)
open GaussianCompactRiemannName (field0 field1 field2 field3 field4 field5 grid grid_congr grid_inside sampleBody sampleData)
open GaussianInverseBinomialRows (negative_congr)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerResidualDomain (source)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (qmul)
open GaussianRationalMetric (distanceBounded qnegative)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "F" => GaussianBinetExponentialIntegralGrid.evaluatorF
local notation "f" => sampleBody F
local notation "fixed" => GaussianBinetArctangentCosineRectangle.fixedData

private theorem pole_fields (s : Bool) {X X' Y Y' D D' sign sign' A A' B B' : PTm n}
    (hx : Γ ⊢[PRAAx] X ≐ X') (hy : Γ ⊢[PRAAx] Y ≐ Y') (hd : Γ ⊢[PRAAx] D ≐ D') (hs : Γ ⊢[PRAAx] sign ≐ sign')
    (ha : Γ ⊢[PRAAx] A ≐ A') (hb : Γ ⊢[PRAAx] B ≐ B') : Γ ⊢[PRAAx] pole s X Y D sign A B ≐ pole s X' Y' D' sign' A' B' := by
  have val₅ {α : Type} (a b c d e f' : α) : ![a,b,c,d,e,f'] (5 : Fin 6) = f' := rfl
  simpa only [subst_pole,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,val₅,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (pole s (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6)
      (σ := ![X,Y,D,sign,A,B]) (σ' := ![X',Y',D',sign',A',B']) (fun j => by
        fin_cases j; exact hx; exact hy; exact hd; exact hs; exact ha; exact hb)

theorem outer_tag_at (i p M X Y D sign A B R U L N : PTm n) : Γ ⊢[PRAAx]
    outerTag i (data p M X Y D sign A B R U L N) ≐ grid i M (B+zero) A B :=
  grid_congr _ _ _ _ _ _ _ _ _ _ (.eqRefl _) (GaussianCompactRiemannName.field1_at _ _ _ _ _ _)
    (GaussianCompactRiemannName.field2_at _ _ _ _ _ _) (GaussianCompactRiemannName.field3_at _ _ _ _ _ _)
    (GaussianCompactRiemannName.field4_at _ _ _ _ _ _)

private theorem panel_data_at (s : Bool) (i p M X Y D sign A B R U L N : PTm n) : Γ ⊢[PRAAx]
    panelData s i (data p M X Y D sign A B R U L N) ≐
      let t := grid i M (B+zero) A B
      sampleData (p+N) N one (D*L) one (pairT (qnegative (pole s X Y D sign (tagNumerator t) (sndT t))) ((R+U)*(D*L))) := by
  let x := fixed X Y D sign R U L N
  let d := data p M X Y D sign A B R U L N
  let t := grid i M (B+zero) A B
  have dx : Γ ⊢[PRAAx] field5 d ≐ x := GaussianCompactRiemannName.field5_at _ _ _ _ _ _
  have hx : Γ ⊢[PRAAx] field0 (field5 d) ≐ X :=
    (show Γ ⊢[PRAAx] field0 (field5 d) ≐ field0 x from by
      simpa only [GaussianCompactRiemannName.subst_field0,Syn.subst_var,Syn.inst_zero] using Prf.eqCongr1 (field0 (var 0)) dx).eqTrans
      (GaussianCompactRiemannName.field0_at _ _ _ _ _ _)
  have hy : Γ ⊢[PRAAx] field1 (field5 d) ≐ Y :=
    (show Γ ⊢[PRAAx] field1 (field5 d) ≐ field1 x from by
      simpa only [GaussianCompactRiemannName.subst_field1,Syn.subst_var,Syn.inst_zero] using Prf.eqCongr1 (field1 (var 0)) dx).eqTrans
      (GaussianCompactRiemannName.field1_at _ _ _ _ _ _)
  have hd : Γ ⊢[PRAAx] field2 (field5 d) ≐ D :=
    (show Γ ⊢[PRAAx] field2 (field5 d) ≐ field2 x from by
      simpa only [GaussianCompactRiemannName.subst_field2,Syn.subst_var,Syn.inst_zero] using Prf.eqCongr1 (field2 (var 0)) dx).eqTrans
      (GaussianCompactRiemannName.field2_at _ _ _ _ _ _)
  have hs : Γ ⊢[PRAAx] field3 (field5 d) ≐ sign :=
    (show Γ ⊢[PRAAx] field3 (field5 d) ≐ field3 x from by
      simpa only [GaussianCompactRiemannName.subst_field3,Syn.subst_var,Syn.inst_zero] using Prf.eqCongr1 (field3 (var 0)) dx).eqTrans
      (GaussianCompactRiemannName.field3_at _ _ _ _ _ _)
  have hr : Γ ⊢[PRAAx] field4 (field5 d) ≐ R :=
    (show Γ ⊢[PRAAx] field4 (field5 d) ≐ field4 x from by
      simpa only [GaussianCompactRiemannName.subst_field4,Syn.subst_var,Syn.inst_zero] using Prf.eqCongr1 (field4 (var 0)) dx).eqTrans
      (GaussianCompactRiemannName.field4_at _ _ _ _ _ _)
  have hg : Γ ⊢[PRAAx] field5 (field5 d) ≐ pairT U (pairT L N) :=
    (show Γ ⊢[PRAAx] field5 (field5 d) ≐ field5 x from by
      simpa only [GaussianCompactRiemannName.subst_field5,Syn.subst_var,Syn.inst_zero] using Prf.eqCongr1 (field5 (var 0)) dx).eqTrans
      (GaussianCompactRiemannName.field5_at _ _ _ _ _ _)
  have hp : Γ ⊢[PRAAx] field0 d ≐ p := GaussianCompactRiemannName.field0_at _ _ _ _ _ _
  have hn := panels_at (Γ := Γ) p M X Y D sign A B R U L N
  have hT := horizon_at (Γ := Γ) p M X Y D sign A B R U L N
  have ht : Γ ⊢[PRAAx] outerTag i d ≐ t := outer_tag_at i p M X Y D sign A B R U L N
  have hA := congrMonus (congrFst ht) (congrSnd ht)
  have hPole := negative_congr (pole_fields s hx hy hd hs hA (congrSnd ht))
  have hRadius := congrMul (congrAdd hr ((congrFst hg).eqTrans (fst_pair _ _))) hT
  exact congrPairT (congrAdd hp hn)
    (congrPairT hn (congrPairT (.eqRefl one) (congrPairT hT (congrPairT (.eqRefl one) (congrPairT hPole hRadius)))))

theorem original_cell (i j p M X Y D sign A B R U L N : PTm n) : Γ ⊢[PRAAx]
    inst3 matrix i j (data p M X Y D sign A B R U L N) ≐
      let T := D*L
      let t := grid i M (B+zero) A B
      mean (row (p+N) (qnegative (pole false X Y D sign (tagNumerator t) (sndT t))) ((R+U)*T) (T*j) N)
        (row (p+N) (qnegative (pole true X Y D sign (tagNumerator t) (sndT t))) ((R+U)*T) (T*j) N) := by
  let d := data p M X Y D sign A B R U L N
  let t := grid i M (B+zero) A B
  let T := D*L
  let S := (R+U)*T
  have h s : Γ ⊢[PRAAx] inst2 f j (panelData s i d) ≐
      row (p+N) (qnegative (pole s X Y D sign (tagNumerator t) (sndT t))) S (T*j) N :=
    (congrInst2 f (.eqRefl _) (panel_data_at s i p M X Y D sign A B R U L N)).eqTrans
      (GaussianBinetExponentialIntegralGrid.cell_at j (p+N) _ S T N)
  rw [matrix_at]
  exact (GaussianRationalQuadratureMean.entry f f j (panelData false i d) (panelData true i d)).eqTrans
    (qmul_congr (.eqRefl _) (qadd_congr (h false) (h true)))

theorem factor_error (i j p M X Y D sign A B R U L N : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R) (hB : Γ ⊢[PRAAx] le one B)
    (hM : Γ ⊢[PRAAx] le one M) (hN : Γ ⊢[PRAAx] le one N) (hA : Γ ⊢[PRAAx] le A (B*U))
    (hi : Γ ⊢[PRAAx] le i M) (hj : Γ ⊢[PRAAx] le j N) :
    let T := D*L
    let t := grid i M (B+zero) A B
    Γ ⊢[PRAAx] distanceBounded (inst3 matrix i j (data p M X Y D sign A B R U L N))
      (qmul (row (p+N) (qnegative (argument X Y D sign)) (R*T) (T*j) N)
        (mean (row (p+N) (coefficient (tagNumerator t) (sndT t) (polarity false)) (U*T) (T*j) N)
          (row (p+N) (coefficient (tagNumerator t) (sndT t) (polarity true)) (U*T) (T*j) N))) (num 10) (unit (p+N)) := by
  let T := D*L
  let t := grid i M (B+zero) A B
  have inside := grid_inside i M (B+zero) A B (le_trans hB (le_add_right _ _)) hB hM hi
  have tag := tag_inside t zero A B U hB (le_congr (by ipra_ring) (.eqRefl _) hA) inside
  exact distance_congr (original_cell i j p M X Y D sign A B R U L N).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (cosine_factor_sample (p+N) X Y D sign (tagNumerator t) (sndT t) (T*j) N R U T hz inside.andE₂.andE₁ hN tag.andE₂
      (le_congr (mul_comm j T) (mul_comm N T) (mul_le_mul_right T hj)))

end LeanProofs.IPRA.Analysis.GaussianBinetOscillatoryMatrixCell

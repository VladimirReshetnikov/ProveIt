import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.SineKernels.GaussianBinetSineKernelGrid
import IPRADerivations.Analysis.Stirling.Binet.SecondFormula.GaussianBinetSecondWeightedSineTransposedPrefix
import IPRADerivations.Analysis.Stirling.Binet.SecondFormula.GaussianBinetSecondWeightedSineCut

/-!
# The actual transposed sine prefix and the frozen kernel rectangle

Both sums use geometric indices one through the shared prefix length.
The kernel row has the same physical frequency weight and the same
integer cutoff as the corresponding exact transposed sine row.
The pointwise comparison retains both dyadic allowances.
-/

set_option autoImplicit false
set_option maxHeartbeats 670000

namespace LeanProofs.IPRA.Analysis.GaussianBinetSineKernelPrefix

open_ipra
open GaussianBinetArctangentSineUniform (clock count)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianBinetFrozenKernelRectangle (matrix)
open GaussianBinetSineKernelGrid (errorNumerator kernelRow row_error)
open GaussianBinetSineStripCut (cutoff)
open GaussianLogGammaEulerResidualDomain (source)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalFiniteSum (sum multiplyBody multiply_body_at sum_multiply)
open GaussianRationalFubini (rowSumBody row_sum_at)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalRiemannRefinement (termsDistance sum_distance weight)
open GaussianRationalSyntheticDivision (qmul_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "L" => GaussianBinetArctangentSineUniform.cutoff
local notation "XData" => GaussianBinetSecondWeightedSineTransposedPrefix.data
local notation "XBody" => GaussianBinetSecondWeightedSineTransposedPrefix.body
local notation "Prefix" => GaussianBinetSecondWeightedSineTransposedPrefix.transposedPrefix
local notation "Rectangle" => GaussianBinetFrozenKernelRectangle.value

theorem selected_cut (q D R T K E : PTm n) :
    GaussianBinetSecondWeightedSineCut.cut q D R T K E =
      cutoff (count q D R T K) (D*L q T K) E := rfl

@[simp] theorem subst_rectangle_value {m : ℕ} (σ : Fin n → PTm m) (s k I N S cut X Y D sign R : PTm n) :
    Syn.subst σ (Rectangle s k I N S cut X Y D sign R) =
      Rectangle (Syn.subst σ s) (Syn.subst σ k) (Syn.subst σ I) (Syn.subst σ N) (Syn.subst σ S) (Syn.subst σ cut)
        (Syn.subst σ X) (Syn.subst σ Y) (Syn.subst σ D) (Syn.subst σ sign) (Syn.subst σ R) := by
  simp [GaussianBinetFrozenKernelRectangle.value,one]

private def kernelBody : PTm 2 := multiplyBody (rowSumBody matrix)

private def kernelData (s k N S cut X Y D sign R : PTm n) : PTm n :=
  pairT (weight S one N) (pairT (monus N cut) (GaussianBinetFrozenKernelRectangle.data s k N S cut X Y D sign R))

@[simp] private theorem subst_kernelData {m : ℕ} (σ : Fin n → PTm m) (s k N S cut X Y D sign R : PTm n) :
    Syn.subst σ (kernelData s k N S cut X Y D sign R) =
      kernelData (Syn.subst σ s) (Syn.subst σ k) (Syn.subst σ N) (Syn.subst σ S) (Syn.subst σ cut)
        (Syn.subst σ X) (Syn.subst σ Y) (Syn.subst σ D) (Syn.subst σ sign) (Syn.subst σ R) := by
  simp [kernelData,one]

private theorem kernel_at (i s k N S cut X Y D sign R : PTm n) :
    Γ ⊢[PRAAx] inst2 kernelBody i (kernelData s k N S cut X Y D sign R) ≐
      kernelRow i s k N S cut X Y D sign R := by
  let W := weight S one N
  let C := monus N cut
  let d := GaussianBinetFrozenKernelRectangle.data s k N S cut X Y D sign R
  exact (multiply_body_at (rowSumBody matrix) W i (pairT C d)).eqTrans
    (qmul_congr (.eqRefl _) (row_sum_at matrix i C d))

theorem prefix_error (q k I M T X Y D sign R K E : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R)
    (hS : Γ ⊢[PRAAx] le one (D*L q T K))
    (hN : Γ ⊢[PRAAx] le one (count q D R T K))
    (hE : Γ ⊢[PRAAx] le one E)
    (hmin : Γ ⊢[PRAAx] le (two*((D*L q T K)*E)) (count q D R T K))
    (hc : Γ ⊢[PRAAx] le one (cutoff (count q D R T K) (D*L q T K) E))
    (hT : Γ ⊢[PRAAx] le T (clock q D R T K+count q D R T K))
    (hM : Γ ⊢[PRAAx] le ((num 10*I+D*L q T K)*T) M)
    (hP : Γ ⊢[PRAAx] le (unit (clock q D R T K+count q D R T K)) M) :
    let s := clock q D R T K
    let N := count q D R T K
    let S := D*L q T K
    let c := cutoff N S E
    Γ ⊢[PRAAx] distanceBounded (Prefix q k I M T X Y D sign R K c)
      (Rectangle s k I N S c X Y D sign R) (I*(S*errorNumerator s I E S T)) (unit s*unit T) := by
  let s := clock q D R T K
  let N := count q D R T K
  let S := D*L q T K
  let c := cutoff N S E
  let x := XData q k M T X Y D sign R K c
  let y := kernelData s k N S c X Y D sign R
  let A := S*errorNumerator s I E S T
  let B := unit s*unit T
  have terms : Γ ⊢[PRAAx] termsDistance XBody kernelBody I x y A B := by
    refine .allI (.impI ?_)
    let t (v : PTm n) := Syn.shift v
    let j : PTm (n+1) := var 0
    let Δ := lt j (t I)::Γ.map Fm.shift
    let s' := clock (t q) (t D) (t R) (t T) (t K)
    let N' := count (t q) (t D) (t R) (t T) (t K)
    let L' := L (t q) (t T) (t K)
    let S' := t D*L'
    let c' := cutoff N' S' (t E)
    have zs : Δ ⊢[PRAAx] source (t X) (t Y) (t D) (t sign) (t R) :=
      by simpa [Δ,t,Fm.shift,Syn.shift] using hz.shift.wk
    have ss : Δ ⊢[PRAAx] le one S' := by simpa [Δ,t,S',L',Fm.shift,Syn.shift,one] using hS.shift.wk
    have ns : Δ ⊢[PRAAx] le one N' := by simpa [Δ,t,N',Fm.shift,Syn.shift,one] using hN.shift.wk
    have es : Δ ⊢[PRAAx] le one (t E) := by simpa [Δ,t,Fm.shift,Syn.shift,one] using hE.shift.wk
    have mins : Δ ⊢[PRAAx] le (two*(S'*t E)) N' :=
      by simpa [Δ,t,S',L',N',Fm.shift,Syn.shift,two] using hmin.shift.wk
    have cs : Δ ⊢[PRAAx] le one c' := by simpa [Δ,t,c',S',L',N',Fm.shift,Syn.shift,one] using hc.shift.wk
    have ts : Δ ⊢[PRAAx] le (t T) (s'+N') := by simpa [Δ,t,s',N',Fm.shift,Syn.shift] using hT.shift.wk
    have ms : Δ ⊢[PRAAx] le ((num 10*t I+S')*t T) (t M) :=
      by simpa [Δ,t,S',L',Fm.shift,Syn.shift] using hM.shift.wk
    have ps : Δ ⊢[PRAAx] le (unit (s'+N')) (t M) :=
      by simpa [Δ,t,s',N',Fm.shift,Syn.shift] using hP.shift.wk
    have first := GaussianBinetSecondWeightedSineTransposedPrefix.row_at (Γ := Δ) j (t q) (t k) (t M) (t T)
      (t X) (t Y) (t D) (t sign) (t R) (t K) c'
    have last := kernel_at (Γ := Δ) j s' (t k) N' S' c' (t X) (t Y) (t D) (t sign) (t R)
    have step := row_error j s' (t k) (t I) N' (t E) L' (t M) (t T) (t X) (t Y) (t D) (t sign) (t R)
      zs Prf.hyp0 ss ns es mins cs ts ms ps
    simpa only [Δ,t,j,x,y,A,B,s,N,S,c,s',N',L',S',c',Syn.shift,subst_kernelData,
      GaussianBinetSecondWeightedSineTransposedPrefix.subst_data,GaussianBinetArctangentSineUniform.subst_clock,
      GaussianBinetArctangentSineUniform.subst_count,GaussianBinetArctangentSineUniform.subst_cutoff,
      GaussianBinetSineStripCut.subst_cutoff,GaussianBinetSineKernelGrid.subst_errorNumerator,
      GaussianCoefficientNameBounds.subst_unit,PTm.subst_mul] using
      distance_congr first.eqSymm last.eqSymm (.eqRefl _) (.eqRefl _) step
  have exactly : Γ ⊢[PRAAx] sum kernelBody I y ≐ Rectangle s k I N S c X Y D sign R :=
    sum_multiply (rowSumBody matrix) (weight S one N) I (pairT (monus N c) (GaussianBinetFrozenKernelRectangle.data s k N S c X Y D sign R))
  exact distance_congr (.eqRefl _) exactly (.eqRefl _) (.eqRefl _)
    (sum_distance XBody kernelBody I x y A B (positive_product _ _ (unit_positive s) (unit_positive T)) terms)

theorem actual_Binet_transposed_to_frozen_kernel_prefix_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 12
      (let q := var 0
       let k := var 1
       let I := var 2
       let M := var 3
       let T := var 4
       let X := var 5
       let Y := var 6
       let D := var 7
       let sign := var 8
       let R := var 9
       let K := var 10
       let E := var 11
       let s := clock q D R T K
       let N := count q D R T K
       let S := D*L q T K
       let c := cutoff N S E
       (source X Y D sign R ⋏ (le one S ⋏ (le one N ⋏ le one E))) ⋏
         ((le (two*(S*E)) N ⋏ le one c) ⋏
           (le T (s+N) ⋏ (le ((num 10*I+S)*T) M ⋏ le (unit (s+N)) M))) ⟶
         distanceBounded (Prefix q k I M T X Y D sign R K c)
           (Rectangle s k I N S c X Y D sign R) (I*(S*errorNumerator s I E S T)) (unit s*unit T)) :=
  closeUniv 12 (.impI (prefix_error _ _ _ _ _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁.andE₁ Prf.hyp0.andE₁.andE₂.andE₁ Prf.hyp0.andE₁.andE₂.andE₂.andE₁
    Prf.hyp0.andE₁.andE₂.andE₂.andE₂ Prf.hyp0.andE₂.andE₁.andE₁ Prf.hyp0.andE₂.andE₁.andE₂
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBinetSineKernelPrefix

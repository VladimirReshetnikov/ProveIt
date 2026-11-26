import IPRADerivations.Analysis.Gamma.Zeta.Mellin.EndpointBounds.GaussianGammaZetaMellinUpperPoint
import IPRADerivations.Analysis.Gamma.Zeta.Mellin.Compact.GaussianGammaZetaMellinGrid
import IPRADerivations.Analysis.SpecialFunctions.DampingPower.GaussianNamedDampingPowerReciprocalTail

/-!
# Uniform upper tail of the original Mellin quadrature

On any panel starting at a/E ≥ 1, use the actual left mesh of step
1/(E*N). A scalar reciprocal-square majorant telescopes uniformly in
the panel's length and the refinement count.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinUpperGrid

open_ipra
open GaussianCompactRiemannName (quadrature sampleBody sampleData sample_body_at grid)
open GaussianEulerUpperPowerCoefficients (source subst_source)
open GaussianGammaZetaMellinGrid (evaluatorF fixedData sample_at subst_fixedData)
open GaussianGammaZetaMellinUpperPoint (coefficientBound degree upper_observation_bound)
open GaussianNamedDampingPowerReciprocalTail (body gridData subst_gridData affine_grid_majorant quadrature_bound_of_majorized)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalSumMajorant (majorized termsMajorized)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem cell_majorant (i p N z R B a C E : PTm n)
    (h : Γ ⊢[PRAAx] source z R B) (hE : Γ ⊢[PRAAx] le one E) (ha : Γ ⊢[PRAAx] le E a)
    (hC : Γ ⊢[PRAAx] le one C) (hN : Γ ⊢[PRAAx] le one N) (hp : Γ ⊢[PRAAx] le (degree R) p) :
    Γ ⊢[PRAAx] majorized
      (inst2 (sampleBody evaluatorF) i (sampleData p (C*N) a C E (fixedData z B)))
      (inst2 body i (gridData (coefficientBound R) a E N)) := by
  let M := C*N
  let x := a*M+C*i
  let y := E*M
  let K := coefficientBound R
  let t := grid i M a C E
  have hy := positive_product E M hE (positive_product _ _ hC hN)
  have time : Γ ⊢[PRAAx] le y x := le_trans (mul_le_mul_right M ha) (le_add_right _ _)
  have hx := le_trans hy time
  have support : Γ ⊢[PRAAx] GaussianEulerUpperPowerOrder.source z R B x y :=
    .andI h (.andI (.andI hx hy) time)
  have raw := upper_observation_bound p z R B x y support hp
  have read := (sample_body_at (Γ := Γ) evaluatorF i p M a C E (fixedData z B)).eqTrans (sample_at p z B x y)
  exact affine_grid_majorant i K a C E N x y (le_trans hE ha) hC hN hx
    (.andI (fst_pair _ _) (snd_pair _ _)) read (bound_congr (.eqRefl _) (by ipra_ring) (.eqRefl _) raw)

theorem upper_grid_bound (p N z R B a C E : PTm n)
    (h : Γ ⊢[PRAAx] source z R B) (hE : Γ ⊢[PRAAx] le one E) (ha : Γ ⊢[PRAAx] le E a)
    (hC : Γ ⊢[PRAAx] le one C) (hN : Γ ⊢[PRAAx] le one N) (hp : Γ ⊢[PRAAx] le (degree R) p) :
    Γ ⊢[PRAAx] bounded (quadrature evaluatorF p (C*N) a C E (fixedData z B))
      (two*coefficientBound R*E) a := by
  let M := C*N
  let f := sampleBody evaluatorF
  let X := sampleData p M a C E (fixedData z B)
  let Y := gridData (coefficientBound R) a E N
  have ha' := le_trans hE ha
  have rows : Γ ⊢[PRAAx] termsMajorized f body M X Y := by
    refine .allI (.impI ?_)
    let s (t : PTm n) := Syn.shift t
    let i : PTm (n+1) := var 0
    let Δ := lt i (s C*s N)::Γ.map Fm.shift
    have hz : Δ ⊢[PRAAx] source (s z) (s R) (s B) := by simpa [Δ,s,Fm.shift,Syn.shift] using h.shift.wk
    have e : Δ ⊢[PRAAx] le one (s E) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hE.shift.wk
    have a' : Δ ⊢[PRAAx] le (s E) (s a) := by simpa [Δ,s,Fm.shift,Syn.shift] using ha.shift.wk
    have c : Δ ⊢[PRAAx] le one (s C) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hC.shift.wk
    have ns : Δ ⊢[PRAAx] le one (s N) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hN.shift.wk
    have p' : Δ ⊢[PRAAx] le (degree (s R)) (s p) := by simpa [Δ,s,Fm.shift,Syn.shift] using hp.shift.wk
    simpa only [f,X,Y,M,Δ,i,s,Syn.shift,GaussianCompactRiemannName.subst_sampleData,subst_fixedData,
      subst_gridData,GaussianGammaZetaMellinUpperPoint.subst_coefficientBound,PTm.subst_mul] using
      cell_majorant (var 0) (s p) (s N) (s z) (s R) (s B) (s a) (s C) (s E) hz e a' c ns p'
  exact quadrature_bound_of_majorized evaluatorF p (coefficientBound R) a a C E N _ ha' hC hE hN rows

theorem actual_Mellin_upper_grid_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (let p := var 0
     let N := var 1
     let z := var 2
     let R := var 3
     let B := var 4
     let a := var 5
     let C := var 6
     let E := var 7
     (source z R B ⋏ (le one E ⋏ (le E a ⋏ (le one C ⋏ (le one N ⋏ le (degree R) p))))) ⟶
       bounded (quadrature evaluatorF p (C*N) a C E (fixedData z B)) (two*coefficientBound R*E) a) :=
  closeUniv 8 (.impI (upper_grid_bound _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinUpperGrid

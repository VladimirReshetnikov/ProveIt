import IPRADerivations.Analysis.Stirling.Binet.Laplace.Moments.DerivativeQuotients.GaussianBinetLaplaceMomentMarginRows
import IPRADerivations.Analysis.Stirling.Binet.Laplace.Moments.Improper.GaussianBinetLaplaceMomentTail
import IPRADerivations.Analysis.SpecialFunctions.DampingPower.GaussianNamedDampingPowerReciprocalTail
import IPRADerivations.Analysis.Stirling.Binet.Laplace.Strips.GaussianBinetLaplaceStripCutoff

/-!
# Uniform positive-margin tails of the actual Binet quadrature

Late compact observations absorb the row error into an inverse-square
majorant at a fixed lower chart. Its original affine left grid gives
a bound independent of the right endpoint and of the input denominator.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentMarginTail

open_ipra
open GaussianBinetLaplaceMomentTail (cell_majorant_of_observation name_bound_of_late_grid)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianBinetLaplaceMomentCompact (data)
open GaussianBinetLaplaceMomentDecay (tailScale)
open GaussianBinetLaplaceMomentMarginRows (allowance observation_inverse_square_bound)
open GaussianBinetLaplaceMomentFloor (evaluatorF fixedData gain nameF)
open GaussianBinetLaplaceStrip (source)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (quadrature sampleBody sampleData precision mesh)
open GaussianNamedDampingPowerReciprocalTail (body gridData subst_gridData quadrature_bound_of_majorized)
open GaussianRationalMetric (bounded)
open GaussianRationalSumMajorant (majorized termsMajorized)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

def coefficient (j K : PTm n) : PTm n := tailScale j K+num 30

ipra_subst coefficient

private theorem cell_majorant (i p N j X D R K T A C E : PTm n)
    (h : Γ ⊢[PRAAx] source X zero D zero R T A C E)
    (hK : Γ ⊢[PRAAx] le one K) (hmargin : Γ ⊢[PRAAx] le D (K*X)) (hA : Γ ⊢[PRAAx] le one A)
    (hC : Γ ⊢[PRAAx] le one C) (hN : Γ ⊢[PRAAx] le one N)
    (hq : Γ ⊢[PRAAx] le ((T*T)*(one+pw T j)) (unit p)) (hi : Γ ⊢[PRAAx] lt i (C*N)) : Γ ⊢[PRAAx]
    majorized (inst2 (sampleBody evaluatorF) i (sampleData p (C*N) (E+A) C E (fixedData j X D R T)))
      (inst2 body i (gridData (coefficient j K) A E N)) := by
  have pad : Γ ⊢[PRAAx] le (allowance j T) (num 30*(one+pw T j)) := by
    unfold allowance
    ipra_le 26+4*𝔞(pw T j)
  have pay : Γ ⊢[PRAAx] le (allowance j T*(T*T)) (num 30*unit p) :=
    le_trans (le_mul_mono pad (le_refl _))
      (le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono (le_refl _) hq))
  exact cell_majorant_of_observation i p N j X D R T A C E (tailScale j K) (allowance j T) (num 30)
    h hA hC hN hi pay (fun a b ha hb time =>
      observation_inverse_square_bound p j X D R K T a b (.andI h.andE₁ (.andI hb time)) hK hmargin ha)

theorem upper_tail_bound (p N j X D R K T A C E : PTm n)
    (h : Γ ⊢[PRAAx] source X zero D zero R T A C E)
    (hK : Γ ⊢[PRAAx] le one K) (hmargin : Γ ⊢[PRAAx] le D (K*X)) (hA : Γ ⊢[PRAAx] le one A)
    (hC : Γ ⊢[PRAAx] le one C) (hN : Γ ⊢[PRAAx] le one N) (hq : Γ ⊢[PRAAx] le ((T*T)*(one+pw T j)) (unit p)) :
    Γ ⊢[PRAAx] bounded (quadrature evaluatorF p (C*N) (E+A) C E (fixedData j X D R T))
      (two*coefficient j K*E) A := by
  let M := C*N
  let f := sampleBody evaluatorF
  let x := sampleData p M (E+A) C E (fixedData j X D R T)
  let y := gridData (coefficient j K) A E N
  have rows : Γ ⊢[PRAAx] termsMajorized f body M x y := by
    refine .allI (.impI ?_)
    let s (v : PTm n) := Syn.shift v
    let Δ := lt (var 0) (s C*s N) :: Γ.map Fm.shift
    have hs : Δ ⊢[PRAAx] source (s X) zero (s D) zero (s R) (s T) (s A) (s C) (s E) := by
      simpa only [Δ,s,Fm.shift,Syn.shift,GaussianBinetLaplaceStrip.subst_source,ConciseIPRA.PTm.subst_zero] using h.shift.wk
    have a : Δ ⊢[PRAAx] le one (s A) := (Order.shift_one_le hA).wk
    have c : Δ ⊢[PRAAx] le one (s C) := (Order.shift_one_le hC).wk
    have ns : Δ ⊢[PRAAx] le one (s N) := (Order.shift_one_le hN).wk
    have ks : Δ ⊢[PRAAx] le one (s K) := (Order.shift_one_le hK).wk
    have ms : Δ ⊢[PRAAx] le (s D) (s K*s X) := by
      simpa only [Δ,s,Fm.shift,Syn.shift,subst_le,PTm.subst_mul] using hmargin.shift.wk
    have q : Δ ⊢[PRAAx] le ((s T*s T)*(one+pw (s T) (s j))) (unit (s p)) := by
      simpa [Δ,s,Fm.shift,Syn.shift,one] using hq.shift.wk
    simpa only [f,x,y,M,Δ,s,Syn.shift,GaussianCompactRiemannName.subst_sampleData,
      GaussianBinetLaplaceMomentFloor.subst_fixedData,subst_gridData,subst_coefficient,PTm.subst_add,PTm.subst_mul] using
      cell_majorant (var 0) (s p) (s N) (s j) (s X) (s D) (s R) (s K) (s T) (s A) (s C) (s E) hs ks ms a c ns q Prf.hyp0
  exact quadrature_bound_of_majorized evaluatorF p (coefficient j K) A (E+A) C E N _
    hA hC h.andE₂.andE₁ hN rows

theorem name_bound (p j X D R K T A C E : PTm n)
    (h : Γ ⊢[PRAAx] source X zero D zero R T A C E)
    (hK : Γ ⊢[PRAAx] le one K) (hmargin : Γ ⊢[PRAAx] le D (K*X))
    (hA : Γ ⊢[PRAAx] le one A) (hC : Γ ⊢[PRAAx] le one C) :
    Γ ⊢[PRAAx] bounded (ap2 nameF p (data j X D R T A C E))
      (A+(two*coefficient j K*E)*unit p) (unit p*A) := by
  let L := gain j R T
  let M := mesh p L T
  let q := GaussianFastValueCut.exponent ((T*T)*(one+pw T j)) (precision p T)
  have hq : Γ ⊢[PRAAx] le (precision p T) q := le_add_right _ _
  have budget : Γ ⊢[PRAAx] le ((T*T)*(one+pw T j)) (unit q) :=
    le_trans (le_congr (by ipra_ring) (.eqRefl _)
      (le_mul_mono (le_refl ((T*T)*(one+pw T j))) (unit_positive (precision p T)))) (GaussianFastValueCut.query_budget _ _)
  exact name_bound_of_late_grid p q j X D R T A C E _ h hA hC hq
    (upper_tail_bound q M j X D R K T A C E h hK hmargin hA hC
      (GaussianCompactRiemannName.mesh_positive p L T) budget)

theorem actual_weighted_Binet_margin_tail_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (let p := var 0
     let j := var 1
     let X := var 2
     let D := var 3
     let R := var 4
     let K := var 5
     let T := var 6
     let A := var 7
     let C := var 8
     let E := var 9
     source X zero D zero R T A C E ⟶ (le one K ⋏ le D (K*X)) ⟶ (le one A ⋏ le one C) ⟶
       bounded (ap2 nameF p (data j X D R T A C E)) (A+(two*coefficient j K*E)*unit p) (unit p*A)) :=
  closeUniv 10 (.impI (.impI (.impI (name_bound _ _ _ _ _ _ _ _ _ _ hyp2 Prf.hyp1.andE₁ Prf.hyp1.andE₂
    Prf.hyp0.andE₁ Prf.hyp0.andE₂))))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentMarginTail

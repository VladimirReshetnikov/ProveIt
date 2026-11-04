import Absorb88Signs
import Absorb88NegativeTransportBound

/-! Unchecked draft: bind the negative transport bound to an 88 graph zero. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace Absorb88NegativeTransportGraph
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency FreeJAbsorb88 Absorb88First Absorb88FirstQuotient
open Absorb88Transport Absorb88Signs Absorb88NegativeTransportBound
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open ArithmeticAdaptiveTransport2011 ModelDifferenceRing
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_negative_transport_bound (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hb : 0 < (p 0 : V)) (hv : ∀ j, 0 < v j)
    (hz : InternalZero (graph (integerPorts p)).output v) :
    let b : V := v 0 * (p 0 : V)
    let q : V := 1 + b
    let X : V := q * v 5
    let Y : V := (q * (q*q)) * v 6
    let Q : V := (X*Y)*Y
    let A : V := (p 1 : V) + v 5
    let Bp : V := q*A
    let Bn : V := (v 1+v 2)*A+v 1
    (ι Bp : DiffRing V) < ι Bn →
      (ι q : DiffRing V) * (ι Bn - ι Bp) ≤ ι Q := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let X : V := q*v 5
  let Y : V := (q*(q*q))*v 6
  let k : V := v 8+v 9
  let Q : V := (X*Y)*Y
  let W : V := 1+k*b
  let A : V := (p 1:V)+v 5
  let Bp : V := q*A
  let Bn : V := (v 1+v 2)*A+v 1
  let zp : Pair V := (b*(v 7)+Bn*(W*q),Bp*(W*q))
  change (ι Bp : DiffRing V) < ι Bn →
    (ι q : DiffRing V) * (ι Bn - ι Bp) ≤ ι Q
  intro hneg
  have hb0 : 0<b := mul_pos (hv 0) hb
  obtain ⟨first,hfirst,hroot,hnorm⟩ := first_root p v hz hb0
  have hmag : magnitude zp=b*first := by
    have he := magnitude_equivalent (root_rep p v)
    exact he.symm.trans hroot
  have hs := magnitude_cases zp.1 zp.2 (b*first) hmag
  have hB : (0 : DiffRing V) < ι b := by
    rw [← map_zero ι, ι_lt_ι]; exact hb0
  have hR : (0 : DiffRing V) < ι (v 7) := by
    rw [← map_zero ι, ι_lt_ι]; exact hv 7
  have hQ : (0 : DiffRing V) ≤ ι Q := ι_nonneg _
  have hk : (1 : DiffRing V) ≤ ι k := by
    apply one_le_of_pos (fun _ h => pos_iff_one_le.mp h)
    rw [← map_zero ι, ι_lt_ι]
    exact add_pos (hv 8) (hv 9)
  have hF : (0 : DiffRing V) ≤ ι first := ι_nonneg _
  have hU : (0 : DiffRing V) < (ι q : DiffRing V) * (ι Bn - ι Bp) := by
    have hq : (0 : DiffRing V) < ι q := by
      rw [← map_zero ι, ι_lt_ι]
      dsimp [q]; exact add_pos_of_pos_of_nonneg (by simp) (by simp)
    exact mul_pos hq (sub_pos.mpr hneg)
  have hN : (ι first : DiffRing V) * ι first =
      1 + ((ι Q : DiffRing V)*ι k) * ((ι Q : DiffRing V)*ι k+ι k) := by
    change first*first=1+Q*(Q+1)*k*k at hnorm
    have hh := congrArg (fun x : V => (ι x : DiffRing V)) hnorm
    simp only [map_add,map_mul,map_one] at hh
    nlinarith [hh]
  have hfirsteq : (ι b : DiffRing V)*ι (v 7) +
      ((ι b : DiffRing V)*ι k+1) * ((ι q : DiffRing V)*(ι Bn-ι Bp)) =
      (ι b : DiffRing V)*ι first := by
    rcases hs with hp | hn
    · have hh := congrArg (fun x : V => (ι x : DiffRing V)) hp
      dsimp only [zp,W] at hh
      simp only [map_add,map_mul,map_one] at hh
      nlinarith
    · have hh := congrArg (fun x : V => (ι x : DiffRing V)) hn
      dsimp only [zp,W] at hh
      simp only [map_add,map_mul,map_one] at hh
      have hbr := mul_pos hB hR
      have hpos : (0 : DiffRing V) < ((ι b : DiffRing V)*ι k+1) * ((ι q : DiffRing V)*(ι Bn-ι Bp)) := by positivity
      nlinarith
  exact negative_transport_le _ _ _ _ _ _
    (fun _ h => one_le_of_pos (fun _ h => pos_iff_one_le.mp h) h)
    hQ hk hF hB hR hU hN hfirsteq

#print axioms Absorb88NegativeTransportGraph.graph_negative_transport_bound
end Absorb88NegativeTransportGraph

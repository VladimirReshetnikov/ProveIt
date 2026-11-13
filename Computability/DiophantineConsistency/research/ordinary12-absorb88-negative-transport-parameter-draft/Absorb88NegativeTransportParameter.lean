import Absorb88NegativeTransportGraph

/-! Draft: bounds on negative-branch transport parameters. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace Absorb88NegativeTransportParameter

theorem parameter_bound {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] (q F alpha A U P : R)
    (hq : 0 < q) (hF : 0 ≤ F) (hA : 1 ≤ A) (hU : 0 ≤ U)
    (hshape : U = q*((F+alpha-q)*A+F)) (hbound : U ≤ P) :
    q*(F+alpha) ≤ P+q*q := by
  by_cases hD : 0 ≤ F+alpha-q
  · have hd := mul_nonneg (mul_nonneg hq.le hD) (show 0 ≤ A-1 by linarith)
    have hf := mul_nonneg hq.le hF
    nlinarith
  · have hd : q*(F+alpha-q) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hq.le (le_of_not_ge hD)
    nlinarith

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency FreeJAbsorb88 Absorb88First
open AdaptiveEquationSyntax2011 ModelDifferenceRing
open Absorb88NegativeTransportGraph

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_negative_transport_parameter_bound
    (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hb : 0 < (p 0 : V)) (hv : ∀ j, 0 < v j)
    (hz : InternalZero (graph (integerPorts p)).output v) :
    let b : V := v 0 * (p 0 : V)
    let q : V := 1 + b
    let X : V := q * v 5
    let Y : V := (q * (q*q)) * v 6
    let P : V := (X*Y)*Y
    let A : V := (p 1 : V) + v 5
    let Bp : V := q*A
    let Bn : V := (v 1+v 2)*A+v 1
    (ι Bp : DiffRing V) < ι Bn →
      (ι q : DiffRing V) * (ι (v 1) + ι (v 2)) ≤ ι P + ι q * ι q := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let X : V := q*v 5
  let Y : V := (q*(q*q))*v 6
  let P : V := (X*Y)*Y
  let A : V := (p 1:V)+v 5
  let Bp : V := q*A
  let Bn : V := (v 1+v 2)*A+v 1
  change (ι Bp : DiffRing V) < ι Bn →
    (ι q : DiffRing V) * (ι (v 1) + ι (v 2)) ≤ ι P + ι q * ι q
  intro hn
  have hQ : (0 : DiffRing V) < ι q := by
    rw [← map_zero ι, ι_lt_ι]
    dsimp [q]; exact add_pos_of_pos_of_nonneg (by simp) (by simp)
  have hA : (1 : DiffRing V) ≤ ι A := by
    apply one_le_of_pos (fun _ h => pos_iff_one_le.mp h)
    rw [← map_zero ι, ι_lt_ι]
    exact add_pos_of_nonneg_of_pos (by simp) (hv 5)
  have hU : (0 : DiffRing V) ≤ ι q * (ι Bn - ι Bp) :=
    (mul_pos hQ (sub_pos.mpr hn)).le
  have hshape : (ι q : DiffRing V) * (ι Bn - ι Bp) =
      ι q * ((ι (v 1)+ι (v 2)-ι q)*ι A+ι (v 1)) := by
    dsimp only [Bp,Bn]
    simp only [map_add,map_mul]
    ring
  have hbound := graph_negative_transport_bound p v hb hv hz hn
  exact parameter_bound (ι q) (ι (v 1)) (ι (v 2)) (ι A) _ _
    hQ (ι_nonneg _) hA hU hshape hbound

#print axioms Absorb88NegativeTransportParameter.parameter_bound
#print axioms Absorb88NegativeTransportParameter.graph_negative_transport_parameter_bound
end Absorb88NegativeTransportParameter

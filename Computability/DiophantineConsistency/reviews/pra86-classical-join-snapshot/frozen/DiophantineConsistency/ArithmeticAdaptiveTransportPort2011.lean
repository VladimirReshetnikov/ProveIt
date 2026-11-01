import DiophantineConsistency.ArithmeticAdaptiveTransportScalar2011
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveTransportPort2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticAdaptiveTransportQuotient2011 ArithmeticAdaptiveTransportScalar2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem restore_at (p : Fin 4 → ℕ) (v : Fin 13 → V) (w : V)
    (hq : 1<1+v 0*(p 0:V)) (hX : v 6=(1+v 0*(p 0:V))*w)
    (ht : TransportQuotient p v) :
    let q : V := 1+v 0*(p 0:V)
    ∃ z : V, 0<z ∧
      q*((p 1:V)+w)=(v 1+v 2)*((p 1:V)+w)+v 1+(q-1)*z := by
  let q : V := 1+v 0*(p 0:V)
  have hbq : q-1=v 0*(p 0:V) := by dsimp [q]; rw [add_comm]; simp
  obtain ⟨j,hj,hjt⟩ := ht
  change q*(v 6+(p 1:V)*q)=(v 1+v 2)*(v 6+(p 1:V)*q)+v 1*q+(v 0*(p 0:V))*j at hjt
  rw [←hbq] at hjt
  obtain ⟨z,hz,_,he⟩ := normalize_transport q (v 6) (p 1:V) (v 1) (v 2) w j hq hj hX hjt
  exact ⟨z,hz,he⟩
end DiophantineConsistency.ArithmeticAdaptiveTransportPort2011

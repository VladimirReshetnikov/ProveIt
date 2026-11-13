import DiophantineConsistency.Compact44.FreeJExactOrdinary
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FreeJExactTransport
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.AdaptiveEquationSyntax2011
open DiophantineConsistency.ArithmeticPellRecurrence
open DiophantineConsistency.ArithmeticPellCongruences
open DiophantineConsistency.Ordinary12FreeJ
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem first_quotient (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀ j,0<v j) (hz : InternalZero (literal (fun j => (p j:ℤ))) v) :
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    ∃ t : V, v 8+v 9=R+1+4*((v 5*v 6)*v 6)*t := by
  let q : V := 1+v 0*(p 0:V)
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  let Q : V := (v 5*v 6)*v 6
  let B : V := 2*(Q-1)+1
  obtain ⟨first,main,j,pi,hfirst,hmain,hj13,hjpi,hpiR,hjR1,hjx,hjy,hpx,hpy⟩ :=
    FreeJExactOrdinary.exact_ordinary_indices p v hb hl hh hv hz
  have hQ : 0<Q := mul_pos (mul_pos (hv 5) (hv 6)) (hv 6)
  have hQ1 : Q-1+1=Q := tsub_add_cancel_of_le (pos_iff_one_le.mp hQ)
  have hB : B+1=2*Q := by
    dsimp [B]
    calc
      2*(Q-1)+1+1=2*(Q-1+1) := by ring
      _=2*Q := by rw [hQ1]
  exact first_transport j B Q R (v 8+v 9) hB hjy.symm hjR1.symm
end FreeJExactTransport
#print axioms FreeJExactTransport.first_quotient

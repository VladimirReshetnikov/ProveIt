import Trace74N2OddThree

/-! UNCHECKED DRAFT. Exact signed eta identity for the same small-k graph zero. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74N2EtaIdentity
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 ArithmeticPellRecurrence
open Trace75Factors Trace74Pell Trace74N2OddThree
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_eta_identity (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j)) = 0)
    (hsmall : k v=8*firstParam p v+4) :
    (ι (v 8):DiffRing V)+4*(ι (Y p v))^2*
      (2*ι (X p v)*ι (Y p v)-(ι (X p v)+1)^2) =
        8*ι (Y p v)*ι (X p v)+4*ι (Y p v)+3 := by
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hY : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hX : 0<X p v := mul_pos (hv 5) hq
  have hApos : 0<A p v := by
    change 0<X p v*Y p v+Y p v
    exact add_pos (mul_pos hX hY) hY
  have hA1 : A p v-1+1=A p v := tsub_add_cancel_of_le (pos_iff_one_le.mp hApos)
  have hA2 : A p v-1+2=A p v+1 := by
    calc
      A p v-1+2=(A p v-1+1)+1 := by ring
      _=A p v+1 := by rw [hA1]
  have hc := graph_small_k_odd_three p v hb hv hz hsmall
  have hy := Trace74OddOrdinateBound.ordinate_three (A p v-1)
  rw [hA2,←hc] at hy
  have hA : A p v=Y p v*(X p v+1) := by dsimp [A]; ring
  have hcform : c p v=k v*Y p v+v 8 := rfl
  rw [hcform,hsmall,hA] at hy
  have hi := congrArg (ι : V →+* DiffRing V) hy
  simp only [map_add,map_mul,map_pow,map_one,map_ofNat] at hi
  dsimp [firstParam] at hi
  simp only [map_mul] at hi
  linear_combination hi

#print axioms Trace74N2EtaIdentity.graph_eta_identity
end Trace74N2EtaIdentity

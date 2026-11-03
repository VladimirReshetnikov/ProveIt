import Trace74Pell
import DiophantineConsistency.ArithmeticPellCongruences

/-! UNCHECKED DRAFT: the first Pell index residue from a positive trace74 zero,
without rank identification or the reverse mask guard. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74FirstIndexResidue
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open ArithmeticPellRecurrence ArithmeticPellCongruences
open Trace75Factors Trace74Pell
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_first_index_residue (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j)) = 0) :
    ∃ n : V, 0<n ∧ 2*ycoord n (2*(firstParam p v-1)+1)=k v ∧
      k v%(q p v)^4=(2*n)%(q p v)^4 := by
  let P : V := firstParam p v
  let M : V := (q p v)^4
  let B : V := 2*(P-1)+1
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hY : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hX : 0<X p v := mul_pos (hv 5) hq
  have hM : 0<M := pow_pos hq 4
  have hP : 0<P := mul_pos hX (mul_pos hY hY)
  have hP1 : P-1+1=P := tsub_add_cancel_of_le (pos_iff_one_le.mp hP)
  have hdiv : M∣B+1 := by
    refine ⟨2*v 5*(q p v)^3*v 6*v 6,?_⟩
    calc
      B+1=2*(P-1+1) := by dsimp [B]; ring
      _=2*P := by rw [hP1]
      _=M*(2*v 5*(q p v)^3*v 6*v 6) := by dsimp [M,P,firstParam,X,Y]; ring
  obtain ⟨_tau,_f,n,_I,_ht,_hf,hn,_hnK,_hE,_hf2,_hnx,hny,_hIeq,_hIpos,_hstrong,_hQ,_hC⟩ :=
    Trace74Pell.first_and_doubled p v hb hv hz
  change 2*ycoord n B=k v at hny
  obtain ⟨_r,s,_hx,hys⟩ := residue_quotients n B M hdiv
  have hk : k v=2*n+M*(2*s) := by rw [←hny,hys]; ring
  have hmod : k v%M=(2*n)%M := by rw [hk,mod_add_mul' _ _ hM]
  exact ⟨n,hn,hny,hmod⟩

#print axioms Trace74FirstIndexResidue.graph_first_index_residue
end Trace74FirstIndexResidue

import Direct80FirstIndexCongruence
import Direct80Pell

/-! The first Pell index has the same residue as the main graph rank. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TenPositive80FirstIndexResidue
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011
open ArithmeticPellRecurrence ArithmeticPellCongruences
open TenPositive80Graph TenPositive80Factors TenPositive80NaturalRank TenPositive80Pell TenPositive80FirstIndexCongruence
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_first_index_residue (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : InternalZero (graph (integerPorts p)).output v)
    (hbeta : ∃u : V, (p 0:V)=2*u+1) :
    ∃ n : V, 0<n ∧
      2*ycoord n (2*(firstParam p v-1)+1)=k v ∧
      (2*n)%(mu p v*mu p v)=(rankNat p v+1)%(mu p v*mu p v) := by
  let P : V := firstParam p v
  let M : V := mu p v*mu p v
  let B : V := 2*(P-1)+1
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hY : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hX : 0<X p v := mul_pos (hv 5) hq
  have hmu : 0<mu p v := add_pos (mul_pos hq hq) (by simp)
  have hM : 0<M := mul_pos hmu hmu
  have hP : 0<P := mul_pos hX (mul_pos (mul_pos hmu hY) (mul_pos hmu hY))
  have hP1 : P-1+1=P := tsub_add_cancel_of_le (pos_iff_one_le.mp hP)
  have hdiv : M∣B+1 := by
    refine ⟨2*X p v*Y p v*Y p v,?_⟩
    calc
      B+1=2*(P-1+1) := by dsimp [B]; ring
      _=2*P := by rw [hP1]
      _=M*(2*X p v*Y p v*Y p v) := by dsimp [M,P,firstParam]; ring
  obtain ⟨_tau,_f,n,_I,_ht,_hf,hn,_hnK,_hE,_hf2,_hnx,hny,_hIeq,_hIpos,_hstrong,_hQ,_hdiv⟩ :=
    first_and_doubled p v hb hv hz
  change 2*ycoord n B=k v at hny
  obtain ⟨_r,s,_hx,hys⟩ := residue_quotients n B M hdiv
  have hk : k v=2*n+M*(2*s) := by rw [←hny,hys]; ring
  have hmod : k v%M=(2*n)%M := by rw [hk,mod_add_mul' _ _ hM]
  have hcong := graph_first_index_congruence p v hb hl hh hv hz hbeta
  exact ⟨n,hn,hny,hmod.symm.trans hcong⟩

#print axioms TenPositive80FirstIndexResidue.graph_first_index_residue
end TenPositive80FirstIndexResidue

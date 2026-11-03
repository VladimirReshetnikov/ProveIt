import Direct80GraphPower
import DiophantineConsistency.ArithmeticRadixAlignment

/-! Internal radix/block alignment from the recovered 80 graph power. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Direct80RadixAlignment
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ArithmeticRadixAlignment
open TenPositive80Graph TenPositive80Factors TenPositive80NaturalRank
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_radix_alignment (p : Fin 4 → ℕ) (v : Fin 10 → V) (d : V)
    (hbeta31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : InternalZero (graph (integerPorts p)).output v)
    (hbetaodd : ∃u : V, (p 0:V)=2*u+1) (hd : 2≤d)
    (hbeta : (p 0:V)+1=Exp.exp d) :
    ∃ N : V, 0<N ∧ q p v=Exp.exp (d*N) ∧ d*N≤rankNat p v ∧
      v 5=Exp.exp (rankNat p v-d*N) := by
  have hx := Direct80GraphPower.graph_power p v hbeta31 hl hh hv hz hbetaodd
  have hpred : Exp.exp d-1=(p 0:V) := by rw [←hbeta]; simp
  have he : Exp.exp (rankNat p v)=v 5*((Exp.exp d-1)*v 0+1) := by
    rw [hpred,←hx]
    rfl
  obtain ⟨_,N,hN,hq,hbound,hrest⟩ := factor_alignment d (v 0) (rankNat p v) (v 5) hd (hv 0) he
  have hqdef : q p v=(Exp.exp d-1)*v 0+1 := by rw [hpred]; rfl
  refine ⟨N,hN,?_,hbound,hrest⟩
  rw [hqdef]
  exact hq

#print axioms Direct80RadixAlignment.graph_radix_alignment
end Direct80RadixAlignment

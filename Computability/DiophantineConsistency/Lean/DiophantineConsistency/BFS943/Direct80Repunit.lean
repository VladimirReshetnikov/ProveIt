import DiophantineConsistency.BFS943.Direct80RadixAlignment
import DiophantineConsistency.ArithmeticRepunit

/-! Bind the positive graph's radix exponent to its actual repunit witness. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Direct80Repunit
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ArithmeticRepunit
open TenPositive80Graph TenPositive80Factors TenPositive80NaturalRank
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_repunit (p : Fin 4 → ℕ) (v : Fin 10 → V) (d : V)
    (hbeta31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : InternalZero (graph (integerPorts p)).output v)
    (hbetaodd : ∃u : V, (p 0:V)=2*u+1) (hd : 2≤d)
    (hbeta : (p 0:V)+1=Exp.exp d) :
    ∃ N : V, 0<N ∧ v 0=rep d N ∧ q p v=Exp.exp (d*N) ∧ d*N≤rankNat p v ∧
      v 5=Exp.exp (rankNat p v-d*N) := by
  obtain ⟨N,hN,hq,hbound,hrest⟩ :=
    Direct80RadixAlignment.graph_radix_alignment p v d hbeta31 hl hh hv hz hbetaodd hd hbeta
  have hpred : Exp.exp d-1=(p 0:V) := by rw [←hbeta]; simp
  have hidentity : (Exp.exp d-1)*v 0+1=Exp.exp (d*N) := by
    rw [hpred]
    exact hq
  have hj : v 0=rep d N := eq_rep_of_identity (lt_of_lt_of_le (by norm_num : (0:V)<2) hd) hidentity
  exact ⟨N,hN,hj,hq,hbound,hrest⟩

#print axioms Direct80Repunit.graph_repunit
end Direct80Repunit

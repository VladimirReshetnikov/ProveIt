import Direct80GraphPower
import Direct80SymbolicPortBounds

/-! Specialize the graph power recovery to explicit symbolic port equalities. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace TenPositive80FixedSymbolicPower
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 CompactFixedBeta CompactSymbolicPorts
open TenPositive80Graph TenPositive80Factors TenPositive80NaturalRank TenPositive80RankExact
open TenPositive80IndexAlignment TenPositive80SymbolicPortBounds Direct80GraphPower
attribute [local irreducible] CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem fixed_symbolic_power (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hp0 : p 0=betaNat) (hp2 : p 2=lowNat) (hp3 : p 3=betaNat+highNat)
    (hv : ∀j,0<v j) (hz : InternalZero (graph (integerPorts p)).output v) :
    X p v=Exp.exp (rankNat p v) ∧ rankNat p v%2=1 ∧
      c p v=ArithmeticPellRecurrence.ycoord (rankNat p v) (A p v-1) ∧
      ∃ n : V, 0<n ∧ 2*n=rankNat p v+1 ∧
        2*ArithmeticPellRecurrence.ycoord n (2*(TenPositive80Pell.firstParam p v-1)+1)=k v := by
  obtain ⟨h31,hl,hh,hodd⟩ := fixed_bounds (V:=V) p hp0 hp2 hp3
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) h31
  have hp := graph_power p v h31 hl hh hv hz hodd
  obtain ⟨_hlo,_hwindow,hrank,hc⟩ := graph_rank_exact p v hb hl hh hv hz
  obtain ⟨n,hn,_hnR,heq,hfirst,_hmain⟩ := graph_first_main_alignment p v hb hl hh hv hz hodd
  exact ⟨hp,hrank,hc,n,hn,heq,hfirst⟩

#print axioms TenPositive80FixedSymbolicPower.fixed_symbolic_power
end TenPositive80FixedSymbolicPower

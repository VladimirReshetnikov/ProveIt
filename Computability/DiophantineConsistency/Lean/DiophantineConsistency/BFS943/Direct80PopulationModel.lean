import DiophantineConsistency.BFS943.Direct80PopulationSandwich
import DiophantineConsistency.BFS943.Direct80SandwichBoth

/-! Population conclusion from the actual positive 80 graph zero. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Direct80PopulationModel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ArithmeticBinaryPopulation
open TenPositive80Graph TenPositive80Factors TenPositive80NaturalRank
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_population (p : Fin 4 → ℕ) (v : Fin 10 → V) (d : V)
    (hbeta31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : InternalZero (graph (integerPorts p)).output v)
    (hbetaodd : ∃u : V, (p 0:V)=2*u+1) (hd : 2≤d)
    (hbeta : (p 0:V)+1=Exp.exp d) :
    ∃ N : V, 0<N ∧ v 0=ArithmeticRepunit.rep d N ∧
      3*(d*N)+2≤population (rankNat p v) := by
  obtain ⟨r,hr,hR,_hX,hlow,hup⟩ :=
    TenPositive80SandwichBoth.graph_sandwich_both p v hbeta31 hl hh hv hz hbetaodd
  exact Direct80PopulationSandwich.graph_population_of_sandwich p v d r
    hbeta31 hl hh hv hz hbetaodd hd hbeta hr hR hlow hup

#print axioms Direct80PopulationModel.graph_population
end Direct80PopulationModel

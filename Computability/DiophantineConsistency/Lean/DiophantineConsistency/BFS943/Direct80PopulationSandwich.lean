import DiophantineConsistency.BFS943.Direct80PopulationConditional
import DiophantineConsistency.BFS943.ScaledPellRounding

/-! Reducing the graph population conclusion to same-index sandwiches. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Direct80PopulationSandwich
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011
open ArithmeticPow ArithmeticBinomPascal ArithmeticBinaryPopulation
open TenPositive80Graph TenPositive80Factors TenPositive80NaturalRank
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_population_of_sandwich (p : Fin 4 → ℕ) (v : Fin 10 → V) (d r : V)
    (hbeta31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : InternalZero (graph (integerPorts p)).output v)
    (hbetaodd : ∃u : V, (p 0:V)=2*u+1) (hd : 2≤d)
    (hbeta : (p 0:V)+1=Exp.exp d) (hr0 : 0<r) (hr : rankNat p v=2*r+1)
    (hlow : k v*power (X p v+1) (2*r)<2*c p v*power (X p v) r)
    (hup : 2*c p v*power (X p v) r<k v*(power (X p v+1) (2*r)+power (X p v) r)) :
    ∃ N : V, 0<N ∧ v 0=ArithmeticRepunit.rep d N ∧
      3*(d*N)+2≤population (rankNat p v) := by
  have hX : X p v=Exp.exp (2*r+1) := by
    rw [←hr]
    exact Direct80GraphPower.graph_power p v hbeta31 hl hh hv hz hbetaodd
  obtain ⟨z,hbin⟩ := ScaledPellRounding.extract (X p v) (Y p v) r (v 8) (v 9)
    (k v) (c p v) hr0 hX rfl rfl (hv 8) (hv 9) hlow hup
  exact Direct80PopulationConditional.graph_population_of_half_binomial p v d r z
    hbeta31 hl hh hv hz hbetaodd hd hbeta hr hbin

#print axioms Direct80PopulationSandwich.graph_population_of_sandwich
end Direct80PopulationSandwich

import MainBalance85
import DiophantineConsistency.ArithmeticPellClassification

/-! Source-only direct 85 main Pell index and carrier balance. No q|X or
other graph zero is assumed; all draft imports remain unelaborated. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.MainIndex85Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticPellRecurrence
open NaturalRank84Draft DirectNorms85Draft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Classify the same direct-85 main root while retaining its old carrier
balance, including the X*Y*q term. No m=R conclusion is made. -/
theorem main_index (p : Fin 4 → ℤ) (beta K MC MF : V) (v : Fin 14 → V)
    (hbeta : 0<beta) (hport : (p 0 : DiffRing V)=ι beta)
    (hK : (p 1 : DiffRing V)=ι K) (hMC : (p 2 : DiffRing V)=ι MC)
    (hMF : (p 3 : DiffRing V)=ι MF) (hv : ∀ j, 0<v j)
    (hz : InternalZero (P85QcubeGraph.graph p).output v) :
    let R := naturalRank beta MC MF v
    let H : V := 3+4*a beta v
    ∃ d m : V, m≤c beta v ∧ xcoord m (a beta v)=d ∧ ycoord m (a beta v)=c beta v ∧
      d*d=1+delta (a beta v)*c beta v*c beta v ∧
      U beta v*d+H*k v=U beta v*(X v+a beta v*c beta v)+
        H*(U beta v*v 12+X v*Y beta v*q beta v+R+1) := by
  obtain ⟨d,hn,hbal⟩ := MainBalance85Draft.norm_and_balance p beta K MC MF v
    hbeta hport hK hMC hMF hv hz
  have hdelta : Delta beta v=delta (a beta v) := by dsimp [Delta,delta]; ring
  have hnorm : d*d=1+delta (a beta v)*c beta v*c beta v := by rw [←hdelta]; exact hn
  obtain ⟨m,hm,hx,hy⟩ := ArithmeticPellClassification.solution_index (a beta v) d (c beta v) hnorm
  exact ⟨d,m,hm,hx,hy,hnorm,hbal⟩

end DiophantineConsistency.MainIndex85Draft

#print axioms DiophantineConsistency.MainIndex85Draft.main_index

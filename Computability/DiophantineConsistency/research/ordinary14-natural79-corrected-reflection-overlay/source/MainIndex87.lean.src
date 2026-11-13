import MainBalance87
import QCubeSize87
import DiophantineConsistency.ArithmeticPellClassification

/-! Source-only direct 87 main Pell index and carrier balance. No q|X or
other graph zero is assumed; all draft imports remain unelaborated. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.MainIndex87Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticPellRecurrence
open NaturalRank84Draft MainBalance87Draft StrongNorm87Draft FirstFields86Draft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Classify the same direct-87 main root while retaining its old carrier
balance, including the X*Y*q term. No m=R conclusion is made. -/
theorem main_index (p : Fin 4 → ℤ) (beta K MC MF : V) (v : Fin 14 → V)
    (hbeta : 0<beta) (hport : (p 0 : DiffRing V)=ι beta)
    (hK : (p 1 : DiffRing V)=ι K) (hMC : (p 2 : DiffRing V)=ι MC)
    (hMF : (p 3 : DiffRing V)=ι MF) (hv : ∀ j, 0<v j)
    (hz : InternalZero (P87ShiftedGuard.graph p).output v) :
    let R := naturalRank beta MC MF v
    let H : V := 3+4*a v
    ∃ d m : V, m≤c v ∧ xcoord m (a v)=d ∧ ycoord m (a v)=c v ∧
      d*d=1+delta (a v)*c v*c v ∧
      U beta v*d+H*k v=U beta v*(X v+a v*c v)+
        H*(U beta v*v 12+X v*Y v*q beta v+R+1) := by
  have hY8 : 8≤Y v := QCubeSize87Draft.Y_at_least_eight p beta v hbeta (hv 0) (hv 7) hport hz
  obtain ⟨d,hn,hbal⟩ := MainBalance87Draft.norm_and_balance p beta K MC MF v
    hbeta hport hK hMC hMF hv hY8 hz
  have hdelta : Delta v=delta (a v) := by dsimp [Delta,delta]; ring
  have hnorm : d*d=1+delta (a v)*c v*c v := by rw [←hdelta]; exact hn
  obtain ⟨m,hm,hx,hy⟩ := ArithmeticPellClassification.solution_index (a v) d (c v) hnorm
  exact ⟨d,m,hm,hx,hy,hnorm,hbal⟩

end DiophantineConsistency.MainIndex87Draft

#print axioms DiophantineConsistency.MainIndex87Draft.main_index

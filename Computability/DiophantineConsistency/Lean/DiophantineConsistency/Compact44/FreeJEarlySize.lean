import DiophantineConsistency.Compact44.FreeJIndexComparison
import DiophantineConsistency.ArithmeticPellResidueAux
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FreeJEarlySize
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency.AdaptiveEquationSyntax2011
open DiophantineConsistency.ArithmeticPellRecurrence
open DiophantineConsistency.ArithmeticPellResidueAux
open DiophantineConsistency.Ordinary12FreeJ
open FreeJIndexComparison
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The main Pell ordinate is already large before recovery of the ordinary
strong norm. The compact44 port inequalities remain explicit assumptions. -/
theorem early_size (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀ j,0<v j) (hz : InternalZero (literal (fun j => (p j:ℤ))) v) :
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    let k : V := v 8+v 9
    let c : V := v 8+v 6*k
    let a : V := v 5*v 6+v 6
    (a+2)*delta a*delta a<c ∧ 2*R<c := by
  obtain ⟨first,main,n,m,hfirst,hmain,hn13,hnm,hm14,hhalf,hroot,horient,hnx,hny,hmx,hmy,hnmod⟩ := comparison p v hb hl hh hv hz
  refine ⟨?_,hhalf⟩
  have hm6 : (6:V)≤m := le_trans (by
    simpa only [show (6:V)+8=14 by ring] using (show (6:V)≤6+8 by simp)) hm14
  rw [←hmy]
  exact large_of_six _ m hm6
end FreeJEarlySize
#print axioms FreeJEarlySize.early_size

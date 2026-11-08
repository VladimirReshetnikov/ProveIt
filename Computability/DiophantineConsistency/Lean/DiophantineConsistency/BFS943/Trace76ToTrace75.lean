import DiophantineConsistency.BFS943.Trace76Transport

/-! # Every positive 76/352 zero gives a positive 75/402 zero

At a positive zero of `value76`, `Trace76Transport.graph_transport` gives
`0 ≤ (V² - b V) B`. Moving `n` up by that amount (`value75_update`) keeps
every coordinate positive and turns the 76 circuit into the 75 circuit at
the same ports. This is the whole soundness reduction: the 75 chain to
halting (`Trace75BFSModelHalt.graph_halts`) then applies unchanged. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace76ToTrace75
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 TenPositiveTrace76
open Trace75Factors
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem positive75_of_positive76 (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : value76 (ports p) (fun j => ι (v j)) = 0) :
    ∃ w : Fin 10 → V, (∀j,0<w j) ∧ value75 (ports p) (fun j => ι (w j)) = 0 := by
  let rr := regs (ports p) (fun j => ι (v j))
  let d : DiffRing V := (rr.V*rr.V-rr.b*rr.V)*rr.B
  have hd : 0≤d := (Trace76Transport.graph_transport p v hb hv hz).2
  obtain ⟨t,ht⟩ : ∃ t : V, (ι t:DiffRing V)=d := by
    rcases nonneg_or_nonpos d with ⟨t,ht⟩|⟨t,ht⟩
    · exact ⟨t,ht.symm⟩
    · refine ⟨t,?_⟩
      have h0 : (ι t:DiffRing V)≤0 := by linarith
      have h1 : (ι t:DiffRing V)=0 := le_antisymm h0 (ι_nonneg t)
      rw [ht,h1]; simp
  let w : Fin 10 → V := Function.update v 7 (v 7+t)
  have hw : ∀j,0<w j := by
    intro j
    by_cases hj : j=7
    · subst hj; simp only [w,Function.update_self]; exact add_pos_of_pos_of_nonneg (hv 7) (by simp)
    · simp only [w,Function.update_of_ne hj]; exact hv j
  have hcast : (fun j => (ι (w j):DiffRing V)) =
      Function.update (fun j => ι (v j)) 7 (ι (v 7)+d) := by
    funext j
    by_cases hj : j=7
    · subst hj; simp only [w,Function.update_self,map_add,ht]
    · simp only [w,Function.update_of_ne hj]
  refine ⟨w,hw,?_⟩
  rw [hcast,value75_update (ports p) (fun j => ι (v j)) (ι (v 7)+d) rfl]
  exact hz

#print axioms Trace76ToTrace75.positive75_of_positive76
end Trace76ToTrace75

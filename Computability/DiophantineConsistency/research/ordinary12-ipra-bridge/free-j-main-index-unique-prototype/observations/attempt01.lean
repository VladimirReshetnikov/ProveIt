import DiophantineConsistency.FreeJExactOrdinary

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace FreeJMainIndexUnique
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.AdaptiveEquationSyntax2011
open DiophantineConsistency.ArithmeticPellRecurrence
open DiophantineConsistency.Ordinary12FreeJ

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Every index of the recovered ordinary ordinate is the graph rank. -/
theorem graph_ordinate_index_unique (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hb : 0 < (p 0 : V)) (hl : (p 2 : V) < (p 0 : V))
    (hh : (p 3 : V) < 2 * (p 0 : V)) (hv : ∀ j, 0 < v j)
    (hz : InternalZero (literal (fun j => (p j : ℤ))) v) (m : V)
    (hm : ycoord m (v 5*v 6+v 6) = v 8+v 6*(v 8+v 9)) :
    let q : V := 1+v 0*(p 0:V)
    m = ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0 := by
  obtain ⟨_, _, _, pi, _, _, _, _, hpi, _, _, _, _, hordinate⟩ :=
    FreeJExactOrdinary.exact_ordinary_indices p v hb hl hh hv hz
  have hm_pi : m = pi := (y_strictMono (v 5*v 6+v 6)).injective (hm.trans hordinate.symm)
  exact hm_pi.trans hpi

end FreeJMainIndexUnique

#print axioms FreeJMainIndexUnique.graph_ordinate_index_unique

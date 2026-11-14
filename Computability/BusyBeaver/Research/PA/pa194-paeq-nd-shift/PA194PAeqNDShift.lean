import PA194PAeqND
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194PAeq.ND
open LO LO.FirstOrder

def shiftProof {Γ : List Form} {p : Form} (d : Proof Γ p) : Proof (shifted Γ) p.shift := by
  have h := LO.FirstOrder.Derivation.shift d
  simpa [Proof, shifted, Rewriting.shifts, List.map_map, Function.comp_def,
    Semiformula.shift, ← Semiformula.neg_eq] using h

def shiftClosed {Γ : List Form} {p : Form} (d : Proof Γ p)
    (hp : p.freeVariables = ∅) : Proof (shifted Γ) p := by
  have h : p.shift = p := by
    apply Semiformula.rew_eq_self_of
    · intro i; exact Fin.elim0 i
    · intro i hi; exact False.elim (by simpa [Semiformula.FVar?,hp] using hi)
  simpa only [h] using shiftProof d

#print axioms shiftProof
#print axioms shiftClosed
end PA194PAeq.ND

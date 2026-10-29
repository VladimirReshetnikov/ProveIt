import DiophantineConsistency.ParsonsCutFree
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsCutFreeChecks
open LO LO.FirstOrder
open scoped LO.FirstOrder
open ParsonsCutFree

example {L : Language} [L.DecidableEq] {T : Theory L} {σ : Sentence L}
    (p : Theory.Proof T σ) : (cutEliminate p).axioms = p.axioms := rfl
example {L : Language} [L.DecidableEq] {T : Theory L} {σ : Sentence L} :
    T ⊢ σ ↔ Nonempty (CutFreeTheoryProof T σ) := provable_iff_cutFree

#print axioms cutEliminate
#print axioms cutEliminate_axioms
#print axioms toTheoryProof
#print axioms provable_iff_cutFree
end DiophantineConsistency.ParsonsCutFreeChecks

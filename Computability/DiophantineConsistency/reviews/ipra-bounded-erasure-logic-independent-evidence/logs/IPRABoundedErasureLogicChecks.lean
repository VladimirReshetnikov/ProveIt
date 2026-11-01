import DiophantineConsistency.IPRABoundedErasureLogic

open LO LO.FirstOrder
open scoped LO.FirstOrder
open LO.FirstOrder.Rewriting DiophantineConsistency.IPRABoundedErasureLogic

example {L : Language} [L.DecidableEq] {Λ : Hilbertᵢ L}
    {guard φ ψ : Semipropositionᵢ L 1} (h : Λ ⊢! free φ 🡒 free ψ) :
    Λ ⊢! (∃⁰ (guard ⋏ φ)) 🡒 ∃⁰ ψ := eraseGuardedEx h

#print axioms DiophantineConsistency.IPRABoundedErasureLogic.eraseAnd
#print axioms DiophantineConsistency.IPRABoundedErasureLogic.eraseOr
#print axioms DiophantineConsistency.IPRABoundedErasureLogic.eraseAll
#print axioms DiophantineConsistency.IPRABoundedErasureLogic.eraseGuardedEx

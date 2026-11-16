import FINER.DemandClosureBlueprint
import FINER.ObservationBlueprint

/-!
# FINER selected-certificate and residual compiler blueprint

A full graph compiler should *generate* the package below.  Its public theorem
is then a small composition in ordinary `Prf PRAAx`.  Search selection is a
separate constructor built from `Search.mu`, `search_found`, Boolean reflection,
and an explicit accepted-certificate existence residual.
-/

namespace LeanProofs.IPRA.FINER

open LeanProofs.ConciseIPRA
open LeanProofs.IPRA
open Syn
open scoped Fm

/-- Already specialised output of all compiler passes. -/
structure CompiledQuery (n : ℕ) where
  residuals : List (Fm PTm n)
  selectedCertificate : PTm n
  selectedAccepted : Fm PTm n
  conclusion : Fm PTm n
  acceptanceProof : residuals ⊢[PRAAx] selectedAccepted
  certificateSound : selectedAccepted :: residuals ⊢[PRAAx] conclusion

/-- The generic endpoint after the graph-specific checker, search, trace, and
observer constructors have produced a `CompiledQuery`. -/
theorem compileQuery {n : ℕ} (Q : CompiledQuery n) :
    Q.residuals ⊢[PRAAx] Q.conclusion := by
  apply Prf.trans Q.certificateSound
  intro ψ hψ
  simp only [List.mem_cons] at hψ
  rcases hψ with rfl | htail
  · exact Q.acceptanceProof
  · exact Prf.hyp htail

/-- Close a compiled theorem after supplying derivations of all residuals. -/
theorem closeQuery {n : ℕ} (Q : CompiledQuery n)
    {Γ : List (Fm PTm n)}
    (hres : ∀ ψ ∈ Q.residuals, Γ ⊢[PRAAx] ψ) :
    Γ ⊢[PRAAx] Q.conclusion :=
  Prf.trans (compileQuery Q) hres

/-- Search-specific generator target.  The final implementation should define
`selectedCertificate := Search.mu checkerBody bound packedInput`, prove
acceptance from `certificateExists`, and return a `CompiledQuery`. -/
structure SearchSelectionInput (n : ℕ) where
  residuals : List (Fm PTm n)
  packedInput : PTm n
  bound : PTm n
  checkerBody : PTm 2
  certificateExists : Fm PTm n
  selectedAccepted : Fm PTm n
  conclusion : Fm PTm n
  existenceProof : residuals ⊢[PRAAx] certificateExists
  soundnessProof : selectedAccepted :: residuals ⊢[PRAAx] conclusion

/-- Milestone: build the selected-certificate package from the checked search
API. -/
def compileSearchSelection {n : ℕ} (S : SearchSelectionInput n) :
    CompiledQuery n := by
  -- Construct the `Search.mu` term, reflect `checkerBody = 0`, instantiate
  -- `Search.search_found`, and populate `acceptanceProof`.
  sorry

end LeanProofs.IPRA.FINER

import Foundation.FirstOrder.Hauptsatz

/-! A finite theory proof supplies the cut-free sequent needed to begin the
proof-theoretic conservation argument. Its actual finite axiom list is retained;
no induction axiom is removed and no PRA conservation theorem is asserted. -/
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsCutFree
open LO LO.FirstOrder
open scoped LO.FirstOrder

/-- A cut-free logical derivation with a finite list of actual theory axioms. -/
structure CutFreeTheoryProof {L : Language} (T : Theory L) (σ : Sentence L) where
  axioms : List (Sentence L)
  axioms_mem : ∀ ψ ∈ axioms, ψ ∈ T
  derivation : {d : OneSidedLK.Pullback Derivation Rewriting.emb (σ :: ∼axioms) //
    Derivation.IsCutFree d}

/-- Cut elimination retains the precise list of theory axioms of the input. -/
noncomputable def cutEliminate {L : Language} [L.DecidableEq] {T : Theory L}
    {σ : Sentence L} (p : Theory.Proof T σ) : CutFreeTheoryProof T σ :=
  ⟨p.axioms, p.axioms_mem, Derivation.Canonical.hauptsatz p.derivation⟩

@[simp] theorem cutEliminate_axioms {L : Language} [L.DecidableEq] {T : Theory L}
    {σ : Sentence L} (p : Theory.Proof T σ) : (cutEliminate p).axioms = p.axioms := rfl

/-- Forgetting the cut-free witness recovers a finite theory proof. -/
def toTheoryProof {L : Language} {T : Theory L} {σ : Sentence L}
    (p : CutFreeTheoryProof T σ) : Theory.Proof T σ :=
  ⟨p.axioms, p.axioms_mem, p.derivation.val⟩

theorem provable_iff_cutFree {L : Language} [L.DecidableEq] {T : Theory L}
    {σ : Sentence L} : T ⊢ σ ↔ Nonempty (CutFreeTheoryProof T σ) := by
  constructor
  · rintro ⟨p⟩
    exact ⟨cutEliminate p⟩
  · rintro ⟨p⟩
    exact ⟨toTheoryProof p⟩

end DiophantineConsistency.ParsonsCutFree

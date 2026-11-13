module
public import M6PA.Theory
public import M6PA.Calibration.PAPresentationAxioms
@[expose] public section

/-! Explicit typed witnesses for the unchanged ordinary PAeq axiom predicate.
This is not a numerical code or decoder. Executable later compilers receive
the witness; Prop-only theory membership is never eliminated into proof data. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder

inductive OrdinaryAxiomWitness : Type
  | fixed (p : Proposition Presentation.language) (member : p∈Presentation.fixedAxioms)
  | induction (p : Semiproposition Presentation.language 1)

def OrdinaryAxiomWitness.body : OrdinaryAxiomWitness → Proposition Presentation.language
  | .fixed p _ => p
  | .induction p => Presentation.inductionFormula p

def OrdinaryAxiomWitness.sentence (w : OrdinaryAxiomWitness) : Sentence Presentation.language :=
  w.body.univCl

theorem OrdinaryAxiomWitness.valid (w : OrdinaryAxiomWitness) : Presentation.PAeqAxiom w.body := by
  cases w with
  | fixed p h => exact .fixed p h
  | induction p => exact .induction p

theorem OrdinaryAxiomWitness.mem (w : OrdinaryAxiomWitness) : w.sentence∈Presentation.ordinaryPAeq :=
  ⟨w.body,w.valid,rfl⟩

/-- Existence stays in Prop. This is not an extraction procedure for callers
holding only theory membership. -/
theorem ordinaryAxiomWitness_exists {σ : Sentence Presentation.language}
    (h : σ∈Presentation.ordinaryPAeq) :
    Nonempty {w : OrdinaryAxiomWitness // w.sentence=σ} := by
  obtain ⟨p,hp,he⟩ := h
  cases hp with
  | fixed p hp => exact ⟨⟨.fixed p hp,he⟩⟩
  | induction p => exact ⟨⟨.induction p,he⟩⟩

theorem ordinaryAxiomWitness_iff (σ : Sentence Presentation.language) :
    σ∈Presentation.ordinaryPAeq ↔ Nonempty {w : OrdinaryAxiomWitness // w.sentence=σ} := by
  constructor
  · exact ordinaryAxiomWitness_exists
  · rintro ⟨⟨w,hw⟩⟩
    rw [←hw]
    exact w.mem

#print axioms OrdinaryAxiomWitness.mem
#print axioms ordinaryAxiomWitness_exists
#print axioms ordinaryAxiomWitness_iff
end M6.PA.ForwardRelational


module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedAnnotatedProof
public import M6PA.Calibration.PAInterpretedND
@[expose] public section

/-! Conditional executable transport of explicitly annotated ordinary-PAeq
proofs. Every literal closed axiom image is supplied as an actual target proof;
this module does not manufacture an induction image or eliminate Prop-only
membership into witness data. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)

def ordinaryAnnotatedImages (ws : List OrdinaryAxiomWitness) : List (SourceFormula 0) :=
  ws.map (fun w => Rewriting.emb w.sentence)

def ordinaryAnnotatedImageSupply (ws : List OrdinaryAxiomWitness) (f : Nat → Term 0)
    {C : List Form} (h : ∀ w,w∈ws→ND.Proof C (formula (Rewriting.emb w.sentence) Fin.elim0 f))
    (p : SourceFormula 0) (hp : p∈ordinaryAnnotatedImages ws) :
    ND.Proof C (formula p Fin.elim0 f) := by
  cases ws with
  | nil => exact False.elim (List.not_mem_nil hp)
  | cons w ws =>
    by_cases he : p=Rewriting.emb w.sentence
    · subst p; exact h w (by simp)
    · exact ordinaryAnnotatedImageSupply ws f (fun v hv => h v (List.mem_cons_of_mem _ hv)) p
        ((List.mem_cons.mp hp).resolve_left he)

def OrdinaryAnnotatedProof.interpret {σ : Sentence Presentation.language}
    (d : OrdinaryAnnotatedProof σ) {C : List Form} (f : Nat → Term 0)
    (A : SubstitutionPremises C) (H : DomainEnvironment C f)
    (h : ∀ w,w∈d.witnesses→ND.Proof C (formula (Rewriting.emb w.sentence) Fin.elim0 f)) :
    ND.Proof C (formula (Rewriting.emb σ) Fin.elim0 f) :=
  interpretedND (ordinaryAnnotatedImages d.witnesses) _ d.sourceDerivation f A H
    (ordinaryAnnotatedImageSupply d.witnesses f h)

#print axioms ordinaryAnnotatedImageSupply
#print axioms OrdinaryAnnotatedProof.interpret
end M6.PA.ForwardRelational


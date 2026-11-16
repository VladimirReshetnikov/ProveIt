module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedAxiomWitness
public import M6PA.Calibration.PAPresentationND
@[expose] public section

/-! Explicit finite ordinary-PAeq proof annotations. Executable consumers take
these typed witness lists; existence from Prop-only theory membership remains
in Prop and is not a numerical decoder or internal arithmetized reduction. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder

structure OrdinaryAnnotatedProof (σ : Sentence Presentation.language) where
  witnesses : List OrdinaryAxiomWitness
  derivation : OneSidedLK.Pullback LK.Derivation Rewriting.emb
    (⦃σ⦄ + ∼(witnesses.map OrdinaryAxiomWitness.sentence : Multiset (Sentence Presentation.language)))

def OrdinaryAnnotatedProof.forget {σ : Sentence Presentation.language}
    (d : OrdinaryAnnotatedProof σ) : Presentation.ordinaryPAeq.Proof σ where
  axioms := d.witnesses.map OrdinaryAxiomWitness.sentence
  axioms_mem := by
    intro ψ hψ
    have hm : ψ ∈ d.witnesses.map OrdinaryAxiomWitness.sentence := by simpa using hψ
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
    exact w.mem
  derivation := d.derivation

def OrdinaryAnnotatedProof.sourceDerivation {σ : Sentence Presentation.language}
    (d : OrdinaryAnnotatedProof σ) :
    Presentation.ND.Proof (d.witnesses.map (fun w => (Rewriting.emb w.sentence : Proposition Presentation.language)))
      (Rewriting.emb σ) := by
  refine LK.Derivation.cast d.derivation ?_
  simp [Presentation.ND.negatives,Multiset.tilde_def,Multiset.map_map,
    List.map_map,Function.comp_def,←Semiformula.neg_eq,Rewriting.emb]
  abel

theorem ordinaryAnnotateList : ∀ l : List (Sentence Presentation.language),
    (∀σ∈l,σ∈Presentation.ordinaryPAeq) →
    ∃ ws : List OrdinaryAxiomWitness,ws.map OrdinaryAxiomWitness.sentence=l
  | [],_ => ⟨[],rfl⟩
  | σ::l,h => by
    obtain ⟨⟨w,hw⟩⟩ := ordinaryAxiomWitness_exists (h σ (by simp))
    obtain ⟨ws,hws⟩ := ordinaryAnnotateList l (fun τ hτ => h τ (List.mem_cons_of_mem _ hτ))
    exact ⟨w::ws,by simp [hw,hws]⟩

theorem ordinaryAnnotations_exist {σ : Sentence Presentation.language}
    (d : Presentation.ordinaryPAeq.Proof σ) : Nonempty (OrdinaryAnnotatedProof σ) := by
  obtain ⟨ws,hws⟩ := ordinaryAnnotateList d.axioms.toList (by simpa using d.axioms_mem)
  exact ⟨⟨ws,by simpa only [hws,Multiset.coe_toList] using d.derivation⟩⟩

#print axioms OrdinaryAnnotatedProof.forget
#print axioms OrdinaryAnnotatedProof.sourceDerivation
#print axioms ordinaryAnnotations_exist
end M6.PA.ForwardRelational


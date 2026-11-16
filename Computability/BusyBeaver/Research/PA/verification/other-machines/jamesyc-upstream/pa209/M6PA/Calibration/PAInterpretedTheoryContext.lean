module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedAnnotatedCompiler
public import M6PA.Calibration.PAInterpretedFixedPremises
@[expose] public section

/-! Finite theory-image integration. The only support premise is an explicit
syntax identity for translated closed sentences, separate from logical axiom
images. Both are retained until their independent suppliers are instantiated. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)

def ordinarySentenceImage (σ : Sentence Presentation.language) : Form :=
  formula (Rewriting.emb σ) Fin.elim0 (fun _ => .fvar 0)

def SentenceImageSupport : Prop :=
  ∀ (σ : Sentence Presentation.language) (f : Nat → Term 0),
    formula (Rewriting.emb σ) Fin.elim0 f = ordinarySentenceImage σ

def ordinarySentenceImageShift (S : SentenceImageSupport) {Γ : List Form}
    (σ : Sentence Presentation.language) (h : ND.Proof Γ (ordinarySentenceImage σ)) :
    ND.Proof (shifted Γ) (ordinarySentenceImage σ) := by
  have he : (ordinarySentenceImage σ).shift = ordinarySentenceImage σ := by
    simp only [ordinarySentenceImage,formula_shift]
    have hb : freeShiftEnv (Fin.elim0 : Fin 0 → Term 0) = Fin.elim0 := by
      funext i; exact Fin.elim0 i
    rw [hb]
    exact S σ _
  exact he ▸ shiftProof h

def FixedImagePremises.prepend {Γ : List Form} (I : FixedImagePremises Γ) :
    (ps : List Form) → FixedImagePremises (ps++Γ)
  | [] => I
  | p::ps => (I.prepend ps).up p

def ordinaryImageContext (ws : List OrdinaryAxiomWitness) : List Form :=
  ws.map (fun w => ordinarySentenceImage w.sentence)

def OrdinaryAnnotatedProof.refutation {Γ : List Form}
    (d : OrdinaryAnnotatedProof (Semiformula.falsum : Sentence Presentation.language))
    (S : SentenceImageSupport) (I : FixedImagePremises Γ)
    (h : ∀w,w∈d.witnesses→ND.Proof Γ (ordinarySentenceImage w.sentence)) : ND.Proof Γ ⊥ := by
  apply exsElim I.totality.zero
  let b : Form := (Ordinal.domain (.bvar 0) ⋏ Ordinal.zero (.bvar 0)).free
  have hb : ND.Proof (b::shifted Γ) (Ordinal.domain (.fvar 0) ⋏ Ordinal.zero (.fvar 0)) := by
    have hh : ND.Proof (b::shifted Γ) b := assumption (by simp)
    convert hh using 1 <;> (dsimp [b] <;> totalitySyntax)
  have out := d.interpret (fun _ => .fvar 0) (I.shift.up b).substitution
    (fun _ => andLeft hb) (fun w hw => by
      rw [S w.sentence _]
      exact up (ordinarySentenceImageShift S w.sentence (h w hw)) b)
  convert out using 1 <;>
    (simp only [formula,Semiformula.shift,Rewriting.shift,Rewriting.emb,
      Semiformula.rew,Semiformula.rewAux] <;> rfl)

def ordinaryRefutationDerivation
    (d : OrdinaryAnnotatedProof (Semiformula.falsum : Sentence Presentation.language))
    (S : SentenceImageSupport) :
    ND.Proof (ordinaryImageContext d.witnesses++interpretedFixedAxioms) ⊥ :=
  d.refutation S (interpretedFixedPremises.prepend _) (fun w hw => assumption
    (List.mem_append_left _ (List.mem_map.mpr ⟨w,hw,rfl⟩)))

#print axioms ordinarySentenceImageShift
#print axioms OrdinaryAnnotatedProof.refutation
#print axioms ordinaryRefutationDerivation
end M6.PA.ForwardRelational


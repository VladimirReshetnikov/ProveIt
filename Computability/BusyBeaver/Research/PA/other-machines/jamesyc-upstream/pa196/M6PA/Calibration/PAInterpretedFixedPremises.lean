module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedFixedSupplier
public import M6PA.Calibration.PAInterpretedND
@[expose] public section

/-! The paid fixed-image context is stable under genuine target eigenvariable
shifts and supplies the logical compiler's explicit arithmetic proof data. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
open PairGraph

def FixedImagePremises.substitution {Γ : List Form} (I : FixedImagePremises Γ) :
    SubstitutionPremises Γ :=
  ⟨I.multiplication.additionImage.coherence,I.totality,
    I.multiplication.additionImage.identity,I.multiplication.additionImage.symmetry,
    I.multiplication.transitivity⟩

def FixedImagePremises.up {Γ : List Form} (I : FixedImagePremises Γ) (q : Form) :
    FixedImagePremises (q::Γ) :=
  ⟨I.multiplication.up q,I.totality.up q,ND.up I.strictSeparation q⟩

def FixedImagePremises.shift {Γ : List Form} (I : FixedImagePremises Γ) :
    FixedImagePremises (shifted Γ) :=
  ⟨I.multiplication.shift,I.totality.shift,predecessorClosedSeparationShift I.strictSeparation⟩

/-- Finite fixed-axiom ND transport, with every source axiom checked against
exact fixedAxioms and every target image genuinely constructed. -/
def interpretedFixedND {Γ : List Form} (I : FixedImagePremises Γ)
    (ps : List (SourceFormula 0)) (p : SourceFormula 0) (d : Presentation.ND.Proof ps p)
    (hps : ∀ q,q∈ps→q∈Presentation.fixedAxioms)
    (f : Nat → Term 0) (H : DomainEnvironment Γ f) :
    ND.Proof Γ (formula p Fin.elim0 f) :=
  interpretedND ps p d f I.substitution H (fun q hq => interpretedFixedAxiom I q (hps q hq) f)

#print axioms FixedImagePremises.shift
#print axioms interpretedFixedND
end M6.PA.ForwardRelational


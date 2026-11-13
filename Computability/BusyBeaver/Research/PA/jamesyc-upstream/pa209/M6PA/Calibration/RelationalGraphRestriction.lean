module
public import M6PA.Theory
public import M6PA.Calibration.RelationalOrderIsoRules
public import M6PA.Calibration.RelationalKuratowskiTransport
public import M6PA.Calibration.RelationalParameterSpecialization
@[expose] public section

/-! Finite restrictions of actual graph objects. Separation retains all free
parameters; a retained object includes its own decoding witnesses. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)

def strictEntry (top p : Term n) : Formula n :=
  ∃¹ ∃¹ (kuratowski (Rew.bShift (Rew.bShift p)) (.bvar 1) (.bvar 0) ⋏
    mem (Rew.bShift (Rew.bShift top)) (.bvar 1))
def strictEntryProperty (top : Term n) : Formula (n+1) :=
  strictEntry (Rew.bShift top) (.bvar 0)
def entryFilter (h g : Term n) (φ : Formula (n+1)) : Formula n :=
  ∀¹ sourceIff (mem (Rew.bShift h) (.bvar 0))
    (mem (Rew.bShift g) (.bvar 0) ⋏ φ)
def strictGraphCut (top g h : Term n) : Formula n :=
  entryFilter h g (strictEntryProperty top)
def strictGraphCutExists (top g : Term n) : Formula n :=
  ∃¹ strictGraphCut (Rew.bShift top) (Rew.bShift g) (.bvar 0)
def strictGraphRestriction (top g h : Term n) : Formula n :=
  ∀¹ ∀¹ sourceIff (edge (Rew.bShift (Rew.bShift h)) (.bvar 1) (.bvar 0))
    (edge (Rew.bShift (Rew.bShift g)) (.bvar 1) (.bvar 0) ⋏
      mem (Rew.bShift (Rew.bShift top)) (.bvar 1))

macro "restrictionSyntax" : tactic => `(tactic|
  ((first | simp only [strictEntry,strictEntryProperty,entryFilter,strictGraphCut,
    strictGraphCutExists,strictGraphRestriction,separationFormula,liftMember,memAtom] | skip); isoSyntax))

def strictCutExists {Γ : List Form} (top g : Nat)
    (hs : ND.Proof Γ (separationFormula (strictEntryProperty (.fvar top)))) :
    ND.Proof Γ (strictGraphCutExists (.fvar top) (.fvar g)) := by
  convert allElim _ (.fvar g) hs using 1 <;> restrictionSyntax

def strictCutShift {Γ : List Form} (top g h : Nat)
    (hc : ND.Proof Γ (strictGraphCut (.fvar top) (.fvar g) (.fvar h))) :
    ND.Proof (shifted Γ) (strictGraphCut (.fvar (top+1)) (.fvar (g+1)) (.fvar (h+1))) := by
  convert shiftProof hc using 1 <;> restrictionSyntax

def strictCutAt {Γ : List Form} (top g h p : Nat)
    (hc : ND.Proof Γ (strictGraphCut (.fvar top) (.fvar g) (.fvar h))) :
    ND.Proof Γ (sourceIff (mem (.fvar h) (.fvar p))
      (mem (.fvar g) (.fvar p) ⋏ strictEntry (.fvar top) (.fvar p))) := by
  convert allElim _ (.fvar p) hc using 1 <;> restrictionSyntax

def strictEntryIntro {Γ : List Form} (top p x y : Nat)
    (hk : ND.Proof Γ (kuratowski (.fvar p) (.fvar x) (.fvar y)))
    (hm : ND.Proof Γ (mem (.fvar top) (.fvar x))) :
    ND.Proof Γ (strictEntry (.fvar top) (.fvar p)) := by
  apply exsIntro _ (.fvar x)
  have hi : ND.Proof Γ (∃¹ (kuratowski (.fvar p) (.fvar x) (.bvar 0) ⋏
      mem (.fvar top) (.fvar x))) := by
    apply exsIntro _ (.fvar y)
    convert andIntro hk hm using 1 <;> restrictionSyntax
  convert hi using 1 <;> restrictionSyntax

/-- Eliminate the two actual coordinate witnesses, keeping the context explicit. -/
def strictEntryEliminate {Γ : List Form} (top p : Nat) (q : Form)
    (hs : ND.Proof Γ (strictEntry (.fvar top) (.fvar p)))
    (k : ∀ {Δ : List Form}, (∀ z, z ∈ shifted (shifted Γ) → z ∈ Δ) →
      ND.Proof Δ (kuratowski (.fvar (p+1+1)) (.fvar 1) (.fvar 0)) →
      ND.Proof Δ (mem (.fvar (top+1+1)) (.fvar 1)) →
      ND.Proof Δ q.shift.shift) : ND.Proof Γ q := by
  apply exsElim hs
  let σ : Formula 1 := ∃¹ (kuratowski (.fvar p) (.bvar 1) (.bvar 0) ⋏
    mem (.fvar top) (.bvar 1))
  let C := σ.free :: shifted Γ
  let τ : Formula 1 := kuratowski (.fvar (p+1)) (.fvar 0) (.bvar 0) ⋏
    mem (.fvar (top+1)) (.fvar 0)
  have ht : ND.Proof C (∃¹ τ) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ,τ]; restrictionSyntax)
  apply exsElim ht
  let D := τ.free :: shifted C
  have hd : ND.Proof D (kuratowski (.fvar (p+1+1)) (.fvar 1) (.fvar 0) ⋏
      mem (.fvar (top+1+1)) (.fvar 1)) := by
    have hh : ND.Proof D τ.free := assumption (by simp [D])
    convert hh using 1 <;> (dsimp [τ]; restrictionSyntax)
  have out := k (Δ := D) (by intro z hz; simp [D,C,shifted] at *; tauto)
    (andLeft hd) (andRight hd)
  convert out using 1 <;> (dsimp [D,C,σ,τ]; restrictionSyntax)

#print axioms strictCutExists
#print axioms strictEntryEliminate
end M6.PA.RelationalSource.PairGraph

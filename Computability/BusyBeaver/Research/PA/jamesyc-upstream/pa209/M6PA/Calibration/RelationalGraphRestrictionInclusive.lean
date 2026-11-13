module
public import M6PA.Theory
public import M6PA.Calibration.RelationalGraphRestrictionEdges
@[expose] public section

/-! Finite restrictions of actual graph objects. Separation retains all free
parameters; a retained object includes its own decoding witnesses. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)

def inclusiveDomain (top x : Term n) : Formula n := mem top x ⋎ eq x top

def domainEntry (top p : Term n) : Formula n :=
  ∃¹ ∃¹ (kuratowski (Rew.bShift (Rew.bShift p)) (.bvar 1) (.bvar 0) ⋏
    inclusiveDomain (Rew.bShift (Rew.bShift top)) (.bvar 1))
def domainEntryProperty (top : Term n) : Formula (n+1) :=
  domainEntry (Rew.bShift top) (.bvar 0)
def inclusiveGraphCut (top g h : Term n) : Formula n :=
  entryFilter h g (domainEntryProperty top)
def inclusiveGraphCutExists (top g : Term n) : Formula n :=
  ∃¹ inclusiveGraphCut (Rew.bShift top) (Rew.bShift g) (.bvar 0)
def graphRestriction (top g h : Term n) : Formula n :=
  ∀¹ ∀¹ sourceIff (edge (Rew.bShift (Rew.bShift h)) (.bvar 1) (.bvar 0))
    (edge (Rew.bShift (Rew.bShift g)) (.bvar 1) (.bvar 0) ⋏
      inclusiveDomain (Rew.bShift (Rew.bShift top)) (.bvar 1))

macro "inclusiveRestrictionSyntax" : tactic => `(tactic|
  ((first | simp only [inclusiveDomain,domainEntry,domainEntryProperty,entryFilter,inclusiveGraphCut,
    inclusiveGraphCutExists,graphRestriction,separationFormula,liftMember,memAtom] | skip); isoSyntax))

def inclusiveCutExists {Γ : List Form} (top g : Nat)
    (hs : ND.Proof Γ (separationFormula (domainEntryProperty (.fvar top)))) :
    ND.Proof Γ (inclusiveGraphCutExists (.fvar top) (.fvar g)) := by
  convert allElim _ (.fvar g) hs using 1 <;> inclusiveRestrictionSyntax

def inclusiveCutShift {Γ : List Form} (top g h : Nat)
    (hc : ND.Proof Γ (inclusiveGraphCut (.fvar top) (.fvar g) (.fvar h))) :
    ND.Proof (shifted Γ) (inclusiveGraphCut (.fvar (top+1)) (.fvar (g+1)) (.fvar (h+1))) := by
  convert shiftProof hc using 1 <;> inclusiveRestrictionSyntax

def inclusiveCutAt {Γ : List Form} (top g h p : Nat)
    (hc : ND.Proof Γ (inclusiveGraphCut (.fvar top) (.fvar g) (.fvar h))) :
    ND.Proof Γ (sourceIff (mem (.fvar h) (.fvar p))
      (mem (.fvar g) (.fvar p) ⋏ domainEntry (.fvar top) (.fvar p))) := by
  convert allElim _ (.fvar p) hc using 1 <;> inclusiveRestrictionSyntax

def domainEntryIntro {Γ : List Form} (top p x y : Nat)
    (hk : ND.Proof Γ (kuratowski (.fvar p) (.fvar x) (.fvar y)))
    (hm : ND.Proof Γ (inclusiveDomain (.fvar top) (.fvar x))) :
    ND.Proof Γ (domainEntry (.fvar top) (.fvar p)) := by
  apply exsIntro _ (.fvar x)
  have hi : ND.Proof Γ (∃¹ (kuratowski (.fvar p) (.fvar x) (.bvar 0) ⋏
      inclusiveDomain (.fvar top) (.fvar x))) := by
    apply exsIntro _ (.fvar y)
    convert andIntro hk hm using 1 <;> inclusiveRestrictionSyntax
  convert hi using 1 <;> inclusiveRestrictionSyntax

/-- Eliminate the two actual coordinate witnesses, keeping the context explicit. -/
def domainEntryEliminate {Γ : List Form} (top p : Nat) (q : Form)
    (hs : ND.Proof Γ (domainEntry (.fvar top) (.fvar p)))
    (k : ∀ {Δ : List Form}, (∀ z, z ∈ shifted (shifted Γ) → z ∈ Δ) →
      ND.Proof Δ (kuratowski (.fvar (p+1+1)) (.fvar 1) (.fvar 0)) →
      ND.Proof Δ (inclusiveDomain (.fvar (top+1+1)) (.fvar 1)) →
      ND.Proof Δ q.shift.shift) : ND.Proof Γ q := by
  apply exsElim hs
  let σ : Formula 1 := ∃¹ (kuratowski (.fvar p) (.bvar 1) (.bvar 0) ⋏
    inclusiveDomain (.fvar top) (.bvar 1))
  let C := σ.free :: shifted Γ
  let τ : Formula 1 := kuratowski (.fvar (p+1)) (.fvar 0) (.bvar 0) ⋏
    inclusiveDomain (.fvar (top+1)) (.fvar 0)
  have ht : ND.Proof C (∃¹ τ) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ,τ]<;> inclusiveRestrictionSyntax)
  apply exsElim ht
  let D := τ.free :: shifted C
  have hd : ND.Proof D (kuratowski (.fvar (p+1+1)) (.fvar 1) (.fvar 0) ⋏
      inclusiveDomain (.fvar (top+1+1)) (.fvar 1)) := by
    have hh : ND.Proof D τ.free := assumption (by simp [D])
    convert hh using 1 <;> (dsimp [τ]<;> inclusiveRestrictionSyntax)
  have out := k (Δ := D) (by intro z hz; simp [D,C,shifted] at *; tauto)
    (andLeft hd) (andRight hd)
  convert out using 1 <;> (dsimp [D,C,σ,τ]<;> inclusiveRestrictionSyntax)

#print axioms inclusiveCutExists
#print axioms domainEntryEliminate
end M6.PA.RelationalSource.PairGraph

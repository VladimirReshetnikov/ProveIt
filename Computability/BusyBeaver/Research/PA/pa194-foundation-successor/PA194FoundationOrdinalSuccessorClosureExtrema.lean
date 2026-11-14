import PA194FoundationOrdinalSuccessorClosureTrace
namespace M6.PA.RelationalSource.Ordinal
open LO LO.FirstOrder ND

def leastExists (s : Term n) : Formula n := ∃⁰ least (Rew.bShift s) (.bvar 0)
def greatestExists (s : Term n) : Formula n := ∃⁰ greatest (Rew.bShift s) (.bvar 0)
def extrema (s : Term n) : Formula n := leastExists s ⋏ greatestExists s

macro "extremaSyntax" : tactic => `(tactic|
  ((try simp only [leastExists,greatestExists,extrema]); ordinalSyntax))

def logicalCases {Γ : List Form} (p : Form) : ND.Proof Γ (p ⋎ ∼p) :=
  closed (LO.FirstOrder.Derivation.or (LO.FirstOrder.Derivation.eta p))

def leastWitness {Γ : List Form} (s m : Nat) (d : ND.Proof Γ (least (.fvar s) (.fvar m))) :
    ND.Proof Γ (leastExists (.fvar s)) := by
  apply exsIntro _ (.fvar m)
  convert d using 1 ; extremaSyntax

def greatestWitness {Γ : List Form} (s m : Nat) (d : ND.Proof Γ (greatest (.fvar s) (.fvar m))) :
    ND.Proof Γ (greatestExists (.fvar s)) := by
  apply exsIntro _ (.fvar m)
  convert d using 1 ; extremaSyntax

def internalExtremaShift {Γ : List Form} (a : Nat)
    (d : ND.Proof Γ (internalExtrema (.fvar a))) :
    ND.Proof (shifted Γ) (internalExtrema (.fvar (a+1))) := by
  convert shiftProof d using 1 ; ordinalSyntax

def internalExtremaAt {Γ : List Form} (a c : Nat)
    (d : ND.Proof Γ (internalExtrema (.fvar a)))
    (hc : ND.Proof Γ (subset (.fvar c) (.fvar a)))
    (hne : ND.Proof Γ (nonempty (.fvar c))) : ND.Proof Γ (extrema (.fvar c)) := by
  have hd : ND.Proof Γ ((subset (.fvar c) (.fvar a) ⋏ nonempty (.fvar c)) 🡒 extrema (.fvar c)) := by
    convert allElim _ (.fvar c) d using 1 ; extremaSyntax
  exact mp (andIntro hc hne) hd

def traceLeastExists {Γ : List Form} (e : EqualityProofs Γ) (a b s c : Nat)
    (hs : ND.Proof Γ (successor (.fvar a) (.fvar b)))
    (hsub : ND.Proof Γ (subset (.fvar s) (.fvar b)))
    (ht : ND.Proof Γ (intersection (.fvar a) (.fvar s) (.fvar c)))
    (hl : ND.Proof Γ (leastExists (.fvar c))) : ND.Proof Γ (leastExists (.fvar s)) := by
  apply exsElim hl
  let σ : Formula 1 := least (Rew.bShift (.fvar c)) (.bvar 0)
  let C := σ.free :: shifted Γ
  have hm : ND.Proof C (least (.fvar (c+1)) (.fvar 0)) := by
    have h : ND.Proof C σ.free := assumption (by simp [C])
    convert h using 1 ; dsimp [σ] ; ordinalSyntax
  have h := leastWitness (s+1) 0 (traceLeast (e.shift.up σ.free) (a+1) (b+1) (s+1) (c+1) 0
    (up (successorShift a b hs) σ.free) (up (subsetShift s b hsub) σ.free)
    (up (intersectionShift a s c ht) σ.free) hm)
  convert h using 1 ; extremaSyntax

def traceGreatestExists {Γ : List Form} (e : EqualityProofs Γ) (a b s c : Nat)
    (hs : ND.Proof Γ (successor (.fvar a) (.fvar b)))
    (hsub : ND.Proof Γ (subset (.fvar s) (.fvar b)))
    (ht : ND.Proof Γ (intersection (.fvar a) (.fvar s) (.fvar c)))
    (hn : ND.Proof Γ (∼mem (.fvar s) (.fvar a)))
    (hg : ND.Proof Γ (greatestExists (.fvar c))) : ND.Proof Γ (greatestExists (.fvar s)) := by
  apply exsElim hg
  let σ : Formula 1 := greatest (Rew.bShift (.fvar c)) (.bvar 0)
  let C := σ.free :: shifted Γ
  have hm : ND.Proof C (greatest (.fvar (c+1)) (.fvar 0)) := by
    have h : ND.Proof C σ.free := assumption (by simp [C])
    convert h using 1 ; dsimp [σ] ; ordinalSyntax
  have dn : ND.Proof C (∼mem (.fvar (s+1)) (.fvar (a+1))) := by
    convert up (shiftProof hn) σ.free using 1 ; sourceSyntaxEq
  have h := greatestWitness (s+1) 0 (traceGreatest (e.shift.up σ.free) (a+1) (b+1) (s+1) (c+1) 0
    (up (successorShift a b hs) σ.free) (up (subsetShift s b hsub) σ.free)
    (up (intersectionShift a s c ht) σ.free) dn hm)
  convert h using 1 ; extremaSyntax

/-- A nonempty trace supplies a least element. For the greatest element,
the new point is used exactly when it belongs to the represented subset. -/
def nonemptyTraceExtrema {Γ : List Form} (e : EqualityProofs Γ) (a b s c : Nat)
    (ha : ND.Proof Γ (internalExtrema (.fvar a)))
    (hs : ND.Proof Γ (successor (.fvar a) (.fvar b)))
    (hsub : ND.Proof Γ (subset (.fvar s) (.fvar b)))
    (ht : ND.Proof Γ (intersection (.fvar a) (.fvar s) (.fvar c)))
    (hne : ND.Proof Γ (nonempty (.fvar c))) : ND.Proof Γ (extrema (.fvar s)) := by
  have hc := internalExtremaAt a c ha (intersectionSubset a s c ht) hne
  apply andIntro (traceLeastExists e a b s c hs hsub ht (andLeft hc))
  apply orElim (logicalCases (mem (.fvar s) (.fvar a)))
  · exact greatestWitness s a (pointGreatest a b s (up hs _) (up hsub _) (assumption (by simp)))
  · exact traceGreatestExists (e.up _) a b s c (up hs _) (up hsub _) (up ht _)
      (assumption (by simp)) (up (andRight hc) _)

def traceExtrema {Γ : List Form} (e : EqualityProofs Γ) (a b s c : Nat)
    (ha : ND.Proof Γ (internalExtrema (.fvar a)))
    (hs : ND.Proof Γ (successor (.fvar a) (.fvar b)))
    (hsub : ND.Proof Γ (subset (.fvar s) (.fvar b)))
    (ht : ND.Proof Γ (intersection (.fvar a) (.fvar s) (.fvar c)))
    (hne : ND.Proof Γ (nonempty (.fvar s))) : ND.Proof Γ (extrema (.fvar s)) := by
  apply orElim (logicalCases (nonempty (.fvar c)))
  · exact nonemptyTraceExtrema (e.up _) a b s c (up ha _) (up hs _) (up hsub _)
      (up ht _) (assumption (by simp))
  · have hn : ND.Proof (∼nonempty (.fvar c)::Γ) (∼nonempty (.fvar c)) := assumption (by simp)
    have hp := emptyTracePoint (e.up _) a b s c (up hs _) (up hsub _) (up ht _) hn (up hne _)
    exact andIntro (leastWitness s a (emptyTraceLeast (e.up _) a b s c
      (up hs _) (up hsub _) (up ht _) hn hp))
      (greatestWitness s a (pointGreatest a b s (up hs _) (up hsub _) hp))

#print axioms logicalCases
#print axioms traceLeastExists
#print axioms traceGreatestExists
#print axioms nonemptyTraceExtrema
#print axioms traceExtrema
end M6.PA.RelationalSource.Ordinal


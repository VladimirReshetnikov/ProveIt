module
public import M6PA.Theory
public import M6PA.Calibration.RelationalOrdinalSuccessorClosureExtremaLogic
@[expose] public section

/-! Finite least/greatest witness transformations for an intersection trace.
All sets and witnesses remain raw representatives. -/
namespace M6.PA.RelationalSource.Ordinal
open FFL FFL.FirstOrder ND

def traceLeast {Γ : List Form} (e : EqualityProofs Γ) (a b s c m : Nat)
    (hs : ND.Proof Γ (successor (.fvar a) (.fvar b)))
    (hsub : ND.Proof Γ (subset (.fvar s) (.fvar b)))
    (ht : ND.Proof Γ (intersection (.fvar a) (.fvar s) (.fvar c)))
    (hl : ND.Proof Γ (least (.fvar c) (.fvar m))) :
    ND.Proof Γ (least (.fvar s) (.fvar m)) := by
  have hm := mp (andLeft hl) (andLeft (intersectionAt a s c m ht))
  apply andIntro (andLeft hm)
  apply allIntro
  let p : Form := mem (.fvar (s+1)) (.fvar 0)
  let C := p :: shifted Γ
  have hp : ND.Proof C p := assumption (by simp [C])
  have ds := up (successorShift a b hs) p
  have du := up (subsetShift s b hsub) p
  have dt := up (intersectionShift a s c ht) p
  have dl := up (leastShift c m hl) p
  have es := e.shift.up p
  have dm := mp (andLeft dl) (andLeft (intersectionAt (a+1) (s+1) (c+1) (m+1) dt))
  have split := mp (subsetAt _ _ _ du hp) (andLeft (successorAt (a+1) (b+1) 0 ds))
  have old : ND.Proof (mem (.fvar (a+1)) (.fvar 0) :: C)
      (eq (.fvar (m+1)) (.fvar 0) ⋎ mem (.fvar 0) (.fvar (m+1))) :=
    leastAt (c+1) (m+1) 0 (up dl _) (mp (andIntro (up hp _) (assumption (by simp)))
      (up (andRight (intersectionAt (a+1) (s+1) (c+1) 0 dt)) _))
  have point : ND.Proof (eq (.fvar 0) (.fvar (a+1)) :: C)
      (eq (.fvar (m+1)) (.fvar 0) ⋎ mem (.fvar 0) (.fvar (m+1))) :=
    ND.orRight (memContainer (es.up _) (a+1) 0 (m+1)
      (eqSymm (es.up _) 0 (a+1) (assumption (by simp))) (up (andRight dm) _))
  have h := impIntro (orElim split old point)
  convert h using 1 ; dsimp [p,C] ; ordinalSyntax

def pointGreatest {Γ : List Form} (a b s : Nat)
    (hs : ND.Proof Γ (successor (.fvar a) (.fvar b)))
    (hsub : ND.Proof Γ (subset (.fvar s) (.fvar b)))
    (ha : ND.Proof Γ (mem (.fvar s) (.fvar a))) :
    ND.Proof Γ (greatest (.fvar s) (.fvar a)) := by
  apply andIntro ha
  apply allIntro
  let p : Form := mem (.fvar (s+1)) (.fvar 0)
  have hp : ND.Proof (p :: shifted Γ) p := assumption (by simp)
  have ds := up (successorShift a b hs) p
  have du := up (subsetShift s b hsub) p
  have split := mp (subsetAt _ _ _ du hp) (andLeft (successorAt (a+1) (b+1) 0 ds))
  have h : ND.Proof (shifted Γ) (p 🡒
      (eq (.fvar 0) (.fvar (a+1)) ⋎ mem (.fvar (a+1)) (.fvar 0))) :=
    impIntro (orElim split (ND.orRight (assumption (by simp))) (ND.orLeft (assumption (by simp))))
  convert h using 1 ; dsimp [p] ; ordinalSyntax

def traceGreatest {Γ : List Form} (e : EqualityProofs Γ) (a b s c m : Nat)
    (hs : ND.Proof Γ (successor (.fvar a) (.fvar b)))
    (hsub : ND.Proof Γ (subset (.fvar s) (.fvar b)))
    (ht : ND.Proof Γ (intersection (.fvar a) (.fvar s) (.fvar c)))
    (hn : ND.Proof Γ (∼mem (.fvar s) (.fvar a)))
    (hg : ND.Proof Γ (greatest (.fvar c) (.fvar m))) :
    ND.Proof Γ (greatest (.fvar s) (.fvar m)) := by
  have hm := mp (andLeft hg) (andLeft (intersectionAt a s c m ht))
  apply andIntro (andLeft hm)
  apply allIntro
  let p : Form := mem (.fvar (s+1)) (.fvar 0)
  let C := p :: shifted Γ
  have hp : ND.Proof C p := assumption (by simp [C])
  have ds := up (successorShift a b hs) p
  have du := up (subsetShift s b hsub) p
  have dt := up (intersectionShift a s c ht) p
  have dg := up (greatestShift c m hg) p
  have dn : ND.Proof C (∼mem (.fvar (s+1)) (.fvar (a+1))) := by
    convert up (shiftProof hn) p using 1 ; sourceSyntaxEq
  have es := e.shift.up p
  have split := mp (subsetAt _ _ _ du hp) (andLeft (successorAt (a+1) (b+1) 0 ds))
  have old : ND.Proof (mem (.fvar (a+1)) (.fvar 0) :: C)
      (eq (.fvar 0) (.fvar (m+1)) ⋎ mem (.fvar (m+1)) (.fvar 0)) :=
    greatestAt (c+1) (m+1) 0 (up dg _) (mp (andIntro (up hp _) (assumption (by simp)))
      (up (andRight (intersectionAt (a+1) (s+1) (c+1) 0 dt)) _))
  have point : ND.Proof (eq (.fvar 0) (.fvar (a+1)) :: C)
      (eq (.fvar 0) (.fvar (m+1)) ⋎ mem (.fvar (m+1)) (.fvar 0)) :=
    botElim (contradiction (memElement (es.up _) (s+1) 0 (a+1)
      (assumption (by simp)) (up hp _)) (up dn _))
  have h := impIntro (orElim split old point)
  convert h using 1 ; dsimp [p,C] ; ordinalSyntax

/-- If the old trace has no member, every member of the subset is equal to
its new point. This is a logical case split, not external finite search. -/
def emptyTraceAt {Γ : List Form} (a b s c x : Nat)
    (hs : ND.Proof Γ (successor (.fvar a) (.fvar b)))
    (hsub : ND.Proof Γ (subset (.fvar s) (.fvar b)))
    (ht : ND.Proof Γ (intersection (.fvar a) (.fvar s) (.fvar c)))
    (hn : ND.Proof Γ (∼nonempty (.fvar c)))
    (hx : ND.Proof Γ (mem (.fvar s) (.fvar x))) :
    ND.Proof Γ (eq (.fvar x) (.fvar a)) := by
  have split := mp (subsetAt _ _ _ hsub hx) (andLeft (successorAt a b x hs))
  apply orElim split
  · exact botElim (notNonemptyAt c x (up hn _)
      (mp (andIntro (up hx _) (assumption (by simp))) (up (andRight (intersectionAt a s c x ht)) _)))
  · exact assumption (by simp)

def emptyTracePoint {Γ : List Form} (e : EqualityProofs Γ) (a b s c : Nat)
    (hs : ND.Proof Γ (successor (.fvar a) (.fvar b)))
    (hsub : ND.Proof Γ (subset (.fvar s) (.fvar b)))
    (ht : ND.Proof Γ (intersection (.fvar a) (.fvar s) (.fvar c)))
    (hn : ND.Proof Γ (∼nonempty (.fvar c)))
    (hne : ND.Proof Γ (nonempty (.fvar s))) : ND.Proof Γ (mem (.fvar s) (.fvar a)) := by
  apply exsElim hne
  let σ : Formula 1 := mem (Rew.bShift (.fvar s)) (.bvar 0)
  let C := σ.free :: shifted Γ
  have hx : ND.Proof C (mem (.fvar (s+1)) (.fvar 0)) := by
    have h : ND.Proof C σ.free := assumption (by simp [C])
    convert h using 1 ; dsimp [σ] ; ordinalSyntax
  have dn : ND.Proof C (∼nonempty (.fvar (c+1))) := by
    convert up (shiftProof hn) σ.free using 1 ; ordinalSyntax
  have he := emptyTraceAt (a+1) (b+1) (s+1) (c+1) 0
    (up (successorShift a b hs) σ.free) (up (subsetShift s b hsub) σ.free)
    (up (intersectionShift a s c ht) σ.free) dn hx
  have h := memElement (e.shift.up σ.free) (s+1) 0 (a+1) he hx
  convert h using 1 ; sourceSyntaxEq

def emptyTraceLeast {Γ : List Form} (e : EqualityProofs Γ) (a b s c : Nat)
    (hs : ND.Proof Γ (successor (.fvar a) (.fvar b)))
    (hsub : ND.Proof Γ (subset (.fvar s) (.fvar b)))
    (ht : ND.Proof Γ (intersection (.fvar a) (.fvar s) (.fvar c)))
    (hn : ND.Proof Γ (∼nonempty (.fvar c)))
    (ha : ND.Proof Γ (mem (.fvar s) (.fvar a))) : ND.Proof Γ (least (.fvar s) (.fvar a)) := by
  apply andIntro ha
  apply allIntro
  let p : Form := mem (.fvar (s+1)) (.fvar 0)
  have hp : ND.Proof (p :: shifted Γ) p := assumption (by simp)
  have dn : ND.Proof (p :: shifted Γ) (∼nonempty (.fvar (c+1))) := by
    convert up (shiftProof hn) p using 1 ; ordinalSyntax
  have he := emptyTraceAt (a+1) (b+1) (s+1) (c+1) 0
    (up (successorShift a b hs) p) (up (subsetShift s b hsub) p)
    (up (intersectionShift a s c ht) p) dn hp
  have h : ND.Proof (shifted Γ) (p 🡒
      (eq (.fvar (a+1)) (.fvar 0) ⋎ mem (.fvar 0) (.fvar (a+1)))) :=
    impIntro (ND.orLeft (eqSymm (e.shift.up p) 0 (a+1) he))
  convert h using 1 ; dsimp [p] ; ordinalSyntax

#print axioms traceLeast
#print axioms pointGreatest
#print axioms traceGreatest
#print axioms emptyTraceAt
#print axioms emptyTracePoint
#print axioms emptyTraceLeast
end M6.PA.RelationalSource.Ordinal


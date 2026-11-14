import PA194FoundationOrdinalSuccessorClosureEquality
namespace M6.PA.RelationalSource.Ordinal
open LO LO.FirstOrder ND

def successorTransitive {Γ : List Form} (e : EqualityProofs Γ) (i j : Nat)
    (ha : ND.Proof Γ (transitive (.fvar i)))
    (hs : ND.Proof Γ (successor (.fvar i) (.fvar j))) :
    ND.Proof Γ (transitive (.fvar j)) := by
  apply allIntro
  apply allIntro
  let p : Form := mem (.fvar (j+1+1)) (.fvar 1) ⋏ mem (.fvar 1) (.fvar 0)
  let C := p :: shifted (shifted Γ)
  have hp : ND.Proof C p := assumption (by simp [C])
  have es := (e.shift.shift).up p
  have ds := up (successorShift (i+1) (j+1) (successorShift i j hs)) p
  have dt := up (transitiveShift (i+1) (transitiveShift i ha)) p
  have split := mp (andLeft hp) (andLeft (successorAt (i+1+1) (j+1+1) 1 ds))
  have old : ND.Proof (mem (.fvar (i+1+1)) (.fvar 1) :: C)
      (mem (.fvar (j+1+1)) (.fvar 0)) :=
    successorOld _ _ _ (up ds _) (transitiveAt _ _ _ (up dt _)
      (assumption (by simp)) (up (andRight hp) _))
  have point : ND.Proof (eq (.fvar 1) (.fvar (i+1+1)) :: C)
      (mem (.fvar (j+1+1)) (.fvar 0)) :=
    successorOld _ _ _ (up ds _) (memContainer (es.up _) 1 (i+1+1) 0
      (assumption (by simp)) (up (andRight hp) _))
  have h := impIntro (orElim split old point)
  convert h using 1 ; dsimp [p,C] ; ordinalSyntax

def transitiveTransport {Γ : List Form} (e : EqualityProofs Γ) (i j : Nat)
    (hij : ND.Proof Γ (eq (.fvar i) (.fvar j)))
    (ha : ND.Proof Γ (transitive (.fvar i))) : ND.Proof Γ (transitive (.fvar j)) := by
  apply allIntro
  apply allIntro
  let p : Form := mem (.fvar (j+1+1)) (.fvar 1) ⋏ mem (.fvar 1) (.fvar 0)
  let C := p :: shifted (shifted Γ)
  have hp : ND.Proof C p := assumption (by simp [C])
  have es := (e.shift.shift).up p
  have he : ND.Proof C (eq (.fvar (i+1+1)) (.fvar (j+1+1))) := by
    convert up (shiftProof (shiftProof hij)) p using 1 ; sourceSyntaxEq
  have dt := up (transitiveShift (i+1) (transitiveShift i ha)) p
  have hm := memContainer es (j+1+1) (i+1+1) 1 (eqSymm es _ _ he) (andLeft hp)
  have h := impIntro (memContainer es (i+1+1) (j+1+1) 0 he
    (transitiveAt _ _ _ dt hm (andRight hp)))
  convert h using 1 ; dsimp [p,C] ; ordinalSyntax

def successorMemberTransitive {Γ : List Form} (e : EqualityProofs Γ) (i j : Nat)
    (ha : ND.Proof Γ (transitive (.fvar i)))
    (hm : ND.Proof Γ (memberTransitive (.fvar i)))
    (hs : ND.Proof Γ (successor (.fvar i) (.fvar j))) :
    ND.Proof Γ (memberTransitive (.fvar j)) := by
  apply allIntro
  let p : Form := mem (.fvar (j+1)) (.fvar 0)
  let C := p :: shifted Γ
  have hp : ND.Proof C p := assumption (by simp [C])
  have es := e.shift.up p
  have ds := up (successorShift i j hs) p
  have da := up (transitiveShift i ha) p
  have dm := up (memberTransitiveShift i hm) p
  have split := mp hp (andLeft (successorAt (i+1) (j+1) 0 ds))
  have old : ND.Proof (mem (.fvar (i+1)) (.fvar 0) :: C) (transitive (.fvar 0)) :=
    memberTransitiveAt _ _ (up dm _) (assumption (by simp))
  have point : ND.Proof (eq (.fvar 0) (.fvar (i+1)) :: C) (transitive (.fvar 0)) :=
    transitiveTransport (es.up _) (i+1) 0
      (eqSymm (es.up _) 0 (i+1) (assumption (by simp))) (up da _)
  have h := impIntro (orElim split old point)
  convert h using 1 ; dsimp [p,C] ; ordinalSyntax

def successorMemberIr {Γ : List Form} (e : EqualityProofs Γ) (i j : Nat)
    (hi : ND.Proof Γ (memberIr (.fvar i)))
    (hs : ND.Proof Γ (successor (.fvar i) (.fvar j))) :
    ND.Proof Γ (memberIr (.fvar j)) := by
  apply allIntro
  let p : Form := mem (.fvar (j+1)) (.fvar 0)
  let C := p :: shifted Γ
  have hp : ND.Proof C p := assumption (by simp [C])
  have es := e.shift.up p
  have ds := up (successorShift i j hs) p
  have di := up (memberIrShift i hi) p
  have split := mp hp (andLeft (successorAt (i+1) (j+1) 0 ds))
  have old : ND.Proof (mem (.fvar (i+1)) (.fvar 0) :: C) (∼mem (.fvar 0) (.fvar 0)) :=
    memberIrAt _ _ (up di _) (assumption (by simp))
  have point : ND.Proof (eq (.fvar 0) (.fvar (i+1)) :: C) (∼mem (.fvar 0) (.fvar 0)) := by
    apply byContradiction
    have hh : ND.Proof (∼∼mem (.fvar 0) (.fvar 0) :: eq (.fvar 0) (.fvar (i+1)) :: C)
        (mem (.fvar 0) (.fvar 0)) := by
      simpa using (assumption (p := ∼∼mem (.fvar 0) (.fvar 0)) (by simp))
    have he := assumption (Γ := ∼∼mem (.fvar 0) (.fvar 0) :: eq (.fvar 0) (.fvar (i+1)) :: C)
      (p := eq (.fvar 0) (.fvar (i+1))) (by simp)
    exact contradiction (memCongr ((es.up _).up _) 0 (i+1) 0 (i+1) he he hh)
      (up (up (containerIr (i+1) di) _) _)
  have h := impIntro (orElim split old point)
  convert h using 1 ; dsimp [p,C] ; ordinalSyntax

#print axioms successorTransitive
#print axioms transitiveTransport
#print axioms successorMemberTransitive
#print axioms successorMemberIr
end M6.PA.RelationalSource.Ordinal


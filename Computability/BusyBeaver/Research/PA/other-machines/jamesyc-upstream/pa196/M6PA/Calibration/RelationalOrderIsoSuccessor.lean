module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoSuccessorWitness
@[expose] public section

/-! Successor congruence of existential order isomorphism. Both predecessor
objects are ordinal representatives; no raw equality of representatives is used. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Formula)

def orderIsoSuccessor {Γ : List Form} (E : FormulaEquality Γ) (a b c d : Nat)
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula)
    (ha : ND.Proof Γ (Ordinal.domain (.fvar a)))
    (hb : ND.Proof Γ (Ordinal.domain (.fvar b)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar a) (.fvar c)))
    (ht : ND.Proof Γ (Ordinal.successor (.fvar b) (.fvar d)))
    (hi : ND.Proof Γ (orderIso (.fvar a) (.fvar b))) :
    ND.Proof Γ (orderIso (.fvar c) (.fvar d)) := by
  apply exsElim hi
  let body : Formula 1 := orderBijection (.bvar 0) (.fvar a) (.fvar b)
  let C := body.free :: shifted Γ
  have hg : ND.Proof C (orderBijection (.fvar 0) (.fvar (a+1)) (.fvar (b+1))) := by
    have h : ND.Proof C body.free := assumption (by simp [C])
    convert h using 1 <;> (dsimp [body] <;> isoSyntax)
  let I : IsoSuccessorFrame C 0 (a+1) (b+1) (c+1) (d+1) :=
    ⟨E.shifted.weaken (fun p hp => List.mem_cons_of_mem body.free hp),
      up (emptyClosedShift hempty) body.free,up (adjunctionClosedShift hadj) body.free,hg,
      up (Ordinal.domainShift a ha) body.free,up (Ordinal.domainShift b hb) body.free,
      up (Ordinal.successorShift a c hs) body.free,up (Ordinal.successorShift b d ht) body.free⟩
  have out := isoSuccessorWitness 0 (a+1) (b+1) (c+1) (d+1) I
  convert out using 1 <;> (dsimp [C,body] <;> isoSyntax)

def orderIsoSuccessorPremise (a b c d : Nat) : Form :=
  Ordinal.domain (.fvar a) ⋏ (Ordinal.domain (.fvar b) ⋏
    (Ordinal.successor (.fvar a) (.fvar c) ⋏
      (Ordinal.successor (.fvar b) (.fvar d) ⋏ orderIso (.fvar a) (.fvar b))))
def orderIsoSuccessorStatement (a b c d : Nat) : Form :=
  orderIsoSuccessorPremise a b c d 🡒 orderIso (.fvar c) (.fvar d)

def orderIsoSuccessorDerivation (a b c d : Nat) :
    ND.Proof exactContext (orderIsoSuccessorStatement a b c d) := by
  apply impIntro
  let premise := orderIsoSuccessorPremise a b c d
  have hp : ND.Proof (premise::exactContext) premise := assumption (by simp)
  let E : FormulaEquality (premise::exactContext) :=
    ⟨⟨assumption (by simp [exactContext]),assumption (by simp [exactContext]),
      assumption (by simp [exactContext])⟩,assumption (by simp [exactContext])⟩
  exact orderIsoSuccessor E a b c d (assumption (by simp [exactContext]))
    (assumption (by simp [exactContext])) (andLeft hp) (andLeft (andRight hp))
    (andLeft (andRight (andRight hp))) (andLeft (andRight (andRight (andRight hp))))
    (andRight (andRight (andRight (andRight hp))))

#print axioms orderIsoSuccessor
#print axioms orderIsoSuccessorDerivation
end M6.PA.RelationalSource.PairGraph

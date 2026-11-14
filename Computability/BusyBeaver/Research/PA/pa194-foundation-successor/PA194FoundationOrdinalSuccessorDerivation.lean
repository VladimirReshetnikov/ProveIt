import PA194FoundationOrdinalSuccessorClosure
namespace M6.PA.RelationalSource.Ordinal
open LO LO.FirstOrder ND

def domainSuccessorExists (a : Term n) : Formula n :=
  ∃⁰ (domain (.bvar 0) ⋏ successor (Rew.bShift a) (.bvar 0))

def domainSuccessorStatement (a : Term n) : Formula n := domain a 🡒 domainSuccessorExists a

def domainSuccessorFromAxioms {Γ : List Form} (e : EqualityProofs Γ)
    (et : ND.Proof Γ transitivityFormula) (hi : ND.Proof Γ intersectionFormula)
    (hadj : ND.Proof Γ adjunctionFormula) (a : Term 0) (ha : ND.Proof Γ (domain a)) :
    ND.Proof Γ (domainSuccessorExists a) := by
  cases a with
  | bvar i => nomatch i
  | func f _ => nomatch f
  | fvar i =>
    apply exsElim (rawSuccessor (.fvar i) hadj)
    let σ : Formula 1 := successor (Rew.bShift (.fvar i)) (.bvar 0)
    let C := σ.free :: shifted Γ
    have hs : ND.Proof C (successor (.fvar (i+1)) (.fvar 0)) := by
      have h : ND.Proof C σ.free := assumption (by simp [C])
      convert h using 1 ; dsimp [σ] ; successorSyntax
    have da : ND.Proof C (domain (.fvar (i+1))) := by
      convert up (shiftProof ha) σ.free using 1 ; ordinalSyntax
    have db := successorDomain (e.shift.up σ.free)
      (up (equalityTransShift et) σ.free) (up (intersectionAxiomShift hi) σ.free)
      (.fvar (i+1)) (.fvar 0) da hs
    apply exsIntro _ (.fvar 0)
    have h := andIntro db hs
    convert h using 1
    successorSyntax

def successorAxioms : List Form :=
  [reflexivityFormula,symmetryFormula,transitivityFormula,congruenceFormula,
    adjunctionFormula,intersectionFormula]

def domainSuccessorDerivation (a : Term 0) : ND.Proof successorAxioms (domainSuccessorStatement a) := by
  apply impIntro
  exact domainSuccessorFromAxioms
    ⟨assumption (by simp [successorAxioms]), assumption (by simp [successorAxioms]),
      assumption (by simp [successorAxioms])⟩
    (assumption (by simp [successorAxioms])) (assumption (by simp [successorAxioms]))
    (assumption (by simp [successorAxioms])) a (assumption (by simp))


#print axioms domainSuccessorDerivation
end M6.PA.RelationalSource.Ordinal

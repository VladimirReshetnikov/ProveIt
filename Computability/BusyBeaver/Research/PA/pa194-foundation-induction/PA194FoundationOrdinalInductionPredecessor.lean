import PA194FoundationOrdinalInductionMembers

/-! A greatest member of a transitive representative is a raw predecessor.
This is an explicit finite ND proof, not an extensional identification. -/
namespace M6.PA.RelationalSource.Ordinal
open LO LO.FirstOrder ND

def greatestSuccessor {Γ : List Form} (e : EqualityProofs Γ) (b m : Nat)
    (ht : ND.Proof Γ (transitive (.fvar b)))
    (hg : ND.Proof Γ (greatest (.fvar b) (.fvar m))) :
    ND.Proof Γ (successor (.fvar m) (.fvar b)) := by
  apply allIntro
  have ds := greatestShift b m hg
  have dt := transitiveShift b ht
  have es := e.shift
  have forward : ND.Proof (shifted Γ)
      (mem (.fvar (b+1)) (.fvar 0) 🡒
        (mem (.fvar (m+1)) (.fvar 0) ⋎ eq (.fvar 0) (.fvar (m+1)))) := by
    apply impIntro
    apply orElim (greatestAt (b+1) (m+1) 0 (up ds _) (assumption (by simp)))
    · exact ND.orRight (assumption (by simp))
    · exact ND.orLeft (assumption (by simp))
  have backward : ND.Proof (shifted Γ)
      ((mem (.fvar (m+1)) (.fvar 0) ⋎ eq (.fvar 0) (.fvar (m+1))) 🡒
        mem (.fvar (b+1)) (.fvar 0)) := by
    apply impIntro
    apply orElim (assumption (p := mem (.fvar (m+1)) (.fvar 0) ⋎ eq (.fvar 0) (.fvar (m+1))) (by simp))
    · exact transitiveAt (b+1) (m+1) 0 (up (up dt _) _)
        (up (up (andLeft ds) _) _) (assumption (by simp))
    · exact memElement ((es.up _).up _) (b+1) (m+1) 0
        (eqSymm ((es.up _).up _) 0 (m+1) (assumption (by simp)))
        (up (up (andLeft ds) _) _)
  have h := andIntro forward backward
  convert h using 1 ; successorSyntax

#print axioms greatestSuccessor
end M6.PA.RelationalSource.Ordinal

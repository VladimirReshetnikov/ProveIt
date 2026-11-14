import PA194FoundationAdditionZeroExistence
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND
open Ordinal (Term Formula)

def zeroPrefixStatement (a b : Term n) : Formula n :=
  sourceImply (Ordinal.zero a ⋏ Ordinal.domain b) (addPrefixExists a b)

def zeroPrefixDerivation (a b : Nat) : ND.Proof exactContext (zeroPrefixStatement (.fvar a) (.fvar b)) := by
  apply impIntro
  let q : Form := Ordinal.zero (.fvar a) ⋏ Ordinal.domain (.fvar b)
  have hq : ND.Proof (q :: exactContext) q := assumption (by simp)
  let E : FormulaEquality exactContext :=
    ⟨⟨assumption (by simp [exactContext]),assumption (by simp [exactContext]),
      assumption (by simp [exactContext])⟩,assumption (by simp [exactContext])⟩
  exact zeroPrefixWitness (E.weaken (fun r hr => List.mem_cons_of_mem q hr)) a b
    (andLeft hq) (andRight hq) (assumption (by simp [exactContext]))
    (assumption (by simp [exactContext]))

#print axioms zeroPrefixDerivation
end M6.PA.RelationalSource.PairGraph

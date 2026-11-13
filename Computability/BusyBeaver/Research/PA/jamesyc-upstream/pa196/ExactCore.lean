module
public import NthData
@[expose] public section
namespace PalomarPA

def Term.numeral : Nat → Term ξ n
  | 0 => .zero | 1 => .one | k+2 => .add (numeral (k+1)) .one

def rowFormula (src read write next : Nat) (right : Bool) : Formula Empty 6 :=
  let rightBody : Formula Empty 7 :=
    .and (.eq (.bvar (boundIndex 3)) (.add (.mul (.add .one .one) (.bvar (boundIndex 0))) (.numeral read))) <|
    .and (.eq (.bvar (boundIndex 5)) (.add (.mul (.add .one .one) (.bvar (boundIndex 2))) (.numeral write))) <|
    .eq (.bvar (boundIndex 6)) (.bvar (boundIndex 0))
  let leftBody : Formula Empty 9 :=
    .and (.or (.eq (.bvar (boundIndex 0)) .zero) (.eq (.bvar (boundIndex 0)) .one)) <|
    .and (.eq (.bvar (boundIndex 4)) (.add (.mul (.add .one .one) (.bvar (boundIndex 1))) (.bvar (boundIndex 0)))) <|
    .and (.eq (.bvar (boundIndex 5)) (.add (.mul (.add .one .one) (.bvar (boundIndex 2))) (.numeral read))) <|
    .and (.eq (.bvar (boundIndex 7)) (.bvar (boundIndex 1))) <|
    .eq (.bvar (boundIndex 8)) (.add (.mul (.add .one .one)
      (.add (.mul (.add .one .one) (.bvar (boundIndex 2))) (.numeral write))) (.bvar (boundIndex 0)))
  .and (.eq (.bvar (boundIndex 0)) (.numeral src)) <|
  .and (.eq (.bvar (boundIndex 3)) (.numeral next)) <|
  if right then .ex rightBody else .ex (.ex (.ex leftBody))

/-- Application of the explicit sequence-accessor formula to its three terms. -/
def nthAt (v s i : Term Empty n) : Formula Empty n :=
  nthFormula.rewrite (fun j => if j.val=0 then v else if j.val=1 then s else i) Empty.elim

end PalomarPA

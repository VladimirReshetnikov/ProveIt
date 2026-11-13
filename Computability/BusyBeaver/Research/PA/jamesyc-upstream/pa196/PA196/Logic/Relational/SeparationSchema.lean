module
public import PA196.Logic.Relational.Pointed
@[expose] public section

namespace PA196.Logic.Relational

def separationProperty (a b : Nat) (p : Named) := namedAnd (.mem a b) p

def separationOutput (a b z : Nat) (p : Named) :=
  relationalCode z (paddedProperty a b z (separationProperty a b p))

def actualSeparation (a b z : Nat) (p : Named) :
    Proof (wex (separationOutput a b z p)
      (wal b (iffCode (wel (separationOutput a b z p) b)
        (wa (wel a b) (relationalCode z p))))) := by
  let c := separationOutput a b z p
  let prop := wa (wel a b) (relationalCode z p)
  let mc := wel c b
  let clause := wa (wim (wel a b) (wim prop mc)) (wim mc prop)
  let first : Context [prop,clause] prop := .assumption (by simp)
  let hcl : Context [prop,clause] clause := .assumption (by simp)
  let forward : Context [clause] (wim prop mc) :=
    (Context.mp first (.mp first.andLeft hcl.andLeft)).deduction
  let reverse : Context [clause] (wim mc prop) :=
    (Context.assumption (by simp) : Context [clause] clause).andRight
  let pointwise : Proof (wim clause (iffCode mc prop)) :=
    (Context.andIntro reverse forward).deduction.empty
  let frame : Context [wa (wal b clause) (wim prop mc)]
      (wa (wal b clause) (wim prop mc)) := .assumption (by simp)
  let project : Proof (wim (wa (wal b clause) (wim prop mc)) (wal b (iffCode mc prop))) :=
    (frame.andLeft.forallMP b (.closed (.all b pointwise))).deduction.empty
  let raw := pointedPropertyProof a b z (separationProperty a b p)
  exact .mp raw (existentialMonotonicity c project)

#print axioms actualSeparation
end PA196.Logic.Relational


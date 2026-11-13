module
public import FixTemplateCore
@[expose] public section
namespace PalomarPA
/-- Closed-schema application, with explicit argument order. -/
def prSub1 (p : Formula Empty 1) (a : Term Empty n) := substClosed p (fun _ => a)
def prSub2 (p : Formula Empty 2) (a b : Term Empty n) :=
 substClosed p (fun j => if j.val=0 then a else b)
def prSub3 (p : Formula Empty 3) (a b c : Term Empty n) :=
 substClosed p (fun j => if j.val=0 then a else if j.val=1 then b else c)
/-- PR sequence template for arity zero. `edge i s z` denotes the sequence edge.
All low-level HFS definitions are supplied formulas, not hidden predicates. -/
def prCSeqTemplate (zero seq : Formula Empty 1) (succ edge : Formula Empty 3)
 (length : Formula Empty 2) : Formula Empty 1 :=
 let two : Term Empty 2 := .add .one .one
 let initial : Formula Empty 1 := .ex (.and (.lt (.bvar (boundIndex 0)) (.bvar (boundIndex 1)))
  (.and (prSub1 zero (.bvar (boundIndex 0))) (prSub3 edge .zero (.bvar (boundIndex 1)) (.bvar (boundIndex 0)))))
 let guard : Formula Empty 2 := .ex (.and
  (.lt (.bvar (boundIndex 0)) (.add (.mul (.add .one .one) (.bvar (boundIndex 2))) .one))
  (.and (prSub2 length (.bvar (boundIndex 0)) (.bvar (boundIndex 2))) (.lt (.add (.bvar (boundIndex 1)) .one) (.bvar (boundIndex 0)))))
 let next : Formula Empty 3 := .ex (.and (.lt (.bvar (boundIndex 0)) (.bvar (boundIndex 3)))
  (.and (prSub3 succ (.bvar (boundIndex 0)) (.bvar (boundIndex 1)) (.bvar (boundIndex 2)))
   (prSub3 edge (.add (.bvar (boundIndex 2)) .one) (.bvar (boundIndex 3)) (.bvar (boundIndex 0)))))
 let recursion : Formula Empty 2 := .all (.or (.nlt (.bvar (boundIndex 0)) (.bvar (boundIndex 2)))
  (.or (prSub3 edge (.bvar (boundIndex 1)) (.bvar (boundIndex 2)) (.bvar (boundIndex 0))).neg next))
 .and (prSub1 seq (.bvar (boundIndex 0))) (.and initial
  (.all (.or (.nlt (.bvar (boundIndex 0)) (.mul two (.bvar (boundIndex 1)))) (.or guard.neg recursion))))
def prResultTemplate (cseq : Formula Empty 1) (edge : Formula Empty 3) : Formula Empty 2 :=
 .ex (.and (prSub1 cseq (.bvar (boundIndex 0))) (prSub3 edge (.bvar (boundIndex 2)) (.bvar (boundIndex 0)) (.bvar (boundIndex 1))))
end PalomarPA

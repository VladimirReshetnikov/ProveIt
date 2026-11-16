module
public import PACore
@[expose] public section
namespace PalomarPA
/-- Capture-avoiding instantiation of an explicitly supplied closed schema. -/
def substClosed (p : Formula Empty k) (v : Fin k → Term Empty n) : Formula Empty n :=
 p.rewrite v Empty.elim

def fixSuccTemplate (member coreSigma corePi : Formula Empty 2) : Formula Empty 3 :=
 let x : Term Empty 4 := .bvar (boundIndex 0)
 let u : Term Empty 4 := .bvar (boundIndex 1)
 let ih : Term Empty 4 := .bvar (boundIndex 2)
 let s : Term Empty 4 := .bvar (boundIndex 3)
 let mem := substClosed member (fun j => if j.val=0 then x else u)
 let cs := substClosed coreSigma (fun j => if j.val=0 then x else ih)
 let cp := substClosed corePi (fun j => if j.val=0 then x else ih)
 let le := Formula.or (.eq x s) (.lt x s)
 .all (.or (.nlt x (.add u (.add s .one)))
   (.and (.or mem.neg (.and le cs)) (.or (Formula.and le cp).neg mem)))

def fixZeroTemplate : Formula Empty 1 := .eq (.bvar (boundIndex 0)) .zero

def fixPointTemplate (member result : Formula Empty 2) : Formula Empty 1 :=
 .ex (.ex (.and
  (substClosed result (fun j => if j.val=0 then .bvar (boundIndex 0) else .bvar (boundIndex 1)))
  (substClosed member (fun j => if j.val=0 then .bvar (boundIndex 2) else .bvar (boundIndex 0)))))

def nthTemplate (pair3 : Formula Empty 4) (graph : Formula Empty 1) : Formula Empty 3 :=
 .ex (.and
  (substClosed pair3 (fun j => .bvar (boundIndex (match j.val with | 0 => 0 | 1 => 2 | 2 => 3 | _ => 1))))
  (substClosed graph (fun _ => .bvar (boundIndex 0))))
end PalomarPA

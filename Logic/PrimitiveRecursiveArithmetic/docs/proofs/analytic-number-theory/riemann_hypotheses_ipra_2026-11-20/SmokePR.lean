import Hypotheses
import CompilerSemantics

/-! Small exact evaluations of the formally compiled PR symbols. Strict
vectors materialize each argument once to keep the exhaustive checks small.
The theorem equates this interpreter with the standard interpretation. -/
namespace RiemannIPRA.Smoke
open LeanProofs.ConciseIPRA PacketLanguage

def vecEval : {k : Nat} → PR k → Vector Nat k → Nat
  | _, .zero, _ => 0
  | _, .succ, e => e.get 0 + 1
  | _, .proj i, e => e.get i
  | _, .comp f gs, e => vecEval f (Vector.ofFn (fun i => vecEval (gs i) e))
  | _, .prec f g, e =>
    let params := Vector.ofFn (fun i => e.get i.succ)
    Nat.rec (vecEval f params)
      (fun j a => vecEval g (Vector.ofFn (Fin.cases j (Fin.cases a params.get)))) (e.get 0)

@[simp] theorem get_ofFn_eq {n} (a : Fin n → Nat) : (Vector.ofFn a).get = a := by
  funext i
  simp [Vector.get]

theorem vecEval_eq {n} (f : PR n) (e : Vector Nat n) :
    vecEval f e = value f e.get := by
  induction f with
  | zero => rfl
  | succ => rfl
  | proj i => rfl
  | comp f gs ihf ihgs => simp [vecEval, value, ihf, ihgs]
  | prec f g ihf ihg => simp [vecEval, value, ihf, ihg]


private def h (d H u v p k : Nat) : Nat :=
  vecEval PacketPolynomial.rootDegree #v[d,H,u,v,p,k]

#guard h 1 0 0 0 2 1 == 1
#guard h 2 0 1 0 2 1 == 1
#guard h 2 0 1 0 3 1 == 0
#guard h 2 0 1 0 3 2 == 2
#guard vecEval logCode #v[7] == 2
#guard vecEval primeProduct #v[1,0,0,1,2] == 2

end RiemannIPRA.Smoke

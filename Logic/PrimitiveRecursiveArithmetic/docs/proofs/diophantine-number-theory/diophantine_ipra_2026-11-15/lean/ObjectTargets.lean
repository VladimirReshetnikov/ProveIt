import ConciseIPRA.BiInterpretation

/-!
Object-language target and the existing concise-theory transport.

STATUS: not elaborated in this environment.  This file states the exact
shape of the Størmer completeness target and transports an ALREADY SUPPLIED
derivation.  It does not provide the missing arithmetic derivation or the
concrete PR syntax trees for its numerical algorithms.
-/

namespace DiophantineIPRA.Object

open LeanProofs.ConciseIPRA

def app1 {n : Nat} (f : PR 1) (x : PTm n) : PTm n :=
  PTm.app f (fun _ => x)

def app2 {n : Nat} (f : PR 2) (x y : PTm n) : PTm n :=
  PTm.app f (fun i => if i = 0 then x else y)

structure StormerSymbols where
  /-- Characteristic function of a valid finite prime list. -/
  primeList : PR 1
  /-- Characteristic function of positive S-smoothness. -/
  smooth : PR 2
  /-- Characteristic function of membership in the constructed list. -/
  member : PR 2

def stormerCompleteness (s : StormerSymbols) : Fm PTm 0 :=
  Fm.all (Fm.all (
    Fm.imp
      (Fm.eq (app1 s.primeList (PTm.var 1)) (PTm.succ PTm.zero))
      (Fm.iff
        (Fm.and
          (Fm.eq (app2 s.smooth (PTm.var 1) (PTm.var 0)) (PTm.succ PTm.zero))
          (Fm.eq (app2 s.smooth (PTm.var 1) (PTm.succ (PTm.var 0)))
            (PTm.succ PTm.zero)))
        (Fm.eq (app2 s.member (PTm.var 1) (PTm.var 0)) (PTm.succ PTm.zero)))))

def toConcise (phi : Fm PTm 0) (h : Prf PRAAx [] phi) :
    Prf TeqAx [] (phi.map (fun _ => FromPRA.sigma)) :=
  (pra_theorem_iff phi).mp h

/-
Required next step:
  1. Instantiate StormerSymbols by explicit PR syntax trees.
  2. Construct h : Prf PRAAx [] (stormerCompleteness concreteSymbols).
  3. Apply toConcise to h.

For Davenport–Schmidt, reify the finite rational frozen-core statement,
including the bounded local-separation checker.  For quadratic Roth,
reify the finite polynomial, sign-change, and rational-root checks together
with the explicit cutoff conclusion.  Do not introduce a full-Roth axiom.
-/

end DiophantineIPRA.Object

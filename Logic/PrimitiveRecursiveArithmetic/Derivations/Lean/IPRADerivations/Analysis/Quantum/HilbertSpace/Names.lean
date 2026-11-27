import IPRADerivations.Core.BoundedSums

/-! Imported from the packet `analysis/quantum_ipra_2026-11-20`, `lean/QuantumNames.lean`: the namespace is placed under `LeanProofs.IPRA` and the `#print axioms` lines are dropped (the library audits axioms in `Checks/Axioms.lean`). -/

/-! Object syntax for Hilbert names. Every sampler is a fixed `PR`, hence all
of the resulting `Fm PTm 0` are ordinary first-order iPRA sentences. -/
namespace LeanProofs.IPRA.Analysis.Quantum.Names
open_ipra

/-- A stage consists of a length, a common positive denominator, and four
natural numerators per entry. The coordinate readers take (index, stage). -/
structure VectorCode where
  len : PR 1
  denPred : PR 1
  rePos : PR 2
  reNeg : PR 2
  imPos : PR 2
  imNeg : PR 2

variable {n : ℕ}
private def one : PTm n := PTm.succ PTm.zero
private def sq (a : PTm n) := a * a
private def diff (a b : PTm n) := monus a b + monus b a
private def inRange (i l : PTm n) := monus one (monus (PTm.succ i) l)

def den (x : VectorCode) (s : PTm n) := PTm.succ (ap1 x.denPred s)

def component (x : VectorCode) (c : PR 2) (i s : PTm n) :=
  inRange i (ap1 x.len s) * ap2 c i s

/-- Scaled squared discrepancy for one real or imaginary component. -/
def componentError (x y : VectorCode) (xp xn yp yn : PR 2) (i s t : PTm n) :=
  sq (diff (component x xp i s * den y t + component y yn i t * den x s)
           (component x xn i s * den y t + component y yp i t * den x s))

/-- Sum the term body(index,s,t) with s,t fixed as the length varies. -/
def sumWithTwoParameters (body : PTm 3) : PR 3 :=
  recDef (PTm.zero : PTm 2) ((var 1 : PTm 4) + Syn.subst ![var 0, var 2, var 3] body)

def scaledDist (x y : VectorCode) (s t : PTm n) :=
  let i : PTm 3 := var 0
  let a : PTm 3 := var 1
  let b : PTm 3 := var 2
  let val := componentError x y x.rePos x.reNeg y.rePos y.reNeg i a b +
             componentError x y x.imPos x.imNeg y.imPos y.imNeg i a b
  PTm.app (sumWithTwoParameters val) ![ap1 x.len s + ap1 y.len t, s, t]

/-- Distance ≤ p/q. Clients use this with positive q. -/
def within (x y : VectorCode) (s t p q : PTm n) : Fm PTm n :=
  le (sq q * scaledDist x y s t) (sq (p * den x s * den y t))

def powTwo (k : PTm n) := ap2 powF k (PTm.num 2)

def zeroVector : VectorCode :=
  ⟨Sym.zeroK 1, Sym.zeroK 1, Sym.zeroK 2, Sym.zeroK 2, Sym.zeroK 2, Sym.zeroK 2⟩

def valid (x : VectorCode) (M : Nat) : Fm PTm 0 :=
  univ 1 (within x zeroVector (var 0) PTm.zero (PTm.num M) one) ⋏
  univ 2 (le (var 0) (var 1) ⟶ within x x (var 0) (var 1) one (powTwo (var 0)))

def equivalent (x y : VectorCode) : Fm PTm 0 :=
  univ 1 (within x y (var 0) (var 0) (PTm.num 2) (powTwo (var 0)))

/-- The induction invariant at fixed precision really is quantifier-free. -/
theorem within_qf (x y : VectorCode) (s t p q : PTm n) : (within x y s t p q).QF :=
  True.intro

/-- A hypothetical interface for further proof producers. Its fields require
actual derivations. This structure asserts no instance and adds no axioms. -/
structure CertifiedVector where
  code : VectorCode
  boundPred : Nat
  certificate : ([] : List (Fm PTm 0)) ⊢[PRAAx] valid code (boundPred + 1)

end LeanProofs.IPRA.Analysis.Quantum.Names

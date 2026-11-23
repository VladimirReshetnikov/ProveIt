/-
Exact finite Hadamard/Toffoli path arithmetic. STATUS: UNCOMPILED OUTLINE.
Definitions below are semantic starting points, not object-iPRA syntax.
All substantive target statements appear in comments, without admitted proofs.
The gate list must satisfy valid; Toffoli controls and target are distinct.
-/
import Std

namespace IPRAComplexity.QuantumOutline

def bit (x i : Nat) : Bool := (x / 2^i) % 2 == 1

def setBit (x i : Nat) (v : Bool) : Nat :=
  x - (if bit x i then 2^i else 0) + (if v then 2^i else 0)

inductive Gate where
  | x : Nat → Gate
  | h : Nat → Gate
  | toffoli : Nat → Nat → Nat → Gate
  deriving Repr, DecidableEq

def Gate.valid (q : Nat) : Gate → Bool
  | .x i | .h i => decide (i < q)
  | .toffoli a b c => decide (a < q ∧ b < q ∧ c < q ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c)

structure Circuit where
  qubits : Nat
  gates : List Gate
  output : Nat
  deriving Repr

def Circuit.valid (C : Circuit) : Bool :=
  decide (C.output < C.qubits) && C.gates.all (Gate.valid C.qubits)

def Circuit.hCount (C : Circuit) : Nat :=
  C.gates.foldl (fun n g => match g with | .h _ => n+1 | _ => n) 0

structure PathState where
  basis : Nat
  sign : Int
  used : Nat
  deriving Repr

def pathStep (seed : Nat) (p : PathState) : Gate → PathState
  | .x i => { p with basis := setBit p.basis i (!(bit p.basis i)) }
  | .toffoli a b c =>
      if bit p.basis a && bit p.basis b
      then { p with basis := setBit p.basis c (!(bit p.basis c)) }
      else p
  | .h i =>
      let chosen := bit seed p.used
      let neg := bit p.basis i && chosen
      ⟨setBit p.basis i chosen, (if neg then -p.sign else p.sign), p.used+1⟩

def runPath (C : Circuit) (initial seed : Nat) : PathState :=
  C.gates.foldl (pathStep seed) ⟨initial,1,0⟩

def sumInt : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n+1, f => sumInt n f + f n

def sumNat : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n+1, f => sumNat n f + f n

def signedNumerator (C : Circuit) (initial y : Nat) : Int :=
  sumInt (2^C.hCount) fun seed =>
    let p := runPath C initial seed
    if p.basis = y then p.sign else 0

def squareNat (a : Int) : Nat := (a*a).toNat

def totalNorm (C : Circuit) (initial : Nat) : Nat :=
  sumNat (2^C.qubits) fun y => squareNat (signedNumerator C initial y)

def acceptanceNumerator (C : Circuit) (initial : Nat) : Nat :=
  sumNat (2^C.qubits) fun y =>
    if bit y C.output then squareNat (signedNumerator C initial y) else 0

def contribution (C : Circuit) (initial u v : Nat) : Int :=
  let a := runPath C initial u
  let b := runPath C initial v
  if a.basis = b.basis ∧ bit a.basis C.output = true then a.sign*b.sign else 0

def ppBranch (C : Circuit) (initial : Nat) (mode extra : Bool) (u v : Nat) : Bool :=
  if mode then
    let j := u + 2^C.hCount*v + (if extra then 2^(2*C.hCount) else 0)
    decide (j < 2^(2*C.hCount) - 2^(C.hCount-1))
  else
    let g := contribution C initial u v
    if g = 1 then true else if g = -1 then false else extra

/- Precise pending semantic targets (prove after compiling definitions).

Q01, for valid C, initial < 2^C.qubits:
  (runPath C initial seed).used = C.hCount;
  the sign is 1 or -1; the final basis is < 2^C.qubits;
  totalNorm C initial = 2^C.hCount;
  acceptanceNumerator C initial ≤ 2^C.hCount.
  For H pairs (a,b), prove (a+b)^2+(a-b)^2 = 2*(a^2+b^2).
  Prove each gate's exact signed-array update and the path formula.

Q02:
  Implement classical acyclic-circuit -> reversible-gate-list compiler.
  Use fresh zero targets, a reserved distinct constant-one control,
  and simplify repeated inputs AND(a,a), OR(a,a) to controlled copies.
  Show output equals original circuit on every retained seed.
  Initial H gates create a bijection between seeds and final basis branches,
  so acceptanceNumerator is the original successful-seed count.
  Prove polynomial gate, qubit, and printing bounds separately.

Q03:
  First append H,H on a fresh unused wire so h≥2. Show original acceptance
  probability preserved by numerator and denominator both multiplying by 4.
  Prove sum_{u,v<2^h} contribution C initial u v = acceptanceNumerator.
  For 2h+2 branch bits, show #accept-#reject = 2*A-2^h.
  Prove polynomial time of runPath and threshold comparison on O(h) bits.
  Do not compute acceptanceNumerator in the PP branch machine.

Q04:
  Implement the enumerator over y,u with an O(q+h+L)-bit accounting record.
  Partial signed sums are bounded in absolute value by 2^h; the unreduced
  squared accumulator is ≤ 2^(q+2h). Prove 2A>2^h is the threshold,
  including h=0. The exact norm then gives the sharper final bound.

Object-iPRA lowering:
  Replace List Gate by a bounded digit-array code and Int by signed Nat pairs.
  Fixed PR syntax implements each path and count function. Use bounded sums,
  finite Boolean case proofs, polynomial identities and the fixed-syntax
  Boolean induction compiler. This does not quantify over arbitrary real
  amplitudes or assume quantum-model universality.
-/

end IPRAComplexity.QuantumOutline

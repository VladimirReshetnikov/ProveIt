/-
SpaceOutline.lean — numerical definitions and proof-obligation map.
Status: NOT COMPILED in this package. There are no axiom or sorry declarations.
The main complexity theorems below are specifications in comments, not claimed
Lean proofs. Importing Std is a prospective Lean 4 environment, not a claim
that ProveIt's object-language iPRA proofs have been produced.
-/
import Std

namespace IPRAComplexity.SpaceOutline

/-- A numerical bit, with an explicit zero default at every unused position. -/
def bitAt (a i : Nat) : Bool := (a / 2 ^ i) % 2 == 1

def setBit (a i : Nat) (b : Bool) : Nat :=
  a - (if bitAt a i then 2 ^ i else 0) + (if b then 2 ^ i else 0)

/-- These folds are fixed primitive-recursive numerical functions. -/
def anyBelow : Nat → (Nat → Bool) → Bool
  | 0, _ => false
  | k + 1, p => anyBelow k p || p k

def sumBelow : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | k + 1, p => sumBelow k p + p k

def packBits (k : Nat) (p : Nat → Bool) : Nat :=
  sumBelow k (fun i => if p i then 2 ^ i else 0)

/-- A graph is a vertex bound and a finite bit-table code. -/
structure Graph where
  vertices : Nat
  edges : Nat
  deriving Repr

def edge (g : Graph) (u v : Nat) : Bool :=
  decide (u < g.vertices) && decide (v < g.vertices) &&
    bitAt g.edges (u * g.vertices + v)

/-- Numerical forward reachability row; no set-existence axiom is involved. -/
def reachableRow (g : Graph) (s : Nat) : Nat → Nat
  | 0 => packBits g.vertices (fun v => v == s)
  | k + 1 =>
    let old := reachableRow g s k
    packBits g.vertices (fun v =>
      bitAt old v || anyBelow g.vertices (fun u => bitAt old u && edge g u v))

def reachCount (g : Graph) (s k : Nat) : Nat :=
  sumBelow g.vertices (fun v => if bitAt (reachableRow g s k) v then 1 else 0)

/-- A finite path is supplied numerically as base-(max 2 N) digits. -/
structure PathCode where
  length : Nat
  digits : Nat
  deriving Repr

def pathVertex (g : Graph) (p : PathCode) (i : Nat) : Nat :=
  (p.digits / (max 2 g.vertices) ^ i) % (max 2 g.vertices)

def allBelow : Nat → (Nat → Bool) → Bool
  | 0, _ => true
  | k + 1, p => allBelow k p && p k

def pathOK (g : Graph) (s t : Nat) (p : PathCode) : Bool :=
  (pathVertex g p 0 == s) && (pathVertex g p p.length == t) &&
  allBelow (p.length + 1) (fun i => decide (pathVertex g p i < g.vertices)) &&
  allBelow p.length (fun i => edge g (pathVertex g p i) (pathVertex g p (i + 1)))

/-- The whole Savitch matrix supplies a manifest structural PR definition.
The separate depth-first implementation must be verified to obtain its
space bound; this definition alone is not a small-space algorithm. -/
def midpointMatrix (g : Graph) : Nat → Nat
  | 0 => packBits (g.vertices * g.vertices) (fun i =>
      let u := i / g.vertices
      let v := i % g.vertices
      (u == v) || edge g u v)
  | k + 1 =>
    let old := midpointMatrix g k
    packBits (g.vertices * g.vertices) (fun i =>
      let u := i / g.vertices
      let v := i % g.vertices
      anyBelow g.vertices (fun z =>
        bitAt old (u * g.vertices + z) &&
        bitAt old (z * g.vertices + v)))

def midpointReach (g : Graph) (s t k : Nat) : Bool :=
  decide (s < g.vertices) && decide (t < g.vertices) &&
  bitAt (midpointMatrix g k) (s * g.vertices + t)

/-- For a concrete resource proof these are numerically packed fields. -/
structure SavitchFrame where
  source : Nat
  target : Nat
  level : Nat
  midpoint : Nat
  phase : Nat  -- 0: try midpoint; 1: first child returned; 2: second returned
  deriving Repr

/-- Numerical QBF syntax, with assignments encoded by a natural number. -/
inductive QBF where
  | constant : Bool → QBF
  | atom : Nat → QBF
  | neg : QBF → QBF
  | conj : QBF → QBF → QBF
  | disj : QBF → QBF → QBF
  | existsBit : Nat → QBF → QBF
  | forallBit : Nat → QBF → QBF
  deriving Repr

def evalQBF : QBF → Nat → Bool
  | .constant b, _ => b
  | .atom v, a => bitAt a v
  | .neg f, a => !(evalQBF f a)
  | .conj f g, a => evalQBF f a && evalQBF g a
  | .disj f g, a => evalQBF f a || evalQBF g a
  | .existsBit v f, a => evalQBF f (setBit a v false) || evalQBF f (setBit a v true)
  | .forallBit v f, a => evalQBF f (setBit a v false) && evalQBF f (setBit a v true)

def qbfNodes : QBF → Nat
  | .constant _ => 1
  | .atom _ => 1
  | .neg f => 1 + qbfNodes f
  | .conj f g => 1 + qbfNodes f + qbfNodes g
  | .disj f g => 1 + qbfNodes f + qbfNodes g
  | .existsBit _ f => 1 + qbfNodes f
  | .forallBit _ f => 1 + qbfNodes f

def implies (f g : QBF) : QBF := .disj (.neg f) g

def iffBit (f g : QBF) : QBF := .conj (implies f g) (implies g f)

def vectorEq : List QBF → List QBF → QBF
  | [], [] => .constant true
  | a :: as, b :: bs => .conj (iffBit a b) (vectorEq as bs)
  | _, _ => .constant false

def exBlock (vars : List Nat) (body : QBF) : QBF :=
  vars.foldr QBF.existsBit body

def allBlock (vars : List Nat) (body : QBF) : QBF :=
  vars.foldr QBF.forallBit body

/-- One selector layer, with exactly one occurrence of the body.
All listed bound variables must be fresh for U,V and any external context;
body has the endpoint vectors A,B.  This freshness is an explicit invariant
of the compiler that allocates disjoint intervals of variable numbers. -/
def selectorLayer (u v : List QBF) (m a b : List Nat)
    (selector : Nat) (body : QBF) : QBF :=
  let mv := m.map QBF.atom
  let av := a.map QBF.atom
  let bv := b.map QBF.atom
  let z := QBF.atom selector
  let left : QBF := .conj (vectorEq av u) (vectorEq bv mv)
  let right : QBF := .conj (vectorEq av mv) (vectorEq bv v)
  let guard : QBF := .conj (implies (.neg z) left) (implies z right)
  exBlock m (.forallBit selector (exBlock a (exBlock b (.conj guard body))))

/-- A numerical game table: each state has two successor codes, owner and
terminal-win bits.  The report's succinct version computes these tables
with bounded circuit evaluators instead of storing them. -/
structure Game where
  width : Nat
  ownerBits : Nat
  winBits : Nat
  next0 : Nat
  next1 : Nat
  deriving Repr

def gameNext (g : Game) (q : Nat) (move : Bool) : Nat :=
  let table := if move then g.next1 else g.next0
  let base := 2 ^ g.width
  (table / base ^ q) % base

def winnerTable (g : Game) : Nat → Nat
  | 0 => g.winBits
  | h + 1 =>
    let old := winnerTable g h
    packBits (2 ^ g.width) (fun q =>
      let l := bitAt old (gameNext g q false)
      let r := bitAt old (gameNext g q true)
      if bitAt g.ownerBits q then l || r else l && r)

/- Main proof obligations, intentionally not declared as axioms.

S01 row_spec:
  valid g, s,t<N → bitAt (reachableRow g s k) t = true ↔
  ∃ p, p.length ≤ k ∧ p.digits < (max 2 N)^(k+1) ∧ pathOK g s t p = true.
Also implement eraseCycles and prove its endpoint, edge and distinctness
invariants, giving length ≤ N-1.  Replace all displayed existential path
quantifiers by bounded numerical formulas for the object-language proof.

S02 config_graph_spec:
  Implement configBits, pack/unpack, local edge, valid records, rejecting
  budget boundary, initial and unique accepting sink.  Prove both trace maps,
  the bound ell ≤ C*(s+bitLength(n+2)+1), and O(s)-space edge evaluation.

S03/S04 reductions:
  Implement logspace graph-streaming code and layered graph output.  Prove
  output bits, polynomial output bound, and explicit witness conversion.

S05 matrix_path_spec and stack_simulation:
  midpointReach g s t k = true ↔ a path of length ≤ 2^k exists.
  Implement the stack machine with frames above and a clock bounded by
  C*(2*N+2)^(k+2)*(ell+k+2)^C.  Prove at most k+1 live frames and their
  bit bound.  Establish equality with the whole-matrix definition.

S07/S08 nonreachability:
  Implement online path checks and forced-enumeration transcript checks.
  If the supplied count equals reachCount g s i, every successful negative
  transcript proves the queried bit at i+1 is false.  Construct a successful
  transcript by finite search/row evaluation when the bit is false.
  Lift both soundness and canonical completeness through all N count stages.
  Bound all transcript and path codes explicitly before induction.

S10/S11/S12 QBF:
  Implement freshness and free-variable checks, all-variable renaming,
  numerical syntax codes, and the local transition-formula compiler.
  Prove selectorLayer evaluation equals OR_m (L(m) AND R(m)); show body
  occurs once; count nodes and variable-name bits.  Iterate levels to ell
  and substitute initial/accept records to obtain PSPACE completeness.

S13 games:
  Define canonical strategy-code construction and check its success against
  every bounded opposing history.  Prove depth-first/table equality and
  polynomial workspace for unary horizon; compile prenex QBF to circuits.

Object-language final layer:
  These Lean Nat functions are semantic specifications. Produce fixed PR k
  syntax for each numerical operation and prove bounded invariants using
  IPRADerivations.Foundations.BoundedSyntaxInduction.  Then build an actual
  Prf PRAAx [] phi.  No ambient inductive datatype or function quantifier is
  silently admitted into the first-order object theory.  Instantiations of
  anyBelow/sumBelow are fixed numerical codes, not a universal PR evaluator.
-/

end IPRAComplexity.SpaceOutline

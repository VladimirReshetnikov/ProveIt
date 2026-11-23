/-
Finite semantic definitions for report Section "Reductions, complete problems,
and constructive search".  STATUS: UNCOMPILED OUTLINE.

This file deliberately contains no `axiom`, `sorry`, or asserted theorem with
an omitted proof. Target theorem signatures appear in comments below. The
listed definitions are intended as a starting point; a Lean toolchain was not
available for checking this new module. They are NOT object-iPRA syntax.

To finish: compile the semantic definitions; prove the listed finite lemmas;
replace lists by bounded numerical codes and construct the corresponding
ConciseIPRA.PR syntax; use fixed bounded-formula reflection/induction; build
concrete clocked transducers and prove their operational cost; finally inhabit
([] : List (Fm PTm 0)) ⊢[PRAAx] phi for each encoded statement. No implication
from "Lean definition exists" to "object-iPRA theorem proved" is intended.
-/
import Std

namespace IPRAComplexity.ReductionOutline

abbrev Assignment := List Bool

def assignments : Nat → List Assignment
  | 0 => [[]]
  | n + 1 => (assignments n).flatMap fun a => [false :: a, true :: a]

structure Literal where
  variable : Nat
  negated : Bool
  deriving Repr, DecidableEq

def pos (i : Nat) : Literal := ⟨i, false⟩
def neg (i : Nat) : Literal := ⟨i, true⟩
def flip (l : Literal) : Literal := ⟨l.variable, !l.negated⟩
def evalLiteral (a : Assignment) (l : Literal) : Bool :=
  if l.negated then !(a.getD l.variable false) else a.getD l.variable false

abbrev Clause := List Literal

structure CNF where
  variables : Nat
  clauses : List Clause
  deriving Repr

def CNF.valid (F : CNF) : Bool :=
  F.clauses.all fun c => c.all fun l => decide (l.variable < F.variables)

def CNF.widthAtMost (F : CNF) (k : Nat) : Bool :=
  F.clauses.all fun c => decide (c.length ≤ k)

def CNF.eval (F : CNF) (a : Assignment) : Bool :=
  F.clauses.all fun c => c.any (evalLiteral a)

def CNF.sat (F : CNF) : Bool :=
  F.valid && (assignments F.variables).any F.eval

def CNF.count (F : CNF) : Nat :=
  if F.valid then ((assignments F.variables).filter F.eval).length else 0

inductive Gate where
  | const (value : Bool)
  | not (a : Nat)
  | and (a b : Nat)
  | or (a b : Nat)
  deriving Repr, DecidableEq

def Gate.refs : Gate → List Nat
  | .const _ => []
  | .not a => [a]
  | .and a b | .or a b => [a,b]

def Gate.eval (values : Assignment) : Gate → Bool
  | .const b => b
  | .not a => !(values.getD a false)
  | .and a b => values.getD a false && values.getD b false
  | .or a b => values.getD a false || values.getD b false

structure Circuit where
  inputs : Nat
  gates : List Gate
  output : Nat
  deriving Repr

def gateListValid : Nat → List Gate → Bool
  | _, [] => true
  | i, g :: gs => (g.refs.all fun j => decide (j < i)) && gateListValid (i+1) gs

def Circuit.valid (C : Circuit) : Bool :=
  gateListValid C.inputs C.gates && decide (C.output < C.inputs + C.gates.length)

def Circuit.extend (C : Circuit) (a : Assignment) : Assignment :=
  C.gates.foldl (fun values g => values ++ [g.eval values]) a

def Circuit.eval (C : Circuit) (a : Assignment) : Bool :=
  (C.extend a).getD C.output false

def Circuit.count (C : Circuit) : Nat :=
  if C.valid then ((assignments C.inputs).filter C.eval).length else 0

def gateClauses (z : Nat) : Gate → List Clause
  | .const true => [[pos z]]
  | .const false => [[neg z]]
  | .not a => [[pos z,pos a],[neg z,neg a]]
  | .and a b => [[neg z,pos a],[neg z,pos b],[pos z,neg a,neg b]]
  | .or a b => [[pos z,neg a],[pos z,neg b],[neg z,pos a,pos b]]

def gateConstraintsFrom : Nat → List Gate → List Clause
  | _, [] => []
  | i, g :: gs => gateClauses i g ++ gateConstraintsFrom (i+1) gs

def tseitin (C : Circuit) : CNF :=
  ⟨C.inputs + C.gates.length,
   gateConstraintsFrom C.inputs C.gates ++ [[pos C.output]]⟩

-- Explicit variable universe in CNF preserves unused input multiplicities.
-- If exporting to occurrence-only DIMACS, add [pos i,neg i] for every input.

def sumNat (xs : List Nat) : Nat := xs.foldl (· + ·) 0

def trueOccurrences (F : CNF) (i : Nat) (b : Bool) (j : Nat) : Nat :=
  ((F.clauses.getD j []).filter fun l =>
    decide (l.variable = i) && (b != l.negated)).length

def variableNumber (F : CNF) (i : Nat) (b : Bool) : Nat :=
  8^i + sumNat ((List.range F.clauses.length).map fun j =>
    trueOccurrences F i b j * 8^(F.variables+j))

def subsetNumbers (F : CNF) : List Nat :=
  (List.range F.variables).flatMap (fun i =>
    [variableNumber F i false, variableNumber F i true]) ++
  (List.range F.clauses.length).flatMap (fun j =>
    [8^(F.variables+j), 2*8^(F.variables+j)])

def subsetTarget (F : CNF) : Nat :=
  sumNat ((List.range F.variables).map fun i => 8^i) +
  4*sumNat ((List.range F.clauses.length).map fun j => 8^(F.variables+j))

def selectedSum (numbers : List Nat) (selection : Assignment) : Nat :=
  sumNat ((List.range numbers.length).map fun i =>
    if selection.getD i false then numbers.getD i 0 else 0)

def subsetCount (numbers : List Nat) (target : Nat) : Nat :=
  ((assignments numbers.length).filter fun a => decide (selectedSum numbers a = target)).length

def assignmentToSubset (F : CNF) (a : Assignment) : Assignment :=
  (List.range F.variables).flatMap (fun i =>
     [!(a.getD i false), a.getD i false]) ++
  F.clauses.flatMap (fun c =>
    let t := (c.filter (evalLiteral a)).length
    let slack := 4 - t
    [decide (slack % 2 = 1), decide ((slack / 2) % 2 = 1)])

def subsetToAssignment (F : CNF) (selection : Assignment) : Assignment :=
  (List.range F.variables).map fun i => selection.getD (2*i+1) false

def partitionFromSubset (numbers : List Nat) (target : Nat) : List Nat :=
  let s := sumNat numbers
  if target > s then [1]
  else if s = 0 then [1,1]
  else numbers ++ [2*s-target,s+target]

structure Graph where
  vertices : Nat
  adjacency : List (List Bool)
  deriving Repr

def Graph.edge (G : Graph) (u v : Nat) : Bool :=
  ((G.adjacency.getD u []).getD v false) && decide (u < G.vertices ∧ v < G.vertices)

def Graph.isCover (G : Graph) (a : Assignment) : Bool :=
  (List.range G.vertices).all fun u =>
    (List.range G.vertices).all fun v =>
      !(G.edge u v) || a.getD u false || a.getD v false

def Graph.isIndependent (G : Graph) (a : Assignment) : Bool :=
  (List.range G.vertices).all fun u =>
    (List.range G.vertices).all fun v =>
      !(a.getD u false && a.getD v false && G.edge u v)

structure Occurrence where
  clause : Nat
  literal : Literal
  deriving Repr

def occurrencesFrom : Nat → List Clause → List Occurrence
  | _, [] => []
  | i, c :: cs => c.map (fun l => ⟨i,l⟩) ++ occurrencesFrom (i+1) cs

def clauseClique (F : CNF) : Graph :=
  let vs := occurrencesFrom 0 F.clauses
  let default : Occurrence := ⟨0,pos 0⟩
  let edge := fun i j =>
    let a := vs.getD i default
    let b := vs.getD j default
    decide (a.clause ≠ b.clause) && decide (a.literal ≠ flip b.literal)
  ⟨vs.length, (List.range vs.length).map fun i => (List.range vs.length).map (edge i)⟩

-- 2SAT tables are explicit finite data, not a logspace implementation.
abbrev BoolTable := List (List Bool)
def tableAt (R : BoolTable) (u v : Nat) : Bool := (R.getD u []).getD v false

def implicationEdge (F : CNF) (u v : Nat) : Bool :=
  let code := fun (l : Literal) => 2*l.variable + (if l.negated then 1 else 0)
  let bar := fun i => if i % 2 = 0 then i+1 else i-1
  F.clauses.any fun c =>
    match c with
    | [] => false
    | [a] => decide (u = bar (code a) ∧ v = code a)
    | a :: b :: _ =>
      decide (u = bar (code a) ∧ v = code b) ||
      decide (u = bar (code b) ∧ v = code a)

def floydStep (size k : Nat) (R : BoolTable) : BoolTable :=
  (List.range size).map fun u => (List.range size).map fun v =>
    tableAt R u v || (tableAt R u k && tableAt R k v)

def implicationReach (F : CNF) : BoolTable :=
  let size := 2*F.variables
  let initial := (List.range size).map fun u => (List.range size).map fun v =>
    decide (u = v) || implicationEdge F u v
  (List.range size).foldl (fun R k => floydStep size k R) initial

def representative (size : Nat) (R : BoolTable) (u : Nat) : Nat :=
  ((List.range size).find? fun v => tableAt R u v && tableAt R v u).getD u

def componentKey (size : Nat) (R : BoolTable) (u : Nat) : Nat :=
  let r := representative size R u
  let reps := (List.range size).filter fun i => decide (representative size R i = i)
  (size+1) * (reps.filter fun d => tableAt R d r).length + r

def solveTwoSAT (F : CNF) : Option Assignment :=
  if !(F.valid && F.widthAtMost 2) || F.clauses.any List.isEmpty then none
  else
    let R := implicationReach F
    if (List.range F.variables).any (fun i => tableAt R (2*i) (2*i+1) && tableAt R (2*i+1) (2*i))
    then none
    else some ((List.range F.variables).map fun i =>
      decide (componentKey (2*F.variables) R (2*i) > componentKey (2*F.variables) R (2*i+1)))

-- Targets below are specifications to prove, NOT declared theorems.
/-
FINITE SEMANTIC TARGETS (prove without classical choice):

T01 assignments_complete:
  a ∈ assignments n ↔ a.length = n
T02 assignments_nodup:
  (assignments n).Nodup
T03 gate_clauses:
  whenever every reference is valid, a gate's clauses are true iff its output
  bit is Gate.eval of the preceding values. Proof: at most eight Boolean cases.
T04 circuit_prefix_unique:
  under C.valid=true and a.length=C.inputs, C.extend a is the unique vector
  of length C.inputs+C.gates.length that extends a and satisfies all gates.
T05 tseitin_forward:
  C.valid=true → a.length=C.inputs → C.eval a=true →
  (tseitin C).eval (C.extend a)=true
T06 tseitin_reverse_unique:
  C.valid=true → b.length=C.inputs+C.gates.length → (tseitin C).eval b=true →
  b = C.extend (b.take C.inputs) ∧ C.eval (b.take C.inputs)=true
T07 tseitin_count:
  C.valid=true → (tseitin C).count = C.count
T08 subset_forward:
  F.valid=true → F.widthAtMost 3=true → a.length=F.variables → F.eval a=true →
  selectedSum (subsetNumbers F) (assignmentToSubset F a)=subsetTarget F
T09 subset_inverse:
  under the same well-formedness and width hypotheses, every solution b of
  the target subset instance equals assignmentToSubset F (subsetToAssignment F b),
  and F.eval (subsetToAssignment F b)=true.
T10 subset_count:
  F.valid=true → F.widthAtMost 3=true →
  subsetCount (subsetNumbers F) (subsetTarget F)=F.count
T11 partition_correct:
  existence of a subset sum target is equivalent to existence of a half-total
  subset of partitionFromSubset numbers target. Split sum=0/target>sum cases.
T12 clique_witness_transport:
  satisfying assignments yield one compatible occurrence per clause, and any
  clique of clause-count size yields a satisfying assignment.
T13 complement_independent_cover:
  a.length=G.vertices → Graph.isIndependent G a=true ↔
  Graph.isCover G (a.map not)=true (for a well-formed undirected simple graph).
T14 floyd_invariant:
  after k stages, tableAt agrees with a coded path of length ≤2*v whose
  intermediate vertices are <k. Prove bounded path shortening first.
T15 component_keys:
  keys differ on distinct components and strictly increase on proper
  reachability of components. Prove by bounded counting of predecessor sets.
T16 two_sat_sound_complete:
  F.valid=true → F.widthAtMost 2=true →
  (solveTwoSAT F=none ↔ F.sat=false), and every returned assignment has length
  F.variables and satisfies F. The empty-clause branch needs a separate case.

REMAINING ALGORITHMS TO DEFINE (their exact finite pseudocode is in the report
and executable Python, so this is an implementation list rather than an
unspecified mathematical oracle):
* hornSweep/hornSolve: list fold setting positive heads of triggered Horn
  rules; iterate v times; check false-head rules; prove inclusion in every model.
* satPrefixSearch: v calls to a supplied exact SAT decision procedure, choosing
  bit zero whenever its prefix query is satisfiable; prove prefix extension.
* greedyCover: finite edge fold that selects disjoint edges and marks endpoints;
  prove maximality and inject each selected edge into every supplied cover.
* coverTree: explicit full binary tree of depth k, choosing an endpoint of the
  first uncovered edge; prove correctness by bounded tree-depth induction.

T17 dual_rail_circuit_horn:
  for each valid circuit with specified inputs, construct two rail variables
  per node, the gate-local Horn rules in N22, and the negative false-output
  unit; prove its satisfiability equals the evaluated output. Gate-prefix
  induction shows that the least positive-rule closure has exactly the
  correct rail at each node. Construct the logspace emitter separately.

COST AND OBJECT-LANGUAGE TARGETS (separate from the semantic targets):
* Construct the fixed numerical encodings and PR syntax for every definition.
* Encode assignments below 2^v, circuit arrays below 2^(inputs+gates), graph
  matrices below 2^(N*N), and paths below max(2,N)^(N+1).
* Build the machine-step-to-circuit compiler of theorem N03 with numerical
  gate indexing. Prove layer simulation, gate count ≤c*(T+1)^2, and logspace
  constructor work bound for each fixed verifier and fixed polynomial clock.
* Build concrete transducer machines for Tseitin, clique, subset sum,
  partition, 0–1 knapsack, and 0–1 integer constraints. Prove polynomial output
  length and polynomial tape time; PR definability alone is not a time bound.
* Apply fixed bounded-formula reflection to the prefix, digit, matrix, and
  search invariants, followed by quantifier-free induction in PRAAx.
* Prove N01 reduction composition at machine-code level (logspace composition
  uses recomputation of a virtual input, not storage of the whole intermediate).
* Compose the object proofs to obtain N05, N06, N07--N11, N15--N18, and N21.
* Keep the coNP and class-equality implications as implications between
  numerical presentations; never eliminate double negation of an unbounded
  semantic agreement assertion.
-/
end IPRAComplexity.ReductionOutline

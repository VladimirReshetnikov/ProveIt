/-
Canonical numerical machine semantics. STATUS: UNCOMPILED OUTLINE.
No omitted proof is asserted as a theorem. Pending targets are comments below.
These host definitions are not yet ConciseIPRA.PR syntax or PRAAx derivations.
Input: read-only, symbols left=0, bit0=1, bit1=2, right=3.
Work: one-sided base-3 digits blank=0, bit0=1, bit1=2.
States 0/1 reject/accept absorb; initial state 2; both heads start at zero.
Moves 0/1/2 mean left/stay/right; left clamps at zero. Input clamps at n+1.
Writes occur before movement; any budget escape, including with acceptance,
becomes the canonical rejecting sink. Invalid words or tables reject.
-/
import Std
namespace IPRAComplexity.CoreOutline

def bitAt (a i : Nat) : Nat := (a / 2^i) % 2
def wordLength (x : Nat) : Nat := x.log2

def packBits : List Nat → Nat
  | [] => 0
  | b :: bs => b % 2 + 2 * packBits bs

def word (bs : List Nat) : Nat := 2^bs.length + packBits bs

def wordBits (x : Nat) : List Nat :=
  (List.range (wordLength x)).map (bitAt x)

def fieldBits (w a : Nat) : List Nat := (List.range w).map (bitAt a)

def unaryAux (count : Nat) : List Nat → Option (Nat × List Nat)
  | [] => none
  | 0 :: bs => some (count, bs)
  | _ :: bs => unaryAux (count+1) bs

def unary (bs : List Nat) : Option (Nat × List Nat) := unaryAux 0 bs

structure Machine where
  states : Nat
  rules : List Nat
  deriving Repr, DecidableEq

def fieldWidth (q : Nat) : Nat := (27*q-1).log2 + 1

def Machine.valid (M : Machine) : Bool :=
  decide (3 ≤ M.states) && decide (M.rules.length = 12*M.states) &&
  M.rules.all (fun r => decide (r < 27*M.states))

def decodeMachine (e : Nat) : Option Machine :=
  if e = 0 then none else
  match unary (wordBits e) with
  | none => none
  | some (ones, rest) =>
    let q := ones+3
    let w := fieldWidth q
    let rs := (List.range (12*q)).map fun j => packBits ((rest.drop (j*w)).take w)
    if decide (rest.length = 12*q*w) && rs.all (fun r => decide (r < 27*q))
    then some ⟨q,rs⟩ else none

def encodeMachine (M : Machine) : Nat :=
  if M.valid then
    word (List.replicate (M.states-3) 1 ++ [0] ++
      M.rules.flatMap (fieldBits (fieldWidth M.states)))
  else 0

structure Rule where
  nextState : Nat
  writeSymbol : Nat
  inputMove : Nat
  workMove : Nat
  deriving Repr, DecidableEq

def ruleNumber (r : Rule) : Nat :=
  27*r.nextState + 9*r.writeSymbol + 3*r.inputMove + r.workMove

def decodeRule (r : Nat) : Rule :=
  ⟨r/27, (r/9)%3, (r/3)%3, r%3⟩

structure Config where
  state : Nat
  inputHead : Nat
  workHead : Nat
  tape : Nat
  deriving Repr, DecidableEq

def reject : Config := ⟨0,0,0,0⟩
def initial : Config := ⟨2,0,0,0⟩
def move (h d : Nat) : Nat := if d = 0 then h-1 else if d = 1 then h else h+1

def inputSymbol (x h : Nat) : Nat :=
  if h = 0 then 0 else
  if h = wordLength x + 1 then 3 else 1 + bitAt x (h-1)

def workSymbol (tape h : Nat) : Nat := (tape / 3^h) % 3

def writeCell (tape h symbol : Nat) : Nat :=
  tape - workSymbol tape h * 3^h + symbol * 3^h

def step (M : Machine) (x : Nat) (c : Config) : Config :=
  if c.state < 2 then c else
  if c.state ≥ M.states ∨ c.inputHead > wordLength x + 1 then reject else
  let a := inputSymbol x c.inputHead
  let b := workSymbol c.tape c.workHead
  let r := decodeRule (M.rules.getD (12*c.state+3*a+b) 0)
  ⟨r.nextState, min (move c.inputHead r.inputMove) (wordLength x+1),
   move c.workHead r.workMove, writeCell c.tape c.workHead r.writeSymbol⟩

def iterate (f : Config → Config) : Nat → Config → Config
  | 0, c => c
  | t+1, c => iterate f t (f c)

def run (e x t : Nat) : Config :=
  if x = 0 then reject else
  match decodeMachine e with
  | none => reject
  | some M => iterate (step M x) t initial

def accept (e x t : Nat) : Nat := if (run e x t).state = 1 then 1 else 0

def budgetStep (M : Machine) (x s : Nat) (c : Config) : Config :=
  if c.workHead ≥ s then reject else
  let d := step M x c
  if d.workHead ≥ s then reject else d

def budgetedRun (e x s t : Nat) : Config :=
  if x = 0 ∨ s = 0 then reject else
  match decodeMachine e with
  | none => reject
  | some M => iterate (budgetStep M x s) t initial

def configurationBound (e x s : Nat) : Nat :=
  let q := match decodeMachine e with | none => 3 | some M => M.states
  (q+2)*(wordLength x+2)*(s+1)*3^s

def spaceAccept (e x s : Nat) : Nat :=
  if (budgetedRun e x s (configurationBound e x s)).state = 1 then 1 else 0

def polynomialClock (c k n : Nat) : Nat := c*(n+1)^k

def selfDescription (e c k : Nat) : Nat :=
  if e = 0 ∨ c = 0 then 0 else
  let es := wordBits e
  word (List.replicate es.length 1 ++ [0] ++ es ++
        List.replicate c 1 ++ [0] ++ List.replicate k 1 ++ [0])

def parseSelfDescription (x : Nat) : Option (Nat × Nat × Nat) :=
  if x = 0 then none else
  match unary (wordBits x) with
  | none => none
  | some (m, tail) =>
    if tail.length < m then none else
    let e := word (tail.take m)
    match unary (tail.drop m) with
    | none => none
    | some (c, tail') =>
      match unary tail' with
      | none => none
      | some (k, tail'') =>
        if c = 0 ∨ tail''.isEmpty = false then none else some (e,c,k)

def diagonal (x : Nat) : Nat :=
  match parseSelfDescription x with
  | none => 0
  | some (e,c,k) => 1 - accept e x (polynomialClock c k (wordLength x))

/- PENDING PROOF TARGETS; these comments are NOT theorem declarations.
1. wordBits (word bs)=bs when all bs entries are 0/1; word (wordBits x)=x
   for x≥1. wordLength (word bs)=bs.length under the same bit condition.
2. Rule fields <(q,3,3,3) imply ruleNumber<27q and decodeRule roundtrip.
3. M.valid=true implies decodeMachine (encodeMachine M)=some M and exact
   payload length (M.states-2)+12*M.states*fieldWidth M.states.
4. decodeMachine e=some M implies M.valid=true and encodeMachine M=e.
5. writeCell replaces exactly its chosen ternary digit and preserves the
   others. Prove 3^h*workSymbol tape h ≤ tape before natural subtraction.
6. Valid runs preserve state<q, inputHead≤n+1, and workHead≤t. All symbols
   remain below 3, and the occupied tape prefix after t steps is bounded by
   t+1 cells. Halting states are absorbing; invalid descriptions reject.
7. Iteration composition and trace uniqueness: the invariant compares all
   trace entries i≤min(j,T) to the same bounded run, with PR trace-code bounds.
8. For s≥1, budgeted runs preserve workHead<s and tape<3^s. Escape is
   rejected even if the transition's proposed state was accepting.
9. Enumerate all configurations in mixed radix; at most
   (q+2)*(n+2)*(s+1)*3^s records suffice. A deterministic repeated nonhalting
   record cannot precede first acceptance. Hence the budgeted clock agrees
   with any supplied finite accepting budget-respecting trace.
10. parseSelfDescription (selfDescription e c k)=some(e,c,k) for e,c≥1;
    its word length is 2*wordLength e+c+k+3. Thus diagonal disagrees with
    the candidate's polynomialClock computation on that explicit word.
11. Build actual PR syntax for word operations, machine decoding, transition,
    iteration, budget checks, configuration bound, and self-description.
    Use fixed Boolean bounded invariants and the repository's bounded
    reflection/induction lemmas. Host definitions alone do not accomplish it.
12. Give a concrete tape interpreter with the report's polynomial overhead.
    Numeric exponentiation/digit access in these definitions are NOT assumed
    to cost one transition. Only then derive the resource-class theorems.
-/
end IPRAComplexity.CoreOutline

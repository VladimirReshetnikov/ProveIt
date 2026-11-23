/-
Finite randomness, counting, circuits, and lower bounds: semantic Lean outline.

STATUS: this file has not been compiled in the current environment. Its main
declarations are definitions of targets, not proofs of those targets. There
are no `axiom` declarations or `sorry` bodies. The two small recursion equations
at the start are the only proof declarations. They are not a certification of
the major complexity results or of object-language iPRA derivability.

The functions used as semantic parameters below must be replaced by the fixed
primitive-recursive code instances of the main report. Quantifying over a Lean
function type here does not add function quantifiers to iPRA. Polynomial clocks
and operational machine costs must be verified using the main machine module.
-/
import Std

namespace IPRAComplexity.CountingOutline

def sumBelow (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => sumBelow f n + f n

def indicator (b : Bool) : Nat := if b then 1 else 0

def countBelow (N : Nat) (p : Nat → Bool) : Nat :=
  sumBelow (fun i => indicator (p i)) N

theorem count_zero (p : Nat → Bool) : countBelow 0 p = 0 := rfl

theorem count_succ (N : Nat) (p : Nat → Bool) :
    countBelow (N+1) p = countBelow N p + indicator (p N) := rfl

def bit (table index : Nat) : Bool := decide (table / 2^index % 2 = 1)

def LeastWitnessSpec (N : Nat) (p : Nat → Bool) (w : Nat) : Prop :=
  w < N ∧ p w = true ∧ ∀ i, i < w → p i = false

def PositiveCountTarget : Prop :=
  ∀ (N : Nat) (p : Nat → Bool),
    0 < countBelow N p ↔ ∃ i, i < N ∧ p i = true

def UnionCountTarget : Prop :=
  ∀ (N k : Nat) (p : Nat → Nat → Bool),
    countBelow N (fun i => (List.range k).any (fun j => p j i)) ≤
      sumBelow (fun j => countBelow N (p j)) k

def ProductCountTarget : Prop :=
  ∀ (N M : Nat) (p q : Nat → Bool),
    sumBelow (fun i => sumBelow
      (fun j => indicator (p i && q j)) M) N =
      countBelow N p * countBelow M q

/- Input words are (n,x) with x < 2^n, allowing leading zero bits. The main
   word-code adapter translates these pairs to its nonzero binary word codes. -/
structure RandomFamily where
  coins : Nat → Nat
  run : Nat → Nat → Nat → Bool

abbrev Language := Nat → Nat → Bool

def seedCount (A : RandomFamily) (n : Nat) : Nat := 2^(A.coins n)

def accepts (A : RandomFamily) (n x : Nat) : Nat :=
  countBelow (seedCount A n) (A.run n x)

def errors (L : Language) (A : RandomFamily) (n x : Nat) : Nat :=
  countBelow (seedCount A n) (fun u => A.run n x u != L n x)

def RPspec (L : Language) (A : RandomFamily) : Prop :=
  ∀ n x, x < 2^n →
    (L n x = false → accepts A n x = 0) ∧
    (L n x = true → seedCount A n ≤ 2 * accepts A n x)

def coRPspec (L : Language) (A : RandomFamily) : Prop :=
  ∀ n x, x < 2^n →
    (L n x = true → accepts A n x = seedCount A n) ∧
    (L n x = false → 2 * accepts A n x ≤ seedCount A n)

def BPPspec (L : Language) (A : RandomFamily) : Prop :=
  ∀ n x, x < 2^n → 3 * errors L A n x ≤ seedCount A n

def PPspec (L : Language) (A : RandomFamily) : Prop :=
  ∀ n x, x < 2^n →
    (L n x = true ↔ seedCount A n < 2 * accepts A n x)

def PolynomialBound (f : Nat → Nat) : Prop :=
  ∃ c k, ∀ n, f n ≤ c * (n+1)^k

/- This definition is only the semantic majority constructor. In the machine
   development, generate each radix digit by streaming fixed-length blocks,
   maintain a counter of successes, and charge polynomial bit-operation cost. -/
def majority (A : RandomFamily) (d n x packed : Nat) : Bool :=
  let q := seedCount A n
  let k := 12*d
  decide (k < 2 * countBelow k
    (fun i => A.run n x (packed / q^i % q)))

def AmplificationTarget : Prop :=
  ∀ (L : Language) (A : RandomFamily), BPPspec L A →
    ∀ d n x, 0 < d → x < 2^n →
      2^d * countBelow ((seedCount A n)^(12*d))
        (fun u => majority A d n x u != L n x) <
      (seedCount A n)^(12*d)

/- R03 proof order:
   1. Define badTrials by a bounded sum over the packed seed tuple.
   2. Prove sum_{tuple} 2^badTrials = (Q+b)^k by induction on k.
   3. Majorities imply badTrials >= k/2; bound their count by this weighted sum.
   4. Derive 9^t*E <= 8^t*Q^(2t) using 3*b <= Q.
   5. Check 2*8^6 < 9^6 numerically and induct on d.
   Every induction invariant is an equality or inequality of bounded folds.
-/

def xorTranslate (m shift table : Nat) : Nat :=
  sumBelow (fun u => if bit table u then 2^(Nat.xor u shift) else 0) (2^m)

def covers (m k table shifts : Nat) : Bool :=
  (List.range (2^m)).all (fun u =>
    (List.range k).any (fun i =>
      bit table (Nat.xor u (shifts / (2^m)^i % (2^m)))))

def CoveringTarget : Prop :=
  ∀ m table, table < 2^(2^m) →
    2 * (2^m - countBelow (2^m) (bit table)) < 2^m →
    ∃ shifts, shifts < (2^m)^(m+1) ∧ covers m (m+1) table shifts = true

def NoncoveringTarget : Prop :=
  ∀ m k table, k * countBelow (2^m) (bit table) < 2^m →
    ∀ shifts, covers m k table shifts = false

/- R07 and R08:
   - advice: concatenate the bad seed tables for x < 2^n; union-count < Q;
     select the least missing seed and then use the clock-to-circuit compiler.
   - hierarchy: instantiate the cover and noncover targets with d=16(r+1)^2,
     m=12*d*r, k=m+1; prove k < 2^d before constructing the quantifier blocks.
   - represent shifts in radix 2^m; quantified tuple bound is (2^m)^k.
-/

inductive TrialAnswer where
  | zero | one | unknown
  deriving DecidableEq, Repr

structure ZeroTrial where
  coins : Nat → Nat
  run : Nat → Nat → Nat → TrialAnswer

def answerAgrees (b : Bool) : TrialAnswer → Bool
  | .zero => !b
  | .one => b
  | .unknown => true

def TrialSound (L : Language) (Z : ZeroTrial) : Prop :=
  ∀ n x u, x < 2^n → u < 2^(Z.coins n) →
    answerAgrees (L n x) (Z.run n x u) = true

def TrialHalfSuccess (Z : ZeroTrial) : Prop :=
  ∀ n x, x < 2^n → 2^(Z.coins n) ≤
    2 * countBelow (2^(Z.coins n))
      (fun u => decide (Z.run n x u ≠ .unknown))

/- A machine truncated at T inspects at most T random bits. This structure is
   an interface for the operational simulator, not a claimed implementation.
   Its consistency/simulation obligations must be proved when instantiated. -/
structure TruncatedMachine where
  answer : Nat → Nat → Nat → Nat → TrialAnswer
  used : Nat → Nat → Nat → Nat → Nat

def FiniteExpectedCertificate (Z : TruncatedMachine) (p : Nat → Nat) : Prop :=
  ∀ n x T, x < 2^n →
    sumBelow (Z.used n x T) (2^T) ≤ p n * 2^T

def FiniteTraceSound (L : Language) (Z : TruncatedMachine) : Prop :=
  ∀ n x T u, x < 2^n → u < 2^T →
    answerAgrees (L n x) (Z.answer n x T u) = true

/- R09 obligations include: unknown at time T implies used=T; later traces
   extend earlier traces; halting outputs remain fixed; extra seed suffixes
   do not alter an earlier computation. These are essential operational facts.
   Restart construction: Q-block product counts, finite tail-sum identity,
   sum of costs for arbitrary cap T after extending to ceil(T/p)*p bits.
-/

structure Gate where
  truth : Nat
  left : Nat
  right : Nat
  deriving Repr

structure Circuit where
  gates : List Gate
  output : Nat
  deriving Repr

def gateEval (g : Gate) (values : List Bool) : Bool :=
  bit g.truth (2 * indicator (values.getD g.left false) +
    indicator (values.getD g.right false))

def circuitEval (n : Nat) (C : Circuit) (x : Nat) : Bool :=
  let input := (List.range n).map (fun i => bit x i) ++ [false, true]
  let values := C.gates.foldl (fun values g => values ++ [gateEval g values]) input
  values.getD C.output false

def CircuitValid (n : Nat) (C : Circuit) : Prop :=
  C.output < n + 2 + C.gates.length ∧
  ∀ i g, C.gates[i]? = some g →
    g.truth < 16 ∧ g.left < n+2+i ∧ g.right < n+2+i

def circuitTable (n : Nat) (C : Circuit) : Nat :=
  sumBelow (fun x => if circuitEval n C x then 2^x else 0) (2^n)

def circuitDescriptionBound (n s : Nat) : Nat :=
  (n+s+2) * (16*(n+s+2)^2)^s

def HardTableSpec (n s h : Nat) : Prop :=
  h < 2^(2^n) ∧ ∀ C : Circuit,
    CircuitValid n C → C.gates.length ≤ s →
    ∃ x, x < 2^n ∧ circuitEval n C x ≠ bit h x

def ShannonTarget : Prop :=
  ∀ n, 4 ≤ n → ∃ h, HardTableSpec n (2^n / (16*(n+1))) h

def CircuitUpperTarget : Prop :=
  ∀ n h, 64 ≤ n → h < 2^(2^n) → ∃ C : Circuit,
    CircuitValid n C ∧ n * C.gates.length ≤ 18 * 2^n ∧
    ∀ x, x < 2^n → circuitEval n C x = bit h x

/- R10--R13 proof path:
   circuit syntax coding -> valid radix descriptions -> truth-table evaluator;
   occupancy-count invariant -> bounded missing-table scan;
   explicit exponent inequality n+(4+2*n)*s <= 2^(n-1);
   DNF compiler -> prefix-indicator compiler -> residual-table library;
   workspace audit for simultaneous candidate table, circuit, and counters.
   The large witnesses are allowed to be PR; none are called polynomial-time.
-/

inductive QueryTree where
  | leaf (output : Bool)
  | node (index : Nat) (zero one : QueryTree)

def queryEval : QueryTree → Nat → Bool
  | .leaf b, _ => b
  | .node i zero one, x => if bit x i then queryEval one x else queryEval zero x

def queryDepth : QueryTree → Nat
  | .leaf _ => 0
  | .node _ zero one => 1 + max (queryDepth zero) (queryDepth one)

def queryLeaves : QueryTree → Nat
  | .leaf _ => 1
  | .node _ zero one => queryLeaves zero + queryLeaves one

def QueryValid (n : Nat) : QueryTree → Prop
  | .leaf _ => True
  | .node i zero one => i < n ∧ QueryValid n zero ∧ QueryValid n one

def parity (n x : Nat) : Bool :=
  decide (countBelow n (bit x) % 2 = 1)

def ParityPairingTarget : Prop :=
  ∀ n T, QueryValid n T → queryDepth T < n →
    2 * countBelow (2^n) (fun x => queryEval T x == parity n x) = 2^n

inductive CompareTree where
  | leaf (order : List Nat)
  | node (leftIndex rightIndex : Nat) (le gt : CompareTree)

def compareEval : CompareTree → List Nat → List Nat
  | .leaf order, _ => order
  | .node i j le gt, keys =>
    if keys.getD i 0 ≤ keys.getD j 0 then compareEval le keys else compareEval gt keys

def compareDepth : CompareTree → Nat
  | .leaf _ => 0
  | .node _ _ le gt => 1 + max (compareDepth le) (compareDepth gt)

def CorrectSort (n : Nat) (T : CompareTree) : Prop :=
  ∀ keys : List Nat, keys.Perm (List.range n) →
    (compareEval T keys).Perm (List.range n) ∧
    (compareEval T keys).map (fun i => keys.getD i 0) = List.range n

def factorial : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * factorial n

def SortingLowerTarget : Prop :=
  ∀ n T, CorrectSort n T → factorial n ≤ 2^(compareDepth T)

inductive CommTree where
  | leaf (output : Bool)
  | node (aliceSpeaks : Bool) (testTable : Nat) (zero one : CommTree)

def commEval : CommTree → Nat → Nat → Bool
  | .leaf b, _, _ => b
  | .node alice table zero one, x, y =>
    if bit table (if alice then x else y)
    then commEval one x y else commEval zero x y

def commDepth : CommTree → Nat
  | .leaf _ => 0
  | .node _ _ zero one => 1 + max (commDepth zero) (commDepth one)

def EqualityCommTarget : Prop :=
  ∀ n T, 0 < n →
    (∀ x y, x < 2^n → y < 2^n → commEval T x y = decide (x = y)) →
    n+1 ≤ commDepth T

def PotentialTarget : Prop :=
  ∀ (m : Nat) (cost charge potential : Nat → Nat),
    (∀ i, i < m → cost i + potential (i+1) ≤ charge i + potential i) →
    sumBelow cost m + potential m ≤ sumBelow charge m + potential 0

/- R14--R23 proof path:
   finite path codes and leaf counts -> permutation-to-leaf injection;
   transcript-preserving bit flip -> deterministic query bounds;
   per-leaf missing-bit involution -> randomized parity count;
   coupled zero/unit-vector traces -> randomized OR incidence inequalities;
   row/column restrictions on a protocol path -> rectangle invariant;
   diagonal input pairs -> equality leaf lower bound;
   mask-bit involution -> public-coin fingerprint collision count;
   arithmetic partial-sum induction -> weighted costs and potential method.

Object-iPRA lowering: compile every finite list/tree to the repository's
natural-number sequence code; use only an explicit depth/step clock for
evaluation. Replace each displayed bounded predicate by its Boolean code.
Generate QF induction derivations for the indicated numerical invariants.
Finally show the resulting code is accepted by the repository's proof checker.
Neither these comments nor an ambient Lean proof of the target proposition
would themselves finish that final proof-lowering obligation.
-/

end IPRAComplexity.CountingOutline

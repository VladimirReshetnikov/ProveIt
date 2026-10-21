import BusyBeaver.ZFC.RMNormalizedBisim

/-!
Automatic correspondence inference for finite Wade source trees.

The generator pairs decrement/halt leaves in their left-to-right order and
computes successor indices from the first tree. It is intentionally heuristic:
it need not succeed for every equivalent pair. Its output is accepted only by
the existing, proved normalized segment checker. Thus no correctness premise
about this generator or about an external path-pairing file enters the theorem.

At run time no change is made to either register program or Turing machine.
-/

namespace SetTheory.BusyBeaver.ZFC.RMAutoCertificate
open RegisterPath RMBisim

def isCheckpoint : Edge → Bool
  | .decnz _ | .halt => true
  | _ => false

/-- Ordered checkpoint paths, using complete consumed root-to-leaf paths. -/
def checkpointPaths : Tree → List Bool → List (List Bool)
  | .none, _ => []
  | .leaf e, rev => if isCheckpoint e then [rev.reverse] else []
  | .node l r, rev =>
      checkpointPaths l (false :: rev) ++ checkpointPaths r (true :: rev)

def checkpointCount : Tree → Nat
  | .none => 0
  | .leaf e => if isCheckpoint e then 1 else 0
  | .node l r => checkpointCount l + checkpointCount r

/-- Rank the checkpoint observed from a zero-extended path. -/
def checkpointRank : Tree → List Bool → Option Nat
  | .none, _ => none
  | .leaf e, _ => if isCheckpoint e then some 0 else none
  | .node l _, [] => checkpointRank l []
  | .node l r, b :: P =>
      if b then (checkpointRank r P).map (checkpointCount l + ·)
      else checkpointRank l P

def encodePath (P : List Bool) : Nat :=
  P.foldl (fun n b => 2 * n + if b then 1 else 0) 1

/-- Failure is retained as a deliberately impossible-to-trust guess. The
checker, not the generator, is responsible for validating the destination. -/
def successor (t : Tree) (P : List Bool) : Nat :=
  match seg t segFuel P with
  | some (_, Q) => (checkpointRank t Q).getD 0
  | none => 0

def entry (t : Tree) (P Q : List Bool) : Entry :=
  match tsite t P with
  | some (.decnz _, A) =>
      (encodePath P, encodePath Q,
        successor t (incPath A), successor t (breakPath 1 A))
  | _ => (encodePath P, encodePath Q, 0, 0)

def entries (t1 t2 : Tree) : List Entry :=
  ((checkpointPaths t1 []).zip (checkpointPaths t2 [])).map
    (fun pq => entry t1 pq.1 pq.2)

/-- Fuel only bounds certificate construction; exhaustion cannot make the
separate semantic checker accept an invalid correspondence. -/
def balanced : Nat → List Entry → CTree
  | 0, _ => .empty
  | _ + 1, [] => .empty
  | _ + 1, [x] => .leaf x
  | f + 1, xs =>
      let c := xs.length / 2
      .branch c (balanced f (xs.take c)) (balanced f (xs.drop c))

def certificate (t1 t2 : Tree) : CTree := balanced 32 (entries t1 t2)

/-- The interface has no explicit correspondence input. The kernel checks
both finite obligations after synthesizing it from the two literal trees. -/
theorem halts_iff {p1 p2 : Program}
    (hs : RMNormalizedBisim.branchOk (ptree p1) (ptree p2)
      (certificate (ptree p1) (ptree p2)) [] [] 0 = true)
    (ha : allC (RMNormalizedBisim.entryOk (ptree p1) (ptree p2)
      (certificate (ptree p1) (ptree p2)))
      (certificate (ptree p1) (ptree p2)) = true) (R : Registers) :
    Halts p1 ⟨[], R⟩ ↔ Halts p2 ⟨[], R⟩ :=
  RMNormalizedBisim.check_halts_iff hs ha R

#print axioms halts_iff
end SetTheory.BusyBeaver.ZFC.RMAutoCertificate

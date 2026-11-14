#!/usr/bin/env python3
"""Generate a Lean kernel-checkable local quotient certificate from the frozen archive."""
import hashlib
import json
import sys
from pathlib import Path

if sys.flags.optimize:
    raise SystemExit('Python optimization disables required archive assertions')

root = Path(__file__).resolve().parents[5]
sys.path.insert(0, str(root / 'Computability/BusyBeaver/Research/PA'))
from packet_inputs import PlacedPacket
out = Path(sys.argv[1]) if len(sys.argv) == 2 else Path(__file__).with_name('PA194LocalQuotient.lean')
if len(sys.argv) > 2:
    raise SystemExit('usage: generate.py [OUTPUT.lean]')
with PlacedPacket(root, '194') as z:
    prefix = 'pa194_conpa/construction/'
    dense = z.read(prefix + 'tables/pa194.tm')
    assert hashlib.sha256(dense).hexdigest() == '4bfea62b17aad7d8c8c5e682fe8942e0a86b93e4351f8e675e32705bdaae007f'
    def rows(name):
        result = []
        for line in z.read(prefix + name).decode().splitlines():
            q, b, w, direction, target = line.split()
            assert direction in ('L', 'R')
            result.append((int(q), int(b), int(w), direction == 'R', int(target)))
        assert len({(q, b) for q, b, *_ in result}) == len(result)
        return result
    parent = rows('tables/unfolded201.native.tm')
    child = rows('tables/pa194.native.tm')
    dense_rows = rows('tables/pa194.tm')
    labels = json.loads(z.read(prefix + 'tables/pa194.labels.json'))
    folds = json.loads(z.read(prefix + 'source/pa194.folds.json'))
    cert = json.loads(z.read(prefix + 'evidence/pa194.local-cases.json'))
assert len(parent) == 402 and len(child) == len(dense_rows) == 388 and len(folds) == 7
assert len(labels) == 195 and len(set(labels)) == 195 and labels[0] == 74 and labels[194] == 254
assert {(labels[q], b, w, d, labels[t]) for q, b, w, d, t in dense_rows} == set(child)
cases = [(v['old_state'], v['history_bit'], v['current_bit'], v['duration']) for v in cert['cases']]
assert len(cases) == 28

def boolean(x): return 'true' if x else 'false'
def table(rs):
    return ',\n'.join(f'  ⟨{q}, {boolean(b)}, {boolean(w)}, {boolean(d)}, {t}⟩' for q,b,w,d,t in rs)
def lean_cases(rs):
    return ',\n'.join(f'  ⟨{q}, {boolean(l)}, {boolean(b)}, {k}⟩' for q,l,b,k in rs)
pairs = ',\n'.join(f'  ({p[0]}, {p[1]})' for p in folds)
head = '''import Mathlib.Data.Int.Basic

/-! Kernel computation verifies the 28 local simulations and incoming-history
conditions directly against the two complete native transition tables extracted
from the PA194 research archive. Head positions are relative to the original
head: -1 and 0 are the two cells the folded run is allowed to inspect.

This is a finite local certificate. It does not by itself prove a trace-level
or all-model halting equivalence, nor any consistency implication. See
`generate.py` for archive binding and table extraction. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PA194LocalQuotient

structure Row where
  state : Nat
  read : Bool
  write : Bool
  right : Bool
  target : Nat
  deriving DecidableEq, Repr

def parent : List Row := [
'''
body = '''
]

def folded : List Row := [
'''
tail = '''
]

def dense : List Row := [
'''
tail_labels = '''
]

def labels : List Nat := [
'''
tail_folds = '''
]

def folds : List (Nat × Nat) := [
'''
tail2 = '''
]

structure Case where
  state : Nat
  left : Bool
  read : Bool
  duration : Nat
  deriving DecidableEq, Repr

def cases : List Case := [
'''
finish = '''
]

def project (q : Nat) : Nat :=
  match folds.find? (fun pair => pair.1 == q) with
  | some pair => pair.2
  | none => q

def lookup (rows : List Row) (q : Nat) (b : Bool) : Option Row :=
  rows.find? (fun row => row.state == q && row.read == b)

structure Window where
  state : Nat
  pos : Int
  left : Bool
  here : Bool
  deriving DecidableEq, Repr

/-- `none` means no table row or an attempted read outside the two cells. -/
def localStep (rows : List Row) (c : Window) : Option Window := do
  let bit ← if c.pos == -1 then some c.left else if c.pos == 0 then some c.here else none
  let row ← lookup rows c.state bit
  let left := if c.pos == -1 then row.write else c.left
  let here := if c.pos == 0 then row.write else c.here
  return ⟨row.target, c.pos + (if row.right then 1 else -1), left, here⟩

def localRun (rows : List Row) : Nat → Window → Option Window
  | 0, c => some c
  | n + 1, c => (localStep rows c).bind (localRun rows n)

def checkCase (c : Case) : Bool :=
  let initial : Window := ⟨c.state, 0, c.left, c.read⟩
  let projected : Window := ⟨project c.state, 0, c.left, c.read⟩
  match localStep parent initial, localRun folded c.duration projected with
  | some a, some b => b == {a with state := project a.state}
  | _, _ => false

/-- Every transition entering a folded reader carries the claimed left bit. -/
def incomingGood (row : Row) : Bool :=
  folds.all fun pair =>
    (if row.target == pair.1 then !row.write && row.right else true) &&
    (if row.target == pair.2 then row.write && row.right else true)

/-- Transitions from all nonfolded parent controls commute with projection. -/
def ordinaryGood (row : Row) : Bool :=
  if folds.any (fun pair => row.state == pair.1 || row.state == pair.2) then true
  else match lookup folded (project row.state) row.read with
    | some out => out.write == row.write && out.right == row.right &&
        out.target == project row.target
    | none => false

/-- Every dense row is the corresponding native row under `labels`. -/
def denseGood (row : Row) : Bool :=
  match labels[row.state]?, labels[row.target]? with
  | some q, some t =>
    match lookup folded q row.read with
    | some out => out.write == row.write && out.right == row.right && out.target == t
    | none => false
  | _, _ => false

def casesCover : Bool := folds.all fun pair =>
  [false, true].all fun bit =>
    cases.any (fun c => c.state == pair.1 && !c.left && c.read == bit) &&
    cases.any (fun c => c.state == pair.2 && c.left && c.read == bit)

theorem finite_certificate :
    parent.length = 402 ∧ folded.length = 388 ∧ folds.length = 7 ∧
    dense.length = 388 ∧ labels.length = 195 ∧ dense.all denseGood = true ∧
    cases.length = 28 ∧ casesCover = true ∧
    cases.all checkCase = true ∧ parent.all incomingGood = true ∧
    parent.all ordinaryGood = true := by decide +kernel

#print axioms finite_certificate
end PA194LocalQuotient
'''
out.write_text(head + table(parent) + body + table(child) + tail + table(dense_rows) + tail_labels + ', '.join(map(str, labels)) + tail_folds + pairs + tail2 + lean_cases(cases) + finish)
print(out)

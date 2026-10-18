#!/usr/bin/env python3
"""Generate the exact routing245 Lean table and its finite graph interface.

Uses only the standard library and frozen text data. It invokes no compiler,
build system, imported report code, or external program. --check writes nothing.
Lean must separately check the emitted proofs. The fixed table has 245 working
states; numerical halt 245 retains its final write and movement as Core `none`.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
PINS = {
    "canonical": "17f4d430747c4a0cd580dc2cc13ea06a74ce7f51f12be4c2d12f6a646691dd13",
    "old": "f8dbeacdad5fd89c57e3f240781324b09110be8e0ccdb838a9c710fb28d2a267",
    "renumbering": "ff8f44548b4f121c2d8838d56fb9c7ccabcc7e78d678cab518fb3c3b5569ba76"
}

HEADER = '''import BusyBeaver.Core

/-!
Exact245-state routing/reassociation table in canonical numbering.
Canonical source SHA-256:
17f4d430747c4a0cd580dc2cc13ea06a74ce7f51f12be4c2d12f6a646691dd13.
Old-label source SHA-256:
f8dbeacdad5fd89c57e3f240781324b09110be8e0ccdb838a9c710fb28d2a267.
There are490 literal actions. Start old95 is canonical0; dispatcher old96
is canonical88. The numerical halt245 is interpreted as Core none, retaining
its final write and head movement. Old74,177,208 are repurposed grammar labels.

Mira-Cult designed the original machine and compact calculus; Jeff Ketchersid
supplied its verification; Andrew James Wade supplied the compiler framework.
Earlier permutation252 and contextual-fold246 developments retain their
attribution. Submission8286787dd0 contributes joint source-grammar/routing
optimization and scanner shortening. Adapted from checked TablePrefix246.
This source imports exact literal data and finite graph facts only. No runtime,
blank bootstrap, nonhalting, consistency, or source-program equivalence is
established here.
-/

namespace SetTheory.BusyBeaver.ZFC

abbrev RawActionRouting245 := Bool × Move × Nat

/-- Literal read-zero/read-one actions, indexed by canonical working state. -/
def rawTableRouting245 : Array (RawActionRouting245 × RawActionRouting245) := #[
'''

BODY = '''
]

theorem rawTableRouting245_size : rawTableRouting245.size = 245 := by decide +kernel

theorem rawTableRouting245_transition_count :
    (rawTableRouting245.toList.flatMap (fun row => [row.1, row.2])).length = 490 := by decide +kernel

theorem rawTableRouting245_targets_bounded :
    rawTableRouting245.toList.all (fun row =>
      decide (row.1.2.2 ≤ 245 ∧ row.2.2.2 ≤ 245)) = true := by decide +kernel

theorem rawTableRouting245_halt_edge_count :
    ((rawTableRouting245.toList.flatMap (fun row => [row.1.2.2, row.2.2.2])).filter
      (fun target => target == 245)).length = 1 := by decide +kernel

/-- The fallback cannot be reached by Fin 245 indices, by the size theorem. -/
def rawActionRouting245 (state : Fin 245) (bit : Bool) : RawActionRouting245 :=
  let row := rawTableRouting245.getD state.val
    ((false, .right, 245), (false, .right, 245))
  if bit then row.2 else row.1

def actionRouting245 (state : Fin 245) (bit : Bool) : Action 245 :=
  let raw := rawActionRouting245 state bit
  { write := raw.1, move := raw.2.1,
    next := if h : raw.2.2 < 245 then some ⟨raw.2.2, h⟩ else none }

def machineRouting245 : Machine 245 where
  transition := actionRouting245

def typedMachineRouting245 : TypedMachine (Fin 245) where
  transition state bit :=
    let a := actionRouting245 state bit
    { write := a.write, move := a.move, next := a.next }

theorem rawActionRouting245_target_bounded : ∀ (q : Fin 245) (b : Bool),
    (rawActionRouting245 q b).2.2 ≤ 245 := by decide +kernel

/-- All 245 old working labels, in canonical order. -/
def oldLabelsRouting245 : Array Nat := #[
'''

MAPPING = '''
]

theorem oldLabelsRouting245_size : oldLabelsRouting245.size = 245 := by decide +kernel

/-- The original label of a canonical working state. -/
def oldLabelRouting245 (q : Fin 245) : Nat := oldLabelsRouting245.getD q.val 95

/-- Exact inverse on old working labels. Absent and terminal labels map to 0;
    this total fallback has no claim to represent an absent operational state. -/
def oldStateRouting245 : Nat → Fin 245
'''

FOOTER = '''
  | _ => 0

theorem oldStateRouting245_oldLabel : ∀ q : Fin 245,
    oldStateRouting245 (oldLabelRouting245 q) = q := by decide +kernel

theorem oldLabelRouting245_injective {q r : Fin 245}
    (h : oldLabelRouting245 q = oldLabelRouting245 r) : q = r := by
  calc
    q = oldStateRouting245 (oldLabelRouting245 q) := (oldStateRouting245_oldLabel q).symm
    _ = oldStateRouting245 (oldLabelRouting245 r) := congrArg oldStateRouting245 h
    _ = r := oldStateRouting245_oldLabel r

def startRouting245 : Fin 245 := 0
def dispatchRouting245 : Fin 245 := oldStateRouting245 96

theorem startRouting245_old95 : startRouting245 = oldStateRouting245 95 := by decide +kernel
theorem dispatchRouting245_eq : dispatchRouting245 = 88 := by decide +kernel

theorem machineRouting245_initial_action :
    machineRouting245.transition startRouting245 false =
      ⟨true, .right, some (oldStateRouting245 109)⟩ := by decide +kernel

/-- The single terminal action is old77/read-one, with its final write/move. -/
theorem machineRouting245_halt_action :
    machineRouting245.transition (oldStateRouting245 77) true =
      ⟨true, .right, none⟩ := by decide +kernel

theorem machineRouting245_halt_iff : ∀ (q : Fin 245) (b : Bool),
    (machineRouting245.transition q b).next = none ↔
      q = oldStateRouting245 77 ∧ b = true := by decide +kernel

/-- The initial read-zero successor has exactly one incoming action. -/
theorem machineRouting245_into_old109_iff : ∀ (q : Fin 245) (b : Bool),
    (machineRouting245.transition q b).next = some (oldStateRouting245 109) ↔
      q = oldStateRouting245 95 ∧ b = false := by decide +kernel

/-- The folded pulse state is entered from old75 or its own read-zero loop. -/
theorem machineRouting245_into_old255_iff : ∀ (q : Fin 245) (b : Bool),
    (machineRouting245.transition q b).next = some (oldStateRouting245 255) ↔
      (q = oldStateRouting245 75 ∨ q = oldStateRouting245 255) ∧ b = false := by decide +kernel

theorem oldStateRouting245_95 : oldStateRouting245 95 = 0 := by decide +kernel
theorem oldStateRouting245_83_ne_95 : oldStateRouting245 83 ≠ oldStateRouting245 95 := by decide +kernel
theorem oldStateRouting245_83_ne_255 : oldStateRouting245 83 ≠ oldStateRouting245 255 := by decide +kernel
'''

ROW_KEYS = [(75, 0), (75, 1), (255, 0), (255, 1), (60, 0), (60, 1), (112, 0), (131, 1), (73, 0), (73, 1), (83, 0), (83, 1), (95, 0), (95, 1), (109, 0), (109, 1), (112, 1), (131, 0), (48, 0), (48, 1), (63, 0), (63, 1), (20, 0), (20, 1), (2, 0), (2, 1), (4, 0), (4, 1), (6, 1), (44, 0), (44, 1), (31, 0), (31, 1), (56, 0), (56, 1), (38, 0), (38, 1), (40, 0), (40, 1), (28, 0), (28, 1), (64, 0), (64, 1), (69, 0), (69, 1), (6, 0)]

def pinned(path, kind):
    data = path.read_bytes()
    if hashlib.sha256(data).hexdigest() != PINS[kind]:
        raise ValueError(f"changed {kind} input: {path}")
    return data

def parse(data):
    start, rows = None, {}
    for line in data.decode('ascii').splitlines():
        if line.startswith('#! start '):
            if start is not None: raise ValueError('duplicate start')
            start = int(line.split()[-1])
        if not line or line.startswith('#'): continue
        q,b,w,d,t = line.split()
        q,b,w,t = map(int,(q,b,w,t))
        if (q,b) in rows or b not in (0,1) or w not in (0,1) or d not in ('L','R'):
            raise ValueError('invalid or duplicate row')
        rows[q,b]=(w,d,t)
    return start, rows

def generate(canonical, old, renumbering):
    start, rows = parse(pinned(canonical,'canonical'))
    oldstart, oldrows = parse(pinned(old,'old'))
    mapping = json.loads(pinned(renumbering,'renumbering'))
    labels = mapping['canonical_to_old']
    oldnew = {int(k):v for k,v in mapping['old_to_canonical'].items()}
    if start != 0 or oldstart != 95 or len(labels) != 245 or len(set(labels)) != 245:
        raise ValueError('invalid start or state census')
    if oldnew != {**{q:i for i,q in enumerate(labels)},254:245}:
        raise ValueError('renumbering is not the exact bijection plus terminal')
    if set(rows) != {(q,b) for q in range(245) for b in (0,1)}:
        raise ValueError('canonical table is not exactly 490 total rows')
    if set(oldrows) != {(q,b) for q in labels for b in (0,1)}:
        raise ValueError('old table domains differ')
    converted = {(oldnew[q],b):(w,d,oldnew[t]) for (q,b),(w,d,t) in oldrows.items()}
    if converted != rows or any(t>245 for w,d,t in rows.values()):
        raise ValueError('row-by-row renumbering or target bound failed')
    if [(q,b) for (q,b),(w,d,t) in rows.items() if t==245] != [(71,1)]:
        raise ValueError('unexpected halt edge')
    if oldnew[96] != 88: raise ValueError('wrong dispatch state')
    for target, incoming in [(109,{(95,0)}),(255,{(75,0),(255,0)})]:
        if {k for k,v in oldrows.items() if v[2]==target} != incoming:
            raise ValueError('incoming graph changed')
    def literal(row):
        w,d,t=row
        return f"({'true' if w else 'false'}, .{'right' if d=='R' else 'left'}, {t})"
    lines=[f"  ({literal(rows[q,0])}, {literal(rows[q,1])}){',' if q<244 else ''} -- {q}; old{labels[q]}" for q in range(245)]
    text=HEADER+'\n'.join(lines)+BODY
    text+='\n'.join('  '+', '.join(map(str,labels[i:i+20]))+(',' if i+20<245 else '') for i in range(0,245,20))
    text+=MAPPING+'\n'.join(f'  | {old} => {new}' for new,old in enumerate(labels))+FOOTER
    for q,b in ROW_KEYS:
        w,d,t=oldrows[q,b]
        if t==254: raise ValueError('unexpected key-row halt')
        bs='true' if b else 'false'
        text+=f'''\ntheorem rowRouting245_old{q}_{bs} :
    machineRouting245.transition (oldStateRouting245 {q}) {bs} =
      ⟨{'true' if w else 'false'}, .{'right' if d=='R' else 'left'}, some (oldStateRouting245 {t})⟩ := by decide +kernel
'''
    return text+'\nend SetTheory.BusyBeaver.ZFC\n'

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source',type=Path,default=HERE/'candidate-routing245/zfc_routing245.tm')
    p.add_argument('--old-source',type=Path,default=HERE/'candidate-routing245/zfc_routing245_old.tm')
    p.add_argument('--renumbering',type=Path,default=HERE/'candidate-routing245/renumbering.json')
    p.add_argument('--output',type=Path,default=REPO/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/TableRouting245.lean')
    p.add_argument('--check',action='store_true')
    a=p.parse_args()
    result=generate(a.source,a.old_source,a.renumbering)
    if a.check:
        if a.output.read_text()!=result: raise ValueError('generated source differs')
    else:
        a.output.parent.mkdir(parents=True,exist_ok=True)
        a.output.write_text(result)
    print(json.dumps({'status':'IDENTICAL' if a.check else 'GENERATED','working_states':245,
        'transition_rows':490,'start':0,'dispatch':88,'halt':245,'input_sha256':PINS,
        'source_sha256':hashlib.sha256(result.encode()).hexdigest(),'kernel_checked':False}))

if __name__=='__main__':main()

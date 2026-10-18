#!/usr/bin/env python3
"""Generate the untrusted exact245 balanced transition tree.

Only standard-library parsing runs. The finite table equality and complete
machine equality still require Lean checking. No startup data are generated.
No report code, compiler, dependency build, or external process is invoked.
"""
from __future__ import annotations
import argparse
import hashlib
from pathlib import Path

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[3]
PIN='17f4d430747c4a0cd580dc2cc13ea06a74ce7f51f12be4c2d12f6a646691dd13'

def parse(path):
    data=path.read_bytes()
    if hashlib.sha256(data).hexdigest()!=PIN:raise ValueError('changed canonical source')
    rows={}; start=None
    for line in data.decode('ascii').splitlines():
        if line.startswith('#! start '):start=int(line.split()[-1])
        if not line or line.startswith('#'):continue
        q,b,w,d,t=line.split(); q,b,w,t=map(int,(q,b,w,t))
        if (q,b) in rows or b not in (0,1) or w not in (0,1) or d not in ('L','R') or not 0<=t<=245:
            raise ValueError('malformed canonical row')
        rows[q,b]=(w,d,t)
    if start!=0 or set(rows)!={(q,b) for q in range(245) for b in (0,1)}:
        raise ValueError('wrong table census or start')
    return rows

def action(row):
    w,d,t=row
    nxt='none' if t==245 else f'some ⟨{t}, by decide⟩'
    return f'⟨{"true" if w else "false"}, .{"right" if d=="R" else "left"}, {nxt}⟩'

def tree(rows,level=1):
    indent='  '*level
    if len(rows)==1:
        return indent+f'.leaf ({action(rows[0][0])}, {action(rows[0][1])})'
    return (indent+'.branch\n'+indent+'  ('+tree(rows[::2],level+2).lstrip()+')\n'+
        indent+'  ('+tree(rows[1::2],level+2).lstrip()+')')

def fast_source(rows):
    literal=tree([(rows[q,0],rows[q,1]) for q in range(245)])
    return '''import BusyBeaver.ZFC.TableRouting245

/-!
Balanced transition lookup for the exact canonical routing245 table.
Adapted from the checked FastTablePrefix246 implementation, whose tree format
comes from the maintained BootPerm252 transition-tree implementation;
the 490 actions are generated anew from canonical SHA-256
17f4d430747c4a0cd580dc2cc13ea06a74ce7f51f12be4c2d12f6a646691dd13.
All-state equality with machineRouting245 is checked by trusted kernel reduction.
Table attribution and the machine conventions are recorded in TableRouting245.
-/

namespace SetTheory.BusyBeaver.ZFC.FastTableRouting245

inductive TransitionTree (states : Nat) where
  | leaf : (Action states × Action states) → TransitionTree states
  | branch : TransitionTree states → TransitionTree states → TransitionTree states

def TransitionTree.lookup {n : Nat} : TransitionTree n → Nat → (Action n × Action n)
  | .leaf row, _ => row
  | .branch even odd, q =>
    if q % 2 = 0 then even.lookup (q / 2) else odd.lookup (q / 2)

def fastTree : TransitionTree 245 :=
'''+literal+'''

def fastMachine : Machine 245 where
  transition q b :=
    let row := fastTree.lookup q.val
    if b then row.2 else row.1

theorem fast_transition_eq : ∀ (q : Fin 245) (b : Bool),
    fastMachine.transition q b = machineRouting245.transition q b := by decide +kernel

theorem fastMachine_eq : fastMachine = machineRouting245 := by
  have h : fastMachine.transition = machineRouting245.transition := by
    funext q b
    exact fast_transition_eq q b
  exact congrArg Machine.mk h

end SetTheory.BusyBeaver.ZFC.FastTableRouting245
'''

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source',type=Path,default=REPO/'Computability/BusyBeaver/Research/ZFC/candidate-routing245/zfc_routing245.tm')
    p.add_argument('--output',type=Path,default=REPO/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/FastTableRouting245.lean')
    p.add_argument('--check',action='store_true')
    a=p.parse_args();text=fast_source(parse(a.source))
    if a.check:
        if a.output.read_text()!=text:raise ValueError('changed generated file '+str(a.output))
    else:a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(text)
    print(a.output,hashlib.sha256(text.encode()).hexdigest())

if __name__=='__main__':main()

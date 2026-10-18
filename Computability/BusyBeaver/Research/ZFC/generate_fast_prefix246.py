#!/usr/bin/env python3
"""Generate the untrusted exact246 balanced transition tree.

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
PIN='89cda615b3ea9fcac07ad6b08e0351faa34841a56935b6f5846d3920f13bc0fc'

def parse(path):
    data=path.read_bytes()
    if hashlib.sha256(data).hexdigest()!=PIN:raise ValueError('changed canonical source')
    rows={}; start=None
    for line in data.decode('ascii').splitlines():
        if line.startswith('#! start '):start=int(line.split()[-1])
        if not line or line.startswith('#'):continue
        q,b,w,d,t=line.split(); q,b,w,t=map(int,(q,b,w,t))
        if (q,b) in rows or b not in (0,1) or w not in (0,1) or d not in ('L','R') or not 0<=t<=246:
            raise ValueError('malformed canonical row')
        rows[q,b]=(w,d,t)
    if start!=0 or set(rows)!={(q,b) for q in range(246) for b in (0,1)}:
        raise ValueError('wrong table census or start')
    return rows

def action(row):
    w,d,t=row
    nxt='none' if t==246 else f'some ⟨{t}, by decide⟩'
    return f'⟨{"true" if w else "false"}, .{"right" if d=="R" else "left"}, {nxt}⟩'

def tree(rows,level=1):
    indent='  '*level
    if len(rows)==1:
        return indent+f'.leaf ({action(rows[0][0])}, {action(rows[0][1])})'
    return (indent+'.branch\n'+indent+'  ('+tree(rows[::2],level+2).lstrip()+')\n'+
        indent+'  ('+tree(rows[1::2],level+2).lstrip()+')')

def fast_source(rows):
    literal=tree([(rows[q,0],rows[q,1]) for q in range(246)])
    return '''import BusyBeaver.ZFC.TablePrefix246

/-!
Balanced transition lookup for the exact canonical prefix246 table.
This isolates the fast table from all bootstrap calculations. The tree format
is adapted from the maintained BootPerm252 transition-tree implementation;
the 492 actions are generated anew from canonical SHA-256
89cda615b3ea9fcac07ad6b08e0351faa34841a56935b6f5846d3920f13bc0fc.
All-state equality with machinePrefix246 is checked by trusted kernel reduction.
Table attribution and the machine conventions are recorded in TablePrefix246.
-/

namespace SetTheory.BusyBeaver.ZFC.FastTablePrefix246

inductive TransitionTree (states : Nat) where
  | leaf : (Action states × Action states) → TransitionTree states
  | branch : TransitionTree states → TransitionTree states → TransitionTree states

def TransitionTree.lookup {n : Nat} : TransitionTree n → Nat → (Action n × Action n)
  | .leaf row, _ => row
  | .branch even odd, q =>
    if q % 2 = 0 then even.lookup (q / 2) else odd.lookup (q / 2)

def fastTree : TransitionTree 246 :=
'''+literal+'''

def fastMachine : Machine 246 where
  transition q b :=
    let row := fastTree.lookup q.val
    if b then row.2 else row.1

theorem fast_transition_eq : ∀ (q : Fin 246) (b : Bool),
    fastMachine.transition q b = machinePrefix246.transition q b := by decide +kernel

theorem fastMachine_eq : fastMachine = machinePrefix246 := by
  have h : fastMachine.transition = machinePrefix246.transition := by
    funext q b
    exact fast_transition_eq q b
  exact congrArg Machine.mk h

end SetTheory.BusyBeaver.ZFC.FastTablePrefix246
'''

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source',type=Path,default=HERE/'candidate-prefix246/zfc_prefix246.tm')
    p.add_argument('--output',type=Path,default=REPO/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/FastTablePrefix246.lean')
    p.add_argument('--check',action='store_true')
    a=p.parse_args();text=fast_source(parse(a.source))
    if a.check:
        if a.output.read_text()!=text:raise ValueError('changed generated file '+str(a.output))
    else:a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(text)
    print(a.output,hashlib.sha256(text.encode()).hexdigest())

if __name__=='__main__':main()

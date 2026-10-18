#!/usr/bin/env python3
"""Generate untrusted exact250 fast-table and first-checkpoint Lean data.

Only standard-library parsing and a bounded 1024-step Python calculation run.
All finite equalities and the transfer to Core still require Lean checking.
No report code, compiler, dependency build, or external process is invoked.
"""
from __future__ import annotations
import argparse
import hashlib
from pathlib import Path

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[3]
PIN='0626819c4842f224001e7685366d8061897a7bc9470c015129a1d1cf22efb36e'

def parse(path):
    data=path.read_bytes()
    if hashlib.sha256(data).hexdigest()!=PIN:raise ValueError('changed canonical source')
    rows={}; start=None
    for line in data.decode('ascii').splitlines():
        if line.startswith('#! start '):start=int(line.split()[-1])
        if not line or line.startswith('#'):continue
        q,b,w,d,t=line.split(); q,b,w,t=map(int,(q,b,w,t))
        if (q,b) in rows or b not in (0,1) or w not in (0,1) or d not in ('L','R') or not 0<=t<=250:
            raise ValueError('malformed canonical row')
        rows[q,b]=(w,d,t)
    if start!=0 or set(rows)!={(q,b) for q in range(250) for b in (0,1)}:
        raise ValueError('wrong table census or start')
    return rows

def action(row):
    w,d,t=row
    nxt='none' if t==250 else f'some ⟨{t}, by decide⟩'
    return f'⟨{"true" if w else "false"}, .{"right" if d=="R" else "left"}, {nxt}⟩'

def tree(rows,level=1):
    indent='  '*level
    if len(rows)==1:
        return indent+f'.leaf ({action(rows[0][0])}, {action(rows[0][1])})'
    return (indent+'.branch\n'+indent+'  ('+tree(rows[::2],level+2).lstrip()+')\n'+
        indent+'  ('+tree(rows[1::2],level+2).lstrip()+')')

def fast_source(rows):
    literal=tree([(rows[q,0],rows[q,1]) for q in range(250)])
    return '''import BusyBeaver.ZFC.TablePrefix250

/-!
Balanced transition lookup for the exact canonical prefix250 table.
This isolates the fast table from all bootstrap calculations. The tree format
is adapted from the maintained BootPerm252 transition-tree implementation;
the 500 actions are generated anew from canonical SHA-256
0626819c4842f224001e7685366d8061897a7bc9470c015129a1d1cf22efb36e.
All-state equality with machinePrefix250 is checked by trusted kernel reduction.
Table attribution and the machine conventions are recorded in TablePrefix250.
-/

namespace SetTheory.BusyBeaver.ZFC.FastTablePrefix250

inductive TransitionTree (states : Nat) where
  | leaf : (Action states × Action states) → TransitionTree states
  | branch : TransitionTree states → TransitionTree states → TransitionTree states

def TransitionTree.lookup {n : Nat} : TransitionTree n → Nat → (Action n × Action n)
  | .leaf row, _ => row
  | .branch even odd, q =>
    if q % 2 = 0 then even.lookup (q / 2) else odd.lookup (q / 2)

def fastTree : TransitionTree 250 :=
'''+literal+'''

def fastMachine : Machine 250 where
  transition q b :=
    let row := fastTree.lookup q.val
    if b then row.2 else row.1

theorem fast_transition_eq : ∀ (q : Fin 250) (b : Bool),
    fastMachine.transition q b = machinePrefix250.transition q b := by decide +kernel

theorem fastMachine_eq : fastMachine = machinePrefix250 := by
  have h : fastMachine.transition = machinePrefix250.transition := by
    funext q b
    exact fast_transition_eq q b
  exact congrArg Machine.mk h

end SetTheory.BusyBeaver.ZFC.FastTablePrefix250
'''

def checkpoint(rows):
    q=head=0;left=[];right=[];ones=set()
    for elapsed in range(1,1025):
        b=right[0] if right else 0
        if b!=int(head in ones):raise ValueError('zipper/sparse read disagreement')
        w,d,q=rows[q,b]
        if q==250:raise ValueError('unexpected early halt')
        if w:ones.add(head)
        else:ones.discard(head)
        right=[w]+right[1:]
        if d=='R':left,right,head=[w]+left,right[1:],head+1
        else:right,left,head=[left[0] if left else 0]+right,left[1:],head-1
        represented={head-i-1 for i,b in enumerate(left) if b}|{head+i for i,b in enumerate(right) if b}
        if represented!=ones:raise ValueError('zipper/sparse whole-tape disagreement')
    return q,head,left,right,sorted(ones)

def bits(xs):return '['+', '.join('true' if x else 'false' for x in xs)+']'

def boot_source(rows):
    q,h,left,right,ones=checkpoint(rows)
    return f'''import BusyBeaver.ZFC.FastTablePrefix250
import BusyBeaver.ZFC.FiniteZipper

/-!
First bounded blank-tape checkpoint for the exact prefix250 machine.
The expected state/tape data are untrusted generated input. Trusted kernel
reduction verifies the 1024-step balanced block; generic zipper soundness
transfers it to every tape cell of Core's actual blank run. This is neither
the final 585431-step bootstrap nor a nonhalting/consistency theorem.
-/

namespace SetTheory.BusyBeaver.ZFC.BootPrefix250First

open FiniteZipper FastTablePrefix250

def checkpoint0 : ZipConfig 250 :=
  {{ state := some ⟨0, by decide⟩, head := 0, left := [], right := [] }}

theorem checkpoint0_rep : ZipRep (initial 250) checkpoint0 := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> intro i <;> rfl

/-- Generic checkpoint composition; each later chunk can be checked separately. -/
theorem advance_checkpoint (elapsed depth : Nat) {{z z' : ZipConfig 250}}
    (before : ZipRep (machinePrefix250.run elapsed) z)
    (calculated : zipBlock fastMachine depth z = z') :
    ZipRep (machinePrefix250.run (elapsed + 2 ^ depth)) z' := by
  rw [Machine.run_add_eq_runFrom]
  have h := zipBlock_sound fastMachine depth before
  rw [calculated, fastMachine_eq] at h
  exact h

def checkpoint1024 : ZipConfig 250 :=
  {{ state := some ⟨{q}, by decide⟩, head := {h},
    left := {bits(left)},
    right := {bits(right)} }}

theorem first_block : zipBlock fastMachine 10 checkpoint0 = checkpoint1024 := by
  decide +kernel

theorem first1024 : ZipRep (machinePrefix250.run 1024) checkpoint1024 :=
  advance_checkpoint 0 10 checkpoint0_rep first_block

theorem first1024_state : (machinePrefix250.run 1024).state = some ⟨{q}, by decide⟩ :=
  first1024.1

theorem first1024_head : (machinePrefix250.run 1024).head = {h} := first1024.2.1

theorem first1024_tape (pos : Int) :
    Tape.read (machinePrefix250.run 1024).tape pos = frameRead checkpoint1024 pos :=
  read_eq_frameRead first1024 pos

end SetTheory.BusyBeaver.ZFC.BootPrefix250First
'''

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source',type=Path,default=HERE/'candidate-prefix250/zfc_prefix250.tm')
    p.add_argument('--fast-output',type=Path,default=REPO/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/FastTablePrefix250.lean')
    p.add_argument('--boot-output',type=Path,help='Optional explicit path for untrusted first-checkpoint source.')
    p.add_argument('--check',action='store_true')
    a=p.parse_args();rows=parse(a.source)
    outputs=[(a.fast_output,fast_source(rows))]
    if a.boot_output is not None:outputs.append((a.boot_output,boot_source(rows)))
    for path,text in outputs:
        if a.check:
            if path.read_text()!=text:raise ValueError('changed generated file '+str(path))
        else:path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)
        print(path,hashlib.sha256(text.encode()).hexdigest())
    if a.boot_output is not None:
        q,h,l,r,ones=checkpoint(rows)
        print('untrusted 1024 checkpoint:',{'state':q,'head':h,'left_length':len(l),'right_length':len(r),'one_cells':ones})

if __name__=='__main__':main()

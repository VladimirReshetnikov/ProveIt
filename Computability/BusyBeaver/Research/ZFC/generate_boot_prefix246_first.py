#!/usr/bin/env python3
"""Generate untrusted first1024 exact246 checkpoint source, using only stdlib."""
from pathlib import Path
import argparse,hashlib,json
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

def checkpoint(rows):
    q=head=0;left=[];right=[];ones=set()
    for elapsed in range(1,1025):
        b=right[0] if right else 0
        if b!=int(head in ones):raise ValueError('zipper/sparse read disagreement')
        w,d,q=rows[q,b]
        if q==246:raise ValueError('unexpected early halt')
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
    return f'''import BusyBeaver.ZFC.FastTablePrefix246
import BusyBeaver.ZFC.FiniteZipper

/-!
First bounded blank-tape checkpoint for the exact prefix246 machine.
The expected state/tape data are untrusted generated input. Trusted kernel
reduction verifies the 1024-step balanced block; generic zipper soundness
transfers it to every tape cell of Core's actual blank run. This is neither
the final 410735-step bootstrap nor a nonhalting/consistency theorem.
-/

namespace SetTheory.BusyBeaver.ZFC.BootPrefix246First

open FiniteZipper FastTablePrefix246

def checkpoint0 : ZipConfig 246 :=
  {{ state := some ⟨0, by decide⟩, head := 0, left := [], right := [] }}

theorem checkpoint0_rep : ZipRep (initial 246) checkpoint0 := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> intro i <;> rfl

/-- Generic checkpoint composition; each later chunk can be checked separately. -/
theorem advance_checkpoint (elapsed depth : Nat) {{z z' : ZipConfig 246}}
    (before : ZipRep (machinePrefix246.run elapsed) z)
    (calculated : zipBlock fastMachine depth z = z') :
    ZipRep (machinePrefix246.run (elapsed + 2 ^ depth)) z' := by
  rw [Machine.run_add_eq_runFrom]
  have h := zipBlock_sound fastMachine depth before
  rw [calculated, fastMachine_eq] at h
  exact h

def checkpoint1024 : ZipConfig 246 :=
  {{ state := some ⟨{q}, by decide⟩, head := {h},
    left := {bits(left)},
    right := {bits(right)} }}

theorem first_block : zipBlock fastMachine 10 checkpoint0 = checkpoint1024 := by
  decide +kernel

theorem first1024 : ZipRep (machinePrefix246.run 1024) checkpoint1024 :=
  advance_checkpoint 0 10 checkpoint0_rep first_block

theorem first1024_state : (machinePrefix246.run 1024).state = some ⟨{q}, by decide⟩ :=
  first1024.1

theorem first1024_head : (machinePrefix246.run 1024).head = {h} := first1024.2.1

theorem first1024_tape (pos : Int) :
    Tape.read (machinePrefix246.run 1024).tape pos = frameRead checkpoint1024 pos :=
  read_eq_frameRead first1024 pos

end SetTheory.BusyBeaver.ZFC.BootPrefix246First
'''

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source',type=Path,default=HERE/'candidate-prefix246/zfc_prefix246.tm')
    p.add_argument('--output',type=Path,default=REPO/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/BootPrefix246First.lean')
    p.add_argument('--check',action='store_true');a=p.parse_args();rows=parse(a.source);text=boot_source(rows)
    if a.check:
        if a.output.read_text()!=text:raise ValueError('Generated source differs.')
    else:a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(text)
    q,h,l,r,ones=checkpoint(rows)
    data=dict(status='UNTRUSTED_GENERATED_DATA',canonical_sha256=PIN,steps=1024,state=q,head=h,left=l,right=r,ones=ones,source_sha256=hashlib.sha256(text.encode()).hexdigest())
    if not a.check:(HERE/'bootstrap-prefix246/first/data.json').write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps({k:v for k,v in data.items() if k not in ['left','right','ones']}))

if __name__=='__main__':main()

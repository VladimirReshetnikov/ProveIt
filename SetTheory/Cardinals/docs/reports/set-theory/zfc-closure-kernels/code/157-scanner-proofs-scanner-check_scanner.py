#!/usr/bin/env python3
"""Exact local whole-tape simulation proof for the 196/77 scanner relay.

Unspecified cells are arbitrary: every read below is from a constrained cell.
The two runs finish with identical state, head, and all constrained cells;
no unconstrained cell is written.  Thus the result quantifies over every
completion to a bi-infinite binary tape, not merely finite test samples.
"""
from pathlib import Path
import argparse,json,hashlib

def table(p):
    out={}
    for line in p.read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
        assert b in (0,1) and w in(0,1) and d in('L','R')
        assert(q,b)not in out
        out[q,b]=(w,1 if d=='R'else-1,z)
    return out

def run(T,initial,steps):
    tape=dict(initial);q,h=34,0;trace=[]
    for _ in range(steps):
        assert h in tape, 'Proof may not read an unspecified arbitrary cell'
        b=tape[h];w,d,z=T[q,b]
        trace.append([q,h,b,w,d,z]);tape[h]=w;h+=d;q=z
    return(q,h,tape),trace

def main():
    ap=argparse.ArgumentParser();ap.add_argument('baseline',type=Path,nargs='?',
        default=Path(__file__).resolve().parents[2]/'inputs/primary218.native.tm')
    ap.add_argument('--output',type=Path);args=ap.parse_args()
    B=table(args.baseline)
    expected={(34,1):(1,-1,2),(34,0):(0,-1,50),(50,0):(0,-1,75),(50,1):(1,-1,2),
              (196,0):(0,1,77),(196,1):(1,1,122),(122,1):(0,-1,1),
              (1,1):(1,-1,2),(75,0):(0,1,75)}
    assert all(B[k]==v for k,v in expected.items())
    assert {k for k,v in B.items()if v[2]==50}=={(34,0)}
    C={k:v for k,v in B.items()if k[0]!=50}
    C[34,0]=(1,-1,196);C[77,1]=(0,-1,75)
    assert len(C)==len(B)-2 and all(v[2]!=50 for v in C.values())
    cases=[]
    for name,initial,oldsteps,newsteps in[
        ('scanned_cell_is_one',{0:1},1,1),
        ('eighth_cell_is_one',{-1:1,0:0},2,4),
        ('eighth_and_ninth_cells_are_zero',{-2:0,-1:0,0:0},3,3)]:
        old,ot=run(B,initial,oldsteps);new,nt=run(C,initial,newsteps)
        assert old==new and old[2]==initial
        cases.append(dict(name=name,constrained_cells=initial,
                          old_steps=oldsteps,new_steps=newsteps,
                          old_trace=ot,new_trace=nt,endpoint=old))
    result=dict(status='EXACT_LOCAL_WHOLE_TAPE_PROOF',
        baseline_sha256=hashlib.sha256(args.baseline.read_bytes()).hexdigest(),
        removed_state=50,patches=[[34,0,1,-1,196],[77,1,0,-1,75]],
        assumptions=['At a scanned-zero entry to state34, a zero immediate left neighbor implies a zero second left neighbor.',
          'Every ordinary non-scanner use of changed row77/1 is separately preserved or removed.'],
        proof_scope='Every bi-infinite binary completion of the constrained cells; translation invariant in the head coordinate.',
        cases=cases)
    text=json.dumps(result,indent=2)+'\n'
    if args.output:args.output.write_text(text)
    else:print(text,end='')
if __name__=='__main__':main()

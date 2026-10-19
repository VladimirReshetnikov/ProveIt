#!/usr/bin/env python3
"""Independently check four literal local simulation blocks with open tape.

Unspecified cells are formal independent bits. A path may read a cell only
when its value follows from an explicit guard or from an earlier write. Thus
these checks quantify the entire unspecified tape, rather than sampling it.
This script does not prove the reachable-only successor-cell guard at169.
"""
from pathlib import Path
import json,hashlib

HERE=Path(__file__).resolve().parent

def table(path):
    out={}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,z=line.split();key=(int(q),int(b))
        assert key not in out
        out[key]=(int(w),1 if d=='R'else -1,int(z))
    return out

T=table(HERE/'baseline240.tm');U=table(HERE/'helper91_target106_239.tm')
assert len(T)==480 and len(U)==478
phi=lambda q:80 if q==169 else q

class Symbolic:
    def __init__(self,q,guard):
        self.q=q;self.h=0;self.tape=dict(guard);self.trace=[]
    def at(self,i):return self.tape.get(i,('input',i))
    def step(self,t):
        b=self.at(self.h)
        assert b in (0,1),('read requires an unstated premise',self.q,self.h,b)
        w,d,z=t[self.q,b]
        self.trace.append([self.q,self.h,b,w,d,z])
        self.tape[self.h]=w;self.q=z;self.h+=d
    def same_tape(self,other):
        return all(self.at(i)==other.at(i) for i in self.tape.keys()|other.tape.keys())

specs=[
 (80,{-1:1,0:0},[80,106,92,107,125,25]),
 (169,{-1:0,0:0},[80,106,93,57]),
 (169,{-1:0,0:1,1:1},[80,91,167,151,173,56]),
 (91,{-3:0,-2:1,-1:1,0:1},[91,167,151,24,36,54,71,82,94,50])]
records=[]
for oldq,guard,path in specs:
    old=Symbolic(oldq,guard);old.step(T)
    new=Symbolic(phi(oldq),guard)
    actual=[new.q]
    for _ in path[1:]:new.step(U);actual.append(new.q)
    assert actual==path
    assert new.q==phi(old.q) and new.h==old.h and new.same_tape(old)
    records.append(dict(old_entry=oldq,guard={str(k):v for k,v in sorted(guard.items())},
                        old_steps=1,new_steps=len(path)-1,new_path=path,
                        old_trace=old.trace,new_trace=new.trace,
                        final_state=new.q,final_head=new.h,
                        arbitrary_other_tape_cells=True))

incoming={q:[]for q,b in T}
for k,(w,d,z)in T.items():
    if z in incoming:incoming[z].append([k[0],k[1],w,d,z])
assert incoming[80]==[[67,1,1,1,80]]
assert incoming[169]==[[147,0,0,1,169]]
assert incoming[91]==[[80,1,1,1,91]]
assert sorted(incoming[67])==[[52,0,0,1,67],[124,0,0,1,67]]
assert 95 not in (80,169,91,67)
# These assertions prove the backward-entry bit facts on every run from95,
# by one, two, or three preceding right moves. They hold for arbitrary tapes.

ordinary=0
for (q,b),(w,d,z) in T.items():
    if (q,b) in {(80,0),(169,0),(169,1),(91,1)}:continue
    assert U[phi(q),b]==(w,d,phi(z)),((q,b),U[phi(q),b],(w,d,phi(z)))
    ordinary+=1
assert ordinary==476
result=dict(status='PASS_LITERAL_OPEN_TAPE_BLOCKS_AND_INCOMING_FACTS',
            baseline_sha256=hashlib.sha256((HERE/'baseline240.tm').read_bytes()).hexdigest(),
            candidate_sha256=hashlib.sha256((HERE/'helper91_target106_239.tm').read_bytes()).hexdigest(),
            state_map={'169':80},start=95,halt=254,ordinary_rows=ordinary,
            blocks=records,
            incoming_facts={str(q):incoming[q]for q in (67,80,91,169)},
            unresolved_by_this_script='At each actually reachable old configuration, state169 reading1 has right neighbor1. The teammate is proving this from all unbounded instruction cases plus exact blank startup.',
            proof='Given the stated reachable guard, the four positive literal blocks and476 matching rows give halting equivalence by stuttering simulation; no bound on the rest of the tape is imposed.')
(HERE/'local_blocks_239_independent.json').write_text(json.dumps(result,indent=2)+'\n')
print({k:v for k,v in result.items()if k not in ('blocks','incoming_facts')})

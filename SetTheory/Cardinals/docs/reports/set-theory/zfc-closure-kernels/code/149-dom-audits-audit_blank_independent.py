#!/usr/bin/env python3
"""Independent exact blank-tape replay and retained-trace comparison.

No repository modules, proof-search programs, or symbolic runtime are imported.
The finite set records every one on the otherwise entirely zero two-way tape.
"""
import argparse,hashlib,json
from pathlib import Path

def table(path):
    t={}
    for line in Path(path).read_text().splitlines():
        if not line.strip() or line.startswith('#'):continue
        q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
        assert (q,b) not in t and b in (0,1) and w in (0,1) and d in ('L','R')
        t[q,b]=(w,1 if d=='R' else -1,z)
    return t

def audit(candidate,reference,steps=312605):
    t=table(candidate);u=table(reference);states={q for q,b in t}
    assert len(states)==218
    assert set(t)=={(q,b)for q in states for b in (0,1)}
    assert {z for w,d,z in t.values()}-states=={254}
    reach={0};todo=[0]
    for q in todo:
        for b in (0,1):
            z=t[q,b][2]
            if z!=254 and z not in reach:reach.add(z);todo.append(z)
    assert reach==states
    q=head=0;ones=set();used=set();trace=hashlib.sha256()
    for tick in range(steps):
        bit=int(head in ones);key=q,bit
        assert t[key]==u[key], ('changed blank-start row',tick,key)
        w,d,z=t[key];used.add(key)
        trace.update(f'{q} {head} {bit} {w} {d} {z}\n'.encode())
        if w:ones.add(head)
        else:ones.discard(head)
        q=z;head+=d
    assert q==84 and min(ones)==head-1
    assert not any(head<=p<head+64 for p in ones)
    header=min(p for p in ones if p>head-1)
    assert header>=head+64
    p=header+1;values=[]
    while p<=max(ones):
        assert p not in ones and p+1 in ones
        p+=1;n=0
        while p in ones:n+=1;p+=1
        values.append(n-1)
    assert p==max(ones)+1 and len(values)>=10
    physical_order=(6,2,0,4,3,7,8,5,1)
    registers=[values[j]for j in physical_order]
    assert registers==[3,0,0,0,3,0,0,0,0]
    return dict(verified=True,working_states=len(states),transition_rows=len(t),
                all_states_graph_reachable=True,blank_symbol=0,initial_state=0,
                halt_state=254,dispatcher_state=q,steps=steps,head=head,
                additional_gap=header-head-64,logical_registers=registers,
                physical_registers=values[:9],spare_values=values[9:],
                complete_one_cells=sorted(ones),zero_exterior=True,
                retained_startup_rows=len(used),trace_sha256=trace.hexdigest(),
                candidate_sha256=hashlib.sha256(Path(candidate).read_bytes()).hexdigest(),
                reference_sha256=hashlib.sha256(Path(reference).read_bytes()).hexdigest(),
                scope='Exact complete blank configuration; every executed row equals the reference table; standard-library independent replay.')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('candidate');p.add_argument('reference');a=p.parse_args()
    print(json.dumps(audit(a.candidate,a.reference),indent=2))

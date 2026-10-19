#!/usr/bin/env python3
"""Canonicalize a complete old-label binary table and certify its bijection."""
from pathlib import Path
import argparse,hashlib,json

def read(path):
    T={}
    for line in path.read_text().splitlines():
        if not line.strip() or line.startswith('#'):continue
        q,b,w,d,t=line.split();q,b,w,t=map(int,(q,b,w,t))
        assert b in (0,1) and w in (0,1) and d in ('L','R') and (q,b) not in T
        T[q,b]=w,d,t
    Q={q for q,b in T}
    assert len(T)==2*len(Q) and all((q,b) in T for q in Q for b in (0,1))
    return T,Q

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('table',type=Path);ap.add_argument('--start',type=int,default=95)
    ap.add_argument('--halt',type=int,default=254);ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--certificate',type=Path,required=True)
    a=ap.parse_args();T,Q=read(a.table)
    assert a.start in Q and a.halt not in Q
    assert {t for _,_,t in T.values()}-Q=={a.halt}
    order=[a.start]+sorted(Q-{a.start});mapping={q:i for i,q in enumerate(order)}
    mapping[a.halt]=len(Q)
    new={(mapping[q],b):(w,d,mapping[t]) for (q,b),(w,d,t) in T.items()}
    body=[f'# {len(Q)} working states; binary alphabet; blank start 0; halt {len(Q)}.',
          '# Columns: state read write direction next_state. Halt is not a working state.']
    body += [f'{q} {b} {w} {d} {t}' for (q,b),(w,d,t) in sorted(new.items())]
    a.output.write_text('\n'.join(body)+'\n')
    R,S=read(a.output);assert R==new and S==set(range(len(Q)))
    assert len(set(mapping.values()))==len(mapping)
    # Check both symbols at every old state independently through inverse labels.
    inverse={v:k for k,v in mapping.items()}
    for (q,b),(w,d,t) in R.items():assert T[inverse[q],b]==(w,d,inverse[t])
    reachable={a.start};work=[a.start]
    while work:
        q=work.pop()
        for b in (0,1):
            t=T[q,b][2]
            if t in Q and t not in reachable:reachable.add(t);work.append(t)
    cert=dict(status='PASS',working_states=len(Q),defined_rows=len(T),old_start=a.start,
        old_halt=a.halt,new_start=0,new_halt=len(Q),old_to_new=mapping,
        original_sha256=hashlib.sha256(a.table.read_bytes()).hexdigest(),
        canonical_sha256=hashlib.sha256(a.output.read_bytes()).hexdigest(),
        graph_reachable_working_states=len(reachable),halting_edges=sum(t==a.halt for _,_,t in T.values()),
        scope='Exact state-label bijection and complete table check; reachability ignores tape symbols.')
    a.certificate.write_text(json.dumps(cert,indent=2)+'\n')
    print(json.dumps({k:v for k,v in cert.items() if k!='old_to_new'}))

if __name__=='__main__':main()

#!/usr/bin/env python3
"""Sound finite-window overapproximation from arbitrary tape at state 95."""
from pathlib import Path
from collections import deque
import argparse, json, hashlib

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--table',type=Path,default=Path(__file__).resolve().parents[1]/'reference/baseline241_old.tm')
    ap.add_argument('--radius',type=int,default=3)
    ap.add_argument('--output-dir',type=Path,default=Path('.'))
    a=ap.parse_args();assert 1<=a.radius<=8
    table={}
    for line in a.table.read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,z=line.split();table[int(q),int(b)]=(int(w),1 if d=='R'else-1,int(z))
    r=a.radius;width=2*r+1;mask=(1<<width)-1
    domains={q:set()for q,b in table};domains[254]=set()
    assert 95 in domains
    domains[95].update(range(mask+1));todo=deque((95,x)for x in range(mask+1))
    while todo:
        q,x=todo.popleft()
        if q==254:continue
        w,d,z=table[q,(x>>r)&1];y=(x&~(1<<r))|(w<<r)
        v=y>>1 if d==1 else(y<<1)&mask
        edge=1<<(width-1) if d==1 else 1
        for nxt in(v,v|edge):
            if nxt not in domains[z]:domains[z].add(nxt);todo.append((z,nxt))
    a.output_dir.mkdir(parents=True,exist_ok=True)
    (a.output_dir/'domains.txt').write_text(''.join(f'{q} {x}\n'for q in sorted(domains)for x in sorted(domains[q])))
    result={'radius':r,'table_sha256':hashlib.sha256(a.table.read_bytes()).hexdigest(),
            'start_tape':'arbitrary','start':95,'halt':254,
            'domains':{str(q):sorted(s)for q,s in sorted(domains.items())},
            'proof':'Least fixed point of literal transitions with both choices for each newly exposed exterior bit; every concrete run projects into these domains.'}
    (a.output_dir/'invariant.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'radius':r,'abstract_states':sum(map(len,domains.values()))}))
if __name__=='__main__':main()

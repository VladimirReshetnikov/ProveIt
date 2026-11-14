#!/usr/bin/env python3
"""Independent source-reachable frame comparison for shortened scanner.
This does not assert reachability of that frame in the modified blank run.
"""
from pathlib import Path
import json,hashlib
ROOT=Path(__file__).resolve().parents[1]
D=ROOT/'reduction_agent/incoming/new196/pa_consistency_research/engine/scanner195'
sites=json.loads((D/'reference196.sites.json').read_text())
regs=[2]+[0]*8;pc=25;gap=48;history=[]
while pc!=0:
    inst=sites[pc]['instruction'];history.append([pc,regs[:],gap]);op=inst[0]
    if op=='inc':regs[inst[1]]+=1;pc=inst[2]
    elif op=='dec':
        if regs[inst[1]]==0:pc=inst[2]
        else:regs[inst[1]]-=1;pc=inst[3];gap+=1
    elif op=='jump':pc=inst[1]
    else:raise ValueError('unexpected halt')
assert len(history)==43 and regs==[3,0,0,0,0,0,1,0,1]
PHYSICAL=[6,2,0,4,3,7,8,5,1]
def frame(site,rs,g):
    physical=[0]*9
    for r,v in enumerate(rs):physical[PHYSICAL[r]]=v
    physical += [1]*26
    tape={-1,g};tape.update(i for i,b in enumerate(sites[site]['path']) if b=='1');pos=g+1
    for v in physical:tape.update(range(pos+1,pos+v+2));pos+=v+2
    return tape

def run(table):
    rows={}
    for line in table.read_text().splitlines():
        q,b,w,d,t=line.split();rows[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(t))
    tape=frame(0,regs,gap);q=84;h=0
    target=sites[0]['instruction'][2];expected=frame(target,regs,gap)
    returns=[]
    for steps in range(1,100001):
        w,d,q=rows[q,int(h in tape)];(tape.add if w else tape.discard)(h);h+=d
        if q==84:
            returns.append({'steps':steps,'head':h,'matches':h==0 and tape==expected,'difference':len(tape^expected)})
            if h==0 and tape==expected:break
            if len(returns)>=10:break
        if q==254:break
    return {'returns':returns,'steps':steps,'q':q,'head':h,'expected_site':target,'difference':len(tape^expected),'matches':q==84 and h==0 and tape==expected,'ones':sorted(tape),'expected_ones':sorted(expected)}
report={'scope':'Finite-prefix comparison on a source-reachable register valuation and admissible frame; the parent needs multiple dispatcher returns. No global failure or later non-rejoining claim.',
        'source_sha256':hashlib.sha256((D/'reference196.sites.json').read_bytes()).hexdigest(),
        'source_steps':len(history),'registers':regs,'gap':gap,'site':pc,'source_history':history,
        'parent':run(D/'reference196.native.tm'),'candidate':run(D/'candidate.native.tm')}
assert report['parent']['matches'] and report['parent']['steps']==574
assert not report['candidate']['matches'] and report['candidate']['steps']==1398
(ROOT/'proof_agent/scanner_source_witness.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='source_history'},indent=2))

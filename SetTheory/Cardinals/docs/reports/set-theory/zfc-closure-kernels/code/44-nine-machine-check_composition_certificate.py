#!/usr/bin/env python3
"""Independent checker for composed253.tm; no generator module is imported."""
import argparse, hashlib, json
from pathlib import Path


def need(p,message):
    if not p: raise ValueError(message)


def load(path):
    raw=Path(path).read_bytes(); rows={}; start=None
    for line in raw.decode().splitlines():
        if line.startswith('#! start '):
            need(start is None,'duplicate start'); start=int(line.split()[-1])
        elif line.strip() and not line.startswith('#'):
            fields=line.split(); need(len(fields)==5,'malformed row')
            q,b,w,d,t=fields; q,b,w,t=map(int,(q,b,w,t))
            need((q,b) not in rows and b in (0,1) and w in (0,1) and d in ('L','R'),'invalid row')
            rows[q,b]=(w,d,t)
    need(start==0,'wrong start')
    need(set(rows)=={(q,b) for q in range(253) for b in (0,1)},'wrong row domain')
    need(all(t in range(254) for w,d,t in rows.values()),'invalid target')
    need(any(t==253 for w,d,t in rows.values()),'missing terminal')
    return rows,hashlib.sha256(raw).hexdigest()


def endpoint():
    values=[0,2,0,0,0,0,5,0,0]+[0,0,1,0,0,0,0,0,1]+[0]*149
    need(len(values)==167,'bad explicit frame')
    ones={-18,23}; p=24
    for v in values:
        p+=1
        for j in range(v+1): ones.add(p+j)
        p+=v+1
    need(len(ones)==178,'bad frame count')
    return (33,-17,ones)


def simulate(rows,n):
    q=0; h=0; ones=set(); shortcuts=0
    for _ in range(n):
        need(q!=253,'unexpected halt in bootstrap')
        b=1 if h in ones else 0; shortcuts+=(q,b)==(60,0)
        w,d,q=rows[q,b]
        if w==1: ones.add(h)
        elif h in ones: ones.remove(h)
        h+=1 if d=='R' else -1
    return (q,h,ones),shortcuts


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('public',type=Path); ap.add_argument('faster',type=Path)
    ap.add_argument('--dir',type=Path,required=True); args=ap.parse_args()
    public,ph=load(args.public); faster,fh=load(args.faster)
    candidate,ch=load(args.dir/'composed253.tm')
    need(ph=='84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95','wrong public input')
    need(fh=='d5b7a357dbf4dd9d18c8e1aa04dc0c3c0e1b8f349853b7558d1a096a15684412','wrong faster input')
    need(ch=='a5e0c60484e6873dc1a32121652606e2f3b2a2ce6046ef26847fd7a62bcfe212','wrong composed table')
    need({k for k in candidate if candidate[k]!=faster[k]}=={(60,0)},'wrong composed delta')
    need(faster[60,0]==(0,'L',45) and faster[45,0]==(0,'R',43) and faster[43,0]==(0,'R',51),'wrong source macro')
    need(candidate[60,0]==(0,'R',51),'wrong target macro')
    data=json.loads((args.dir/'composed_guard_invariant.json').read_text())
    need(data['source_sha256']==fh and data['radius']==2,'wrong invariant source')
    masks={int(q):int(v) for q,v in data['masks'].items()}
    need(set(masks)==set(range(254)),'wrong invariant domain')
    need(all(0<=m<(1<<32) for m in masks.values()),'bad mask range')
    need(masks[0]&1,'blank initial window excluded')
    pairs=0; obligations=0
    for q,m in masks.items():
        for p in range(32):
            if not ((m>>p)&1): continue
            pairs+=1
            if q==60 and not (p&4): need(not(p&2),'shortcut guard fails')
            if q==253: continue
            w,d,t=faster[q,(p>>2)&1]
            u=(p&27)|(w<<2)
            nxt=((u//2),(u//2)+16) if d=='R' else ((u*2)%32,(u*2)%32+1)
            for v in nxt: need((masks[t]>>v)&1,'invariant not closed'); obligations+=1
    need(pairs==3530 and obligations==7044,'invariant census differs')
    target=endpoint()
    for name,table,n in [('public',public,312975),('faster',faster,312935),('composed',candidate,312855)]:
        actual,uses=simulate(table,n)
        need(actual==target,'whole bootstrap frame mismatch: '+name)
        need(uses==40,'unexpected shortcut census')
    reachable={0}; todo=[0]
    while todo:
        q=todo.pop()
        if q==253: continue
        for b in (0,1):
            t=candidate[q,b][2]
            if t not in reachable: reachable.add(t); todo.append(t)
    need(reachable==set(range(254)),'state reachability differs')
    result={'status':'PASS','invariant_pairs':pairs,'closure_obligations':obligations,
       'bootstrap_steps':[312975,312935,312855],'all_integer_tape_cells_equal':True,
       'candidate_sha256':ch,'working_states':253,'graph_reachable_working_states':253,
       'scope':'Independent finite certificate check for the new table-to-table shortcut composition. No proof-assistant runtime or new state-count record.'}
    (args.dir/'independent_composition_check.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__': main()

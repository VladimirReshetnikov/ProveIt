#!/usr/bin/env python3
"""Explore exact lower-bound implications on the certified mixed source."""
from collections import defaultdict, Counter, deque
from pathlib import Path
import argparse, json, time
from sign_inference_original import square_root

def normalize(terms):
    out=defaultdict(int)
    for c,m in terms:out[tuple(sorted(m))]+=c
    return {m:c for m,c in out.items() if c}

def translate(poly,lb):
    out=defaultdict(int)
    for mon,c in poly.items():
        if not mon:out[()]+=c
        elif len(mon)==1:
            x=mon[0];out[(x,)]+=c;out[()]+=c*max(lb[x],0)
        else:
            x,y=mon;a=max(lb[x],0);b=max(lb[y],0)
            out[(x,y)]+=c;out[(x,)]+=c*b;out[(y,)]+=c*a;out[()]+=c*a*b
    return {m:c for m,c in out.items() if c}

def positive(poly,lb):
    p=translate(poly,lb)
    if all(c>=0 for c in p.values()) and all(
       all(e%2==0 or lb[v]>=0 for v,e in Counter(m).items()) for m in p):
        return 1 if p.get((),0)>0 else 0
    if square_root(poly) is not None:return 0
    return -1

def search(directory,output):
    d=Path(directory);source=json.loads((d/'source.json').read_text())
    old=json.loads((d/'domain_certificate.json').read_text())['positivity']
    variables=source['variables'];N=len(variables)
    required=set(old['required_nonnegative']);seed=set(old['guard_indices'])
    rules=[];by_dep=defaultdict(list)
    for rid,row in enumerate(source['residuals']):
        p=normalize(row['terms']);inds={v for m in p for v in m}
        for v in sorted(inds&required):
            if any(mon.count(v)>1 for mon in p):continue
            A=normalize([(c,[u for u in mon if u!=v]) for mon,c in p.items() if v in mon])
            B=normalize([(-c,list(mon)) for mon,c in p.items() if v not in mon])
            if all(c<0 for c in A.values()):A={m:-c for m,c in A.items()};B={m:-c for m,c in B.items()}
            if not A or any(c<0 for c in A.values()):continue
            BA=normalize([(c,m) for m,c in B.items()]+[(-c,m) for m,c in A.items()])
            deps={u for obj in (A,B) for mon in obj for u in mon}
            k=len(rules);rules.append((v,rid,A,B,BA))
            for u in deps:by_dep[u].append(k)
    def closure(seeds,record=False):
        lb=[-1]*N
        for v in seeds:lb[v]=0
        queue=deque(range(len(rules)));queued=set(queue);steps=[]
        while queue:
            k=queue.popleft();queued.remove(k);v,rid,A,B,BA=rules[k]
            if lb[v]>=2 or positive(A,lb)!=1:continue
            bound=positive(B,lb)
            if bound<0:continue
            if positive(BA,lb)==1:bound=2
            if bound<=lb[v]:continue
            lb[v]=bound
            if record:steps.append({'variable':v,'lower_bound':bound,'row':rid})
            for k2 in by_dep[v]:
                if k2 not in queued:queue.append(k2);queued.add(k2)
        return lb,steps
    lb,_=closure(seed)
    if not all(lb[v]>=0 for v in required):raise ValueError('initial closure incomplete')
    start=time.time();removed=[]
    for v in sorted(seed,reverse=True):
        lb,_=closure(seed-{v})
        if all(lb[u]>=0 for u in required):
            seed.remove(v);removed.append(v)
            print('removed',v,variables[v]['name'],'seeds',len(seed),flush=True)
    lb,steps=closure(seed,True)
    result={'seeds':sorted(seed),'required_nonnegative':sorted(required),
            'temporarily_signed':old['temporarily_signed'],'steps':steps,'bounds':lb,
            'removed_from_previous_seeds':removed}
    Path(output).write_text(json.dumps(result,indent=2)+'\n')
    print('result',len(seed),'guards',len(steps),'steps',time.time()-start,flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('directory');p.add_argument('output');a=p.parse_args();search(a.directory,a.output)

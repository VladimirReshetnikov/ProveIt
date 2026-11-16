#!/usr/bin/env python3
"""Exploratory source allocator. A result requires fresh runtime verification."""
from collections import defaultdict, Counter
from functools import lru_cache
from pathlib import Path
import argparse
import hashlib
import json
import sys
import time

ROOT=Path(__file__).resolve().parents[2]
BASE=Path(__file__).resolve().parent
sys.path.insert(0,str(BASE/'code'))
sys.path.insert(0,str(ROOT/'analysis/smt_deps'))
import source_language as s
import build221 as b
import z3

def paths(node,p=''):
    if s.leaf(node): return
    yield p,node
    yield from paths(node[0],p+'0')
    yield from paths(node[1],p+'1')

def edge(table,q,p,bit):
    tape={-1:1,**{i:int(v)for i,v in enumerate(p+str(bit))}}
    before=dict(tape);head=len(p);used=[]
    for _ in range(100):
        if head==len(p)+1:return (q if tape==before else None),used
        if head not in tape or (q,tape[head])not in table:return None,used
        k=q,tape[head];used.append(k);w,d,q=table[k];tape[head]=w;head+=d
    return None,used

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('source',type=Path)
    ap.add_argument('output',type=Path)
    ap.add_argument('--fresh',type=int,default=0)
    ap.add_argument('--seconds',type=int,default=60)
    ap.add_argument('--feasible-only',action='store_true',help='Use SAT feasibility, without allocation-cost optimization')
    ap.add_argument('--protected',type=Path,default=Path(__file__).with_name('protected.txt'))
    args=ap.parse_args();args.output.mkdir(parents=True,exist_ok=True)
    oldtable=b.read_table((BASE/'pa196.native.tm').read_bytes())
    old=s.tree(json.loads((BASE/'original.json').read_text()))
    new=s.tree(json.loads(args.source.read_text()))
    groups,_=b.decoder_map(oldtable,old);oldstates=defaultdict(set)
    for q,ns in groups.items():
        for n in ns:oldstates[n].add(q)
    occ=defaultdict(list)
    for p,n in paths(new):occ[n].append(p)
    @lru_cache(None)
    def compatible(n,p,q):
        if q not in oldstates.get(n,()):return False
        for bit,ch in enumerate(n):
            if s.leaf(ch):
                if q==108 and bit==1:
                    required={'CC':'101','CB':'001'}.get(ch[0])
                    if required and not ('1'+p+'1').endswith(required):return False
                continue
            z,_=edge(oldtable,q,p,bit)
            if z is None or not compatible(ch,p+str(bit),z):return False
        return True
    fixed={}
    for n,ps in occ.items():
        qs={q for q in oldstates.get(n,())if any(compatible(n,p,q)for p in ps)}
        if qs:fixed[n]=qs
    newnodes=[n for n in occ if n not in fixed]
    used=set().union(*fixed.values())if fixed else set()
    pool=sorted({q for q,bit in oldtable}-used)+list(range(2000,2000+args.fresh))
    protected={k for l in args.protected.read_text().splitlines() if l.strip() for k in [tuple(map(int,l.split()))] if k in oldtable}
    helper=set()
    for n,qs in fixed.items():
        for p in occ[n]:
            for q in qs:
                if not compatible(n,p,q):continue
                for bit,ch in enumerate(n):
                    if not s.leaf(ch):
                        z,trace=edge(oldtable,q,p,bit)
                        if z is None:raise ValueError('Incompatible fixed node')
                        helper.update(trace[1:])
    protected|=helper
    leafacts=defaultdict(Counter)
    for q,ns in groups.items():
        for n in ns:
            for bit,ch in enumerate(n):
                if s.leaf(ch):leafacts[ch,bit][oldtable[q,bit]]+=1
    defaults={}
    for key,acts in leafacts.items():
        direct=[a for a in acts if a[:2]==(key[1],1)]
        defaults[key]=max(direct or acts,key=lambda a:acts[a])
    for op,arg,q in [('CC',1,1),('CC',2,16),('CB',1,302)]:
        key=((op,arg),1)
        if key in leafacts:defaults[key]=(0,-1,q);leafacts[key][defaults[key]]+=1
    domains={n:set(pool)for n in newnodes};reqs={}
    if new in domains:domains[new]&={84}
    elif fixed[new]!={84}:raise ValueError('Root mismatch')
    for n in newnodes:
        for q in list(domains[n]):
            valid=True;req=[]
            for bit,ch in enumerate(n):
                if (q,bit)not in protected:continue
                act=oldtable[q,bit]
                if s.leaf(ch):valid &= act in leafacts.get((ch,bit),())
                elif act[:2]!=(bit,1):valid=False
                elif ch in fixed:valid &= act[2]in fixed[ch]
                else:req.append((ch,act[2]))
            if valid:reqs[n,q]=req
            else:domains[n].remove(q)
    changed=True
    while changed:
        changed=False
        for n in newnodes:
            for q in list(domains[n]):
                if any(t not in domains[ch]for ch,t in reqs[n,q]):domains[n].remove(q);changed=True
    receipt={'status':'PENDING','source':str(args.source),'source_sha256':hashlib.sha256(args.source.read_bytes()).hexdigest(),
             'metrics':s.metrics(new),'new_nodes':len(newnodes),'fixed_nodes':len(fixed),'pool':pool,
             'protected_rows':len(protected),'domain_sizes':[len(domains[n])for n in newnodes],
             'scope':'Allocation and prefix checks only; finite engine-protection filter is not a proof.'}
    def save():
        (args.output/'allocation.json').write_text(json.dumps(receipt,indent=2)+'\n')
        print(json.dumps({k:v for k,v in receipt.items()if k not in ('assignments','changed_rows','prefix_failures','domain_sizes')},indent=2),flush=True)
    if any(not d for d in domains.values()):receipt['status']='EMPTY_DOMAIN';save();return
    if len(newnodes)>len(pool):receipt['status']='INSUFFICIENT_POOL';save();return
    variables={(i,q):z3.Bool(f'n{i}_q{q}')for i,n in enumerate(newnodes)for q in sorted(domains[n])}
    index={n:i for i,n in enumerate(newnodes)}
    solver=z3.Solver() if args.feasible_only else z3.Optimize();solver.set(timeout=args.seconds*1000)
    for i,n in enumerate(newnodes):solver.add(z3.PbEq([(variables[i,q],1)for q in domains[n]],1))
    for q in pool:
        vs=[variables[i,q]for i,n in enumerate(newnodes)if q in domains[n]]
        if vs:solver.add(z3.PbLe([(v,1)for v in vs],1))
    required_targets={t for requirements in reqs.values() for ch,t in requirements}
    anonymous=[q for q in pool if q not in required_targets and not any((q,b) in protected for b in (0,1))]
    previous_anonymous={q:anonymous[j-1] for j,q in enumerate(anonymous) if j}
    for (i,q),v in variables.items():
        for ch,t in reqs[newnodes[i],q]:solver.add(z3.Implies(v,variables[index[ch],t]))
    costs=[z3.If(v,-100*sum((q,b)in protected for b in(0,1))+(1000 if q>=2000 else 0),0)for(i,q),v in variables.items()]
    if costs and not args.feasible_only:solver.minimize(z3.Sum(costs))
    start=time.monotonic();result=solver.check()
    receipt.update(solver=str(result),solver_seconds=time.monotonic()-start)
    if result!=z3.sat:receipt['status']='UNSAT' if result==z3.unsat else 'UNKNOWN';save();return
    model=solver.model();mapped={n:set(qs)for n,qs in fixed.items()}
    for (i,q),v in variables.items():
        if z3.is_true(model[v]):mapped[newnodes[i]]={q}
    candidate=dict(oldtable)
    for n in newnodes:
        q=next(iter(mapped[n]))
        for bit,ch in enumerate(n):
            if (q,bit)in protected:continue
            if s.leaf(ch):
                if(ch,bit)not in defaults:receipt.update(status='MISSING_LEAF_ACTION',missing=[ch,bit]);save();return
                candidate[q,bit]=defaults[ch,bit]
            else:candidate[q,bit]=(bit,1,min(mapped[ch]))
    if any(candidate[k]!=oldtable[k]for k in protected):raise ValueError('Protected row changed')
    reach={74};todo=[74]
    for q in todo:
        for bit in(0,1):
            z=candidate[q,bit][2]
            if z!=254 and z not in reach:reach.add(z);todo.append(z)
    candidate={k:v for k,v in candidate.items()if k[0]in reach}
    failures=[];actual={}
    for p,n in paths(new):
        tape={-1:1,**{i:int(v)for i,v in enumerate(p)}};before=dict(tape);head=0;q=84
        for _ in range(10000):
            if head==len(p):break
            if head not in tape or(q,tape[head])not in candidate:break
            w,d,q=candidate[q,tape[head]];tape[head]=w;head+=d
        if head!=len(p)or tape!=before or q not in mapped[n] or (n in fixed and not compatible(n,p,q)):
            failures.append({'path':p,'state':q,'allowed':sorted(mapped[n]),'head':head})
        actual[p]=q
    receipt.update(status='PREFIX_PASS'if not failures else'PREFIX_FAIL',states=len(candidate)//2,
        assignments=[{'path':occ[n][0],'state':min(mapped[n])}for n in newnodes],
        changed_rows=[[*k,*v]for k,v in candidate.items()if oldtable.get(k)!=v],
        removed=sorted({q for q,_ in oldtable}-reach),prefix_failures=failures)
    (args.output/'candidate.native.tm').write_bytes(b.table_bytes(candidate))
    (args.output/'prefix-map.json').write_text(json.dumps(actual,sort_keys=True)+'\n')
    save()

if __name__=='__main__':main()

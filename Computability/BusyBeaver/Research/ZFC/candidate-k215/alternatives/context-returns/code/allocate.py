#!/usr/bin/env python3
"""Finite row-protected source allocator; this is synthesis, never acceptance.

Adapted from the repository's composition-allocation/allocate-v2.py algorithm,
with a freshly computed engine-row filter, explicit base paths, deletion
budgets, and an option to unfix pure decoder roles for a broader allocation.
"""
from pathlib import Path
from collections import defaultdict,Counter
from functools import lru_cache
from types import SimpleNamespace
import argparse,json,hashlib,time,sys
import numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import lil_matrix
HERE=Path(__file__).resolve().parent
BASE=HERE.parent/'upstream'
sys.path.insert(0,str(HERE))
import source_language as s
import build221 as b

def paths(n,p=''):
    if s.leaf(n):return
    yield p,n
    yield from paths(n[0],p+'0');yield from paths(n[1],p+'1')
def edge(T,q,p,bit):
    tape={-1:1,**{i:int(v)for i,v in enumerate(p+str(bit))}};before=dict(tape);h=len(p);used=[]
    for _ in range(100):
        if h==len(p)+1:return(q if tape==before else None),used
        if h not in tape or(q,tape[h])not in T:return None,used
        k=q,tape[h];used.append(k);w,d,q=T[k];tape[h]=w;h+=d
    return None,used
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('source',type=Path);ap.add_argument('output',type=Path)
    ap.add_argument('--limit',type=int,default=60);ap.add_argument('--drop',type=int)
    ap.add_argument('--global-pure',action='store_true');ap.add_argument('--fresh',type=int,default=0)
    ap.add_argument('--table',type=Path,default=BASE/'k215.native.tm')
    ap.add_argument('--engine',type=Path,default=HERE.parent/'evidence/engine-baseline.json')
    a=ap.parse_args();a.output.mkdir(parents=True,exist_ok=False)
    T=b.read_table(a.table.read_bytes());old=s.tree(json.loads((BASE/'sites215.json').read_text()));new=s.tree(json.loads(a.source.read_text()))
    groups,oldpaths=b.decoder_map(T,old);oldstates=defaultdict(set)
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
                    if required is not None and not('1'+p+'1').endswith(required):return False
                continue
            z,_=edge(T,q,p,bit)
            if z is None or not compatible(ch,p+str(bit),z):return False
        return True
    fixed={}
    for n,ps in occ.items():
        options={q for q in oldstates.get(n,())if all(compatible(n,p,q)for p in ps) and q!=a.drop}
        if options and (not a.global_pure or any(T[q,bit][:2]!=(bit,1)for q in options for bit in(0,1))):fixed[n]=options
    newnodes=[n for n in occ if n not in fixed]
    used=set().union(*fixed.values())if fixed else set()
    pool=sorted(({q for q,bit in T}-used)-{a.drop})+list(range(500,500+a.fresh))
    engine=json.loads(a.engine.read_text())
    protected={tuple(k)for k in engine['rows']}
    # Exact full-context decoder providers for all retained roles.
    helper=set();forced=defaultdict(set)
    for n,qs in fixed.items():
        for p in occ[n]:
            for q in qs:
                for bit,ch in enumerate(n):
                    if s.leaf(ch):continue
                    z,trace=edge(T,q,p,bit);assert z is not None
                    helper.update(trace)
                    if ch not in fixed:forced[ch].add(z)
    protected|=helper
    leafacts=defaultdict(Counter)
    for q,ns in groups.items():
        for n in ns:
            for bit,ch in enumerate(n):
                if s.leaf(ch):leafacts[ch,bit][T[q,bit]]+=1
    for op,arg,q in [('CC',1,1),('CC',2,16),('CB',1,302)]:
        key=((op,arg),1)
        if key in leafacts:leafacts[key][(0,-1,q)]+=1
    defaults={}
    for key,acts in leafacts.items():
        direct=[act for act in acts if act[:2]==(key[1],1)]
        defaults[key]=max(direct or acts,key=lambda act:acts[act])
    domains={n:set(pool)for n in newnodes};reqs={}
    if new in domains:domains[new]&={84}
    else:assert fixed[new]=={84}
    for n,qs in forced.items():
        if len(qs)==1:domains[n]&=qs
        else:domains[n].clear()
    for n in newnodes:
        for q in list(domains[n]):
            valid=True;req=[]
            for bit,ch in enumerate(n):
                if(q,bit)not in protected:continue
                act=T[q,bit]
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
    rec={'status':'PENDING','scope':'Synthesis and finite prefix audit. Full runtime, source calibration and blank start are separate obligations.',
         'source':str(a.source),'metrics':s.metrics(new),'new_nodes':len(newnodes),'fixed_nodes':len(fixed),'fixed_states':len(used),'pool':pool,
         'protected_rows':len(protected),'forced_roles':len(forced),'domain_sizes':[len(domains[n])for n in newnodes],
         'drop':a.drop,'global_pure':a.global_pure}
    rec['table']=str(a.table);rec['engine_filter']=str(a.engine)
    def finish():
        (a.output/'allocation.json').write_text(json.dumps(rec,indent=2)+'\n')
        print(json.dumps({k:v for k,v in rec.items()if k not in('assignments','changed_rows','failures','pool','domain_sizes')},indent=2),flush=True)
    if a.drop is not None and any(q==a.drop or T[q,bit][2]==a.drop for q,bit in protected):
        rec['status']='DROP_USED_BY_ENGINE';finish();return
    if any(not d for d in domains.values()):rec['status']='EMPTY_DOMAIN';finish();return
    choices=[(n,q)for n in newnodes for q in sorted(domains[n])];idx={v:i for i,v in enumerate(choices)};rows=[];lo=[];hi=[]
    for n in newnodes:rows.append({idx[n,q]:1 for q in domains[n]});lo.append(1);hi.append(1)
    for q in pool:rows.append({idx[n,q]:1 for n in newnodes if q in domains[n]});lo.append(0);hi.append(1)
    for n,q in choices:
        for ch,t in reqs[n,q]:rows.append({idx[n,q]:1,idx[ch,t]:-1});lo.append(-np.inf);hi.append(0)
    A=lil_matrix((len(rows),len(choices)))
    for i,row in enumerate(rows):
        for j,v in row.items():A[i,j]=v
    costs=np.array([-100*sum((q,bit)in protected for bit in(0,1))+q/1000 for n,q in choices])
    started=time.monotonic()
    ans=milp(costs,integrality=np.ones(len(choices)),bounds=Bounds(0,1),constraints=LinearConstraint(A.tocsc(),lo,hi),options={'time_limit':a.limit})if choices else SimpleNamespace(x=[],message='NO_NEW_ROLES')
    rec.update(solver=ans.message,seconds=time.monotonic()-started,variables=len(choices),constraints=len(rows))
    if ans.x is None:rec['status']='NO_ALLOCATION';finish();return
    mapped={n:set(qs)for n,qs in fixed.items()}
    for(n,q),x in zip(choices,ans.x):
        if x>.5:mapped[n]={q}
    N=dict(T)
    for n in newnodes:
        q=next(iter(mapped[n]))
        for bit,ch in enumerate(n):
            if(q,bit)in protected:continue
            if s.leaf(ch):
                if(ch,bit)not in defaults:rec.update(status='MISSING_LEAF',missing=[ch,bit]);finish();return
                N[q,bit]=defaults[ch,bit]
            else:N[q,bit]=(bit,1,min(mapped[ch]))
    assert all(N[k]==T[k]for k in protected)
    reach={0};todo=[0]
    for q in todo:
        for bit in(0,1):
            z=N[q,bit][2]
            if z!=254 and z not in reach:reach.add(z);todo.append(z)
    N={k:v for k,v in N.items()if k[0]in reach}
    failures=[];actual={}
    for p,n in paths(new):
        tape={-1:1,**{i:int(v)for i,v in enumerate(p)}};before=dict(tape);head=0;q=84
        for _ in range(10000):
            if head==len(p):break
            if head not in tape or(q,tape[head])not in N:break
            w,d,q=N[q,tape[head]];tape[head]=w;head+=d
        local_old=q in oldstates.get(n,())and compatible(n,p,q)and all(N.get((q,bit))==T[q,bit]for bit,ch in enumerate(n)if s.leaf(ch))
        if head!=len(p)or tape!=before or not(q in mapped[n]or local_old):failures.append({'path':p,'state':q,'head':head,'allowed':sorted(mapped[n])})
        actual[p]=q
    rec.update(status='PREFIX_PASS'if not failures else'PREFIX_FAIL',states=len(N)//2,
               removed=sorted({q for q,b in T}-reach),assignments=[{'path':occ[n][0],'q':min(mapped[n])}for n in newnodes],
               changed_rows=[[*k,*N[k]]for k in N if T.get(k)!=N[k]],failures=failures)
    (a.output/'candidate.native.tm').write_bytes(b.table_bytes(N))
    (a.output/'sites.json').write_bytes(s.compact(s.sites(new)))
    (a.output/'prefix-map.json').write_text(json.dumps(actual,sort_keys=True)+'\n');finish()
if __name__=='__main__':main()

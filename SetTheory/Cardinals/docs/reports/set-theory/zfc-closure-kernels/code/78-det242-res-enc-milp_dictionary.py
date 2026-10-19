#!/usr/bin/env python3
"""Globally reparse a union of finite grammar dictionaries by binary MILP.

Word selection and binary parses are optimized simultaneously. All route and
bootstrap projections are exact. Bad zero runs or excessive source depth are
excluded by finite, replayable clauses on the selected ancestor productions.
The optimization is restricted to the supplied finite pool of word labels.
"""
from pathlib import Path
from functools import lru_cache
import argparse,json,time
import numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import coo_matrix
from exact_exchange import load_context,HERE

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--seconds',type=float,default=120);ap.add_argument('--zero-limit',type=int,default=6);ap.add_argument('--target',type=int,default=127);ap.add_argument('--relaxed',action='store_true');ap.add_argument('--height-model',action='store_true');ap.add_argument('--feasible-target',action='store_true');ap.add_argument('--output',type=Path,default=HERE/'milp_result.json');ap.add_argument('--input',type=Path,default=HERE/'baseline_fine_grammar.json');ap.add_argument('--pool',nargs='*',type=Path,default=[HERE/x for x in ['baseline_fine_grammar.json','search_control.json','search_baseline.json','search_reduced_locks.json','search_zero5.json']]);a=ap.parse_args()
    old,roots,allowed,groups,expr,root,atoms,locks=load_context()
    baseline=json.loads(a.input.read_text());routes={(r['source'],r['read']):r['word'] for r in baseline['routes']}
    if a.relaxed:
        lines=(HERE/'fine-grammar.txt').read_text().strip().splitlines();nr,nroot,na=map(int,lines[0].split());roots=lines[1+nr:1+nr+nroot]
        locks=[tuple(x.split()) for x in (HERE/'reduced-locks.txt').read_text().strip().splitlines()[1:]]
        roots=list(dict.fromkeys(roots+[q for q,p,t in locks]))
    checks=locks+[(routes[s,b],p,t) for s,b,w,cs in groups for p,t in cs]
    snapshots={str(p):json.loads(p.read_text()) for p in a.pool};pool={w for data in snapshots.values() for w,l,r in data['rules']}
    pool-=set(allowed);words=sorted(pool,key=lambda w:(len(w),w));known=pool|set(allowed)
    xindex={w:i for i,w in enumerate(words)};productions={};yindex={};varwords=[]
    permitted=lambda l,r:(l not in allowed or allowed[l]&1) and (r not in allowed or allowed[r]&2)
    for w in words:
        productions[w]=[(w[:k],w[k:]) for k in range(1,len(w)) if w[:k] in known and w[k:] in known and permitted(w[:k],w[k:])]
        for lr in productions[w]:yindex[w,lr]=len(words)+len(varwords);varwords.append((w,lr))
    binary_vars=len(words)+len(varwords);nv=binary_vars
    prop_words=sorted(pool|set(allowed)|set(old),key=lambda w:(len(w),w))
    pindex={};eindex={}
    if a.height_model:
        for w in prop_words:
            for kind in range(3):pindex[w,kind]=nv;nv+=1
        for i in range(len(expr)):
            for kind in range(3):eindex[i,kind]=nv;nv+=1
    cost=np.zeros(nv)
    if not a.feasible_target:cost[:len(words)]=1
    lb=np.zeros(nv);ub=np.ones(nv);ub[binary_vars:]=1024
    integrality=np.zeros(nv);integrality[:binary_vars]=1
    rows=[];lower=[];upper=[]
    def add(coeff,lo=-np.inf,hi=np.inf):rows.append(coeff);lower.append(lo);upper.append(hi)
    if a.feasible_target:add({i:1 for i in range(len(words))},hi=a.target)
    for w in words:
        add({xindex[w]:1,**{yindex[w,lr]:-1 for lr in productions[w]}},0,0)
        for lr in productions[w]:
            yi=yindex[w,lr]
            for child in lr:
                if child in pool:add({yi:1,xindex[child]:-1},hi=0)
    for w in set(roots)|set(routes.values()):lb[xindex[w]]=1
    for w,p,target in checks:
        assert 1<=len(p)<=2
        for lr in productions[w]:
            yi=yindex[w,lr];child=lr[int(p[0])]
            if len(p)==1:
                if child!=target:ub[yi]=0
            elif child not in pool:ub[yi]=0
            else:
                options=[yindex[child,sub] for sub in productions[child] if sub[int(p[1])]==target]
                if not options:ub[yi]=0
                else:add({yi:1,**{v:-1 for v in options}},hi=0)
    if a.height_model:
        def link(dest,source,step=0,indicator=None,value=1):
            row={dest:1};row[source]=row.get(source,0)-1;lo=step
            if indicator is not None:
                if value:row[indicator]=-1025;lo-=1025
                else:row[indicator]=1025
            add(row,lo=lo)
        def node(d,l,r,indicator=None,value=1):
            link(d[0],l[0],1,indicator,value)
            link(d[1],l[0],1,indicator,value)
            link(d[1],l[1],0,indicator,value)
            link(d[1],r[1],0,indicator,value)
            link(d[2],l[2],1,indicator,value)
            link(d[2],r[2],1,indicator,value)
        def pp(w):return [pindex[w,k] for k in range(3)]
        def ep(i):return [eindex[i,k] for k in range(3)]
        for w in prop_words:
            if w in allowed:
                for k in range(3):link(pindex[w,k],eindex[atoms[w],k])
            else:
                if w in pool:
                    for lr in productions[w]:node(pp(w),pp(lr[0]),pp(lr[1]),yindex[w,lr])
                if w in old:
                    lr=old[w];node(pp(w),pp(lr[0]),pp(lr[1]),xindex.get(w),0)
        for i,e in enumerate(expr):
            if e[0]=='L':
                for k in range(3):ub[eindex[i,k]]=0
            elif e[0]=='W':
                for k in range(3):link(eindex[i,k],pindex[e[1],k])
            else:node(ep(i),ep(e[1]),ep(e[2]))
        ub[eindex[root,1]]=a.zero_limit;ub[eindex[root,2]]=64
    def unpack(solution):
        out={}
        for w in words:
            chosen=[lr for lr in productions[w] if solution[yindex[w,lr]]>0.5]
            assert len(chosen)==int(solution[xindex[w]]>0.5)
            if chosen:out[w]=chosen[0]
        # A feasibility objective can leave unused, positively charged roles.
        # Prune those roles before reporting or checking the dictionary.
        live=set();todo=list(roots)+list(routes.values())
        while todo:
            w=todo.pop()
            if w in allowed or w in live:continue
            assert w in out;live.add(w);todo.extend(out[w])
        return {w:out[w] for w in live}
    def validate(g):
        for w,lr in g.items():assert w==''.join(lr) and permitted(*lr) and all(c in g or c in allowed for c in lr)
        for w,p,target in checks:
            for b in p:assert w in g;w=g[w][int(b)]
            assert w==target
        seen=set();todo=list(roots)+list(routes.values())
        while todo:
            w=todo.pop()
            if w in allowed or w in seen:continue
            assert w in g;seen.add(w);todo.extend(g[w])
        assert seen==set(g),'Unused roles remain after reachability pruning'
        bad=set();leaves=0;maxdepth=0;maxzero=0
        def prefix_check(p,chain):
            nonlocal maxdepth,maxzero
            maxdepth=max(maxdepth,len(p));maxzero=max(maxzero,max(map(len,p.split('1'))))
            if '0'*(a.zero_limit+1) in p or len(p)>64:
                assert chain,'Immutable source violation';bad.add(frozenset(chain));return False
            return True
        def ew(i,p,chain):
            nonlocal leaves
            if not prefix_check(p,chain):return
            e=expr[i]
            if e[0]=='L':leaves+=1
            elif e[0]=='W':ww(e[1],p,chain)
            else:ew(e[1],p+'0',chain);ew(e[2],p+'1',chain)
        def ww(w,p,chain):
            if not prefix_check(p,chain):return
            if w in allowed:ew(atoms[w],p,chain)
            else:
                lr=g.get(w,old.get(w));assert lr is not None
                if w in g:chain=chain+(yindex[w,lr],)
                ww(lr[0],p+'0',chain);ww(lr[1],p+'1',chain)
        ew(root,'',())
        return bad,dict(source_leaves_if_complete=leaves,maximum_depth_seen=maxdepth,maximum_zero_run_seen=maxzero)
    start=time.monotonic();iterations=[];candidate=None;summary=None
    while time.monotonic()-start<a.seconds:
        rs=[];cs=[];vs=[]
        for i,row in enumerate(rows):
            for j,v in row.items():rs.append(i);cs.append(j);vs.append(v)
        mat=coo_matrix((vs,(rs,cs)),shape=(len(rows),nv)).tocsc()
        result=milp(cost,integrality=integrality,bounds=Bounds(lb,ub),constraints=LinearConstraint(mat,np.array(lower),np.array(upper)),options=dict(time_limit=max(0.1,a.seconds-(time.monotonic()-start)),mip_rel_gap=0.0,disp=False))
        gap=getattr(result,'mip_gap',None);nodes=getattr(result,'mip_node_count',None)
        item=dict(status=int(result.status),message=result.message,objective=float(result.fun) if result.fun is not None else None,gap=float(gap) if gap is not None else None,nodes=int(nodes) if nodes is not None else None)
        iterations.append(item);print('MILP',item,flush=True)
        if result.x is None:break
        g=unpack(result.x);bad,summary=validate(g);item.update(roles=len(g),bad_clauses=len(bad),finite_summary=summary)
        if not bad:
            candidate=g
            break
        for clause in bad:add({v:1 for v in clause},hi=len(clause)-1)
        if result.status!=0:break
    status='FEASIBLE_WITHIN_FINITE_POOL' if candidate is not None else 'NO_FINITE_SOURCE_VALID_WITNESS_RETURNED'
    record=dict(status=status,seconds=time.monotonic()-start,word_pool=len(words),parse_choices=len(varwords),variables=nv,constraints=len(rows),zero_limit=a.zero_limit,height_model=a.height_model,feasible_target=a.target if a.feasible_target else None,relaxed_bootstrap_locks=a.relaxed,iterations=iterations,source_summary=summary,scope=__doc__)
    if candidate is not None:
        record['rules_count']=len(candidate)
        output=dict(baseline,rules_count=len(candidate),roots=roots,rules=[[w,*candidate[w]] for w in sorted(candidate)],properties=[],finite_pool_optimization=record)
        a.output.with_suffix('.grammar.json').write_text(json.dumps(output,indent=2)+'\n')
    a.output.write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record,indent=2))

if __name__=='__main__':main()

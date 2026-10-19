#!/usr/bin/env python3
"""Finite-vocabulary grammar optimization; no binary correctness claim.

Each selected word chooses exactly one binary split. Selecting a split
requires both nonterminal children. This is an exact integer formulation
within the supplied vocabulary; it is not an unrestricted grammar bound.
"""
import argparse
import json
import time
from collections import defaultdict
from functools import lru_cache
from pathlib import Path

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import coo_matrix


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--package', type=Path, required=True)
    ap.add_argument('--vocabulary', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--seconds', type=float, default=60)
    ap.add_argument('--rounds', type=int, default=10)
    ap.add_argument('--zero-bound', type=int, default=6)
    ap.add_argument('--boot-locks', action='store_true')
    ap.add_argument('--free-routes', action='store_true')
    args = ap.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    base = args.package
    source = json.loads((base/'inputs/closed-sequence-grammar-next22.json').read_text())
    symbols = json.loads((base/'inputs/semantic-symbols.json').read_text())
    enc = {v:k for k,v in symbols.items()}
    seed = json.loads((base/'grammar.json').read_text())
    text = (base/'inputs/semantic.txt').read_text().splitlines()
    n,nr,na = map(int,text[0].split())
    names = {int(q):w for k,w,q in map(str.split,text[1:n+1])}
    old = {w:(w[:int(k)],w[int(k):]) for k,w,q in map(str.split,text[1:n+1])}
    allowed = {c:int(v) for c,v in map(str.split,text[1+n+nr:])}
    byast = {int(i):names[int(q)] for q,i in source['sequence_ast_roots'].items()}
    released = {24,89,107,152,154,175,188,207,213,245}
    roots = {names[q] for q in source['required_entry_roots'] if q not in released}
    routes = {(r['source'],r['read']):r['word'] for r in seed['routes']}
    vocabulary_roots=roots|set(routes.values())
    if not args.free_routes:
        roots.update(routes.values())
    constraints = []
    group_constraints=defaultdict(list)
    for c in source['left_entry_projection_constraints']:
        reason = c['reason']
        pre = c['prefix']
        if reason.get('via') == 177:
            pre = str(reason['previous']) + pre
        target=''.join(enc[v] for v in c['word'])
        group_constraints[reason['source'],reason['read']].append((pre,target))
        if not args.free_routes:
            constraints.append((routes[reason['source'],reason['read']],pre,target))
    if args.boot_locks:
        for line in (base/'inputs/state_reduction/bootstrap-lock54.txt').read_text().splitlines()[1:]:
            w,bit,child = line.split()
            roots.add(w)
            constraints.append((w,bit,child))
    vocabulary = set(args.vocabulary.read_text().splitlines()) | set(old) | set(symbols)
    vocabulary.update(w for row in seed['rules'] for w in row)
    # No useful parse of a fixed root can need a word absent from every root.
    vocabulary = {w for w in vocabulary if w and any(w in root for root in vocabulary_roots)}
    vocabulary.update(symbols)
    splits = {}
    for w in sorted(vocabulary,key=lambda w:(len(w),w)):
        if len(w)==1:
            continue
        options=[]
        for k in range(1,len(w)):
            l,r=w[:k],w[k:]
            if l not in vocabulary or r not in vocabulary:
                continue
            if (len(l)==1 and not allowed[l]&1) or (len(r)==1 and not allowed[r]&2):
                continue
            if (len(l)>1 and l not in splits) or (len(r)>1 and r not in splits):
                continue
            options.append((l,r))
        if options:
            splits[w]=options
    assert roots<=splits.keys(), roots-splits.keys()
    # Reachability through any available split prunes irrelevant vocabulary.
    reachable=set()
    def visit(w):
        if len(w)==1 or w in reachable:
            return
        reachable.add(w)
        for pair in splits[w]:
            for child in pair:
                visit(child)
    route_options={}
    if args.free_routes:
        for group,cs in group_constraints.items():
            root_options={}
            for w,options in splits.items():
                suitable={}
                for pair in options:
                    child_constraints=defaultdict(dict)
                    good=True
                    for pre,target in cs:
                        child=pair[int(pre[0])]
                        if len(pre)==1:
                            if child!=target:
                                good=False;break
                        else:
                            assert len(pre)==2
                            bit=int(pre[1])
                            previous=child_constraints[child].get(bit)
                            if previous is not None and previous!=target:
                                good=False;break
                            child_constraints[child][bit]=target
                    child_options={}
                    if good:
                        for child,requirements in child_constraints.items():
                            matching=[p for p in splits.get(child,[]) if all(p[bit]==t for bit,t in requirements.items())]
                            if not matching:
                                good=False;break
                            child_options[child]=matching
                    if good:
                        suitable[pair]=child_options
                if suitable:
                    root_options[w]=suitable
            assert root_options,('No admissible route word',group)
            route_options[group]=root_options
    possible_roots=roots|{w for opts in route_options.values() for w in opts}
    for root in possible_roots:
        visit(root)
    splits={w:splits[w] for w in sorted(reachable,key=lambda w:(len(w),w))}
    x={w:i for i,w in enumerate(splits)}
    y={}
    for w,options in splits.items():
        for pair in options:
            y[w,pair]=len(x)+len(y)
    z={}
    for group,options in route_options.items():
        for w in options:
            z[group,w]=len(x)+len(y)+len(z)
    nv=len(x)+len(y)+len(z)
    rows=[]
    lower=[]
    upper=[]
    def add(coeff,lo=-np.inf,hi=np.inf):
        rows.append(coeff)
        lower.append(lo)
        upper.append(hi)
    for w,options in splits.items():
        add({x[w]:-1,**{y[w,p]:1 for p in options}},0,0)
        for pair in options:
            for child in set(pair):
                if len(child)>1:
                    add({y[w,pair]:1,x[child]:-1},hi=0)
    # Projection constraints include the folded left-entry contexts.
    for w,pre,target in constraints:
        bit=int(pre[0])
        for pair in splits[w]:
            child=pair[bit]
            if len(pre)==1:
                if child!=target:
                    add({y[w,pair]:1},hi=0)
            else:
                assert len(pre)==2
                compatible=[] if child not in splits else [y[child,p]
                    for p in splits[child] if p[int(pre[1])]==target]
                add({y[w,pair]:1,**{i:-1 for i in compatible}},hi=0)
    for group,options in route_options.items():
        add({z[group,w]:1 for w in options},1,1)
        for w,pair_options in options.items():
            zi=z[group,w]
            add({zi:1,**{y[w,p]:-1 for p in pair_options}},hi=0)
            for pair,children in pair_options.items():
                for child,compatible in children.items():
                    add({zi:1,y[w,pair]:1,**{y[child,p]:-1 for p in compatible}},hi=1)
    lb=np.zeros(nv)
    ub=np.ones(nv)
    for w in roots:
        lb[x[w]]=1
    objective=np.zeros(nv)
    objective[:len(x)]=1
    record=dict(scope='Integer optimization within the supplied finite vocabulary and semantic source roots; optional route choices are explicitly listed. Floating solver reports, no certified global lower bound.',
                nonterminal_words=len(x),split_options=len(y),initial_constraints=len(rows),
                roots=len(roots),route_options=len(z),free_routes=args.free_routes,
                boot_locks=args.boot_locks,rounds=[])
    print(json.dumps({k:v for k,v in record.items() if k!='rounds'}),flush=True)
    cutkeys=set()
    begin=time.monotonic()
    for iteration in range(args.rounds):
        ri=[];ci=[];va=[]
        for i,row in enumerate(rows):
            for j,v in row.items():
                if v:
                    ri.append(i);ci.append(j);va.append(v)
        matrix=coo_matrix((va,(ri,ci)),shape=(len(rows),nv)).tocsc()
        result=milp(objective,integrality=np.ones(nv),bounds=Bounds(lb,ub),
                    constraints=LinearConstraint(matrix,np.array(lower),np.array(upper)),
                    options=dict(time_limit=args.seconds,mip_rel_gap=0.0))
        info=dict(round=iteration,status=int(result.status),message=result.message,
                  seconds=time.monotonic()-begin,
                  dual_bound=float(result.mip_dual_bound) if getattr(result,'mip_dual_bound',None) is not None else None)
        record['rounds'].append(info)
        if result.x is None:
            print(json.dumps(info),flush=True)
            break
        g={w:pair for (w,pair),i in y.items() if result.x[i]>0.5}
        assert len(g)==round(result.fun)
        assert roots<=g.keys()
        for w,(l,r) in g.items():
            assert w==l+r
            assert all(len(c)==1 or c in g for c in (l,r))
        info['rules']=len(g)
        out=seed.copy()
        out.update(status='ABSTRACT_ROUTING_GRAMMAR_ONLY',rules_count=len(g),
                   rules=[[w,*g[w]] for w in sorted(g)],roots=sorted(roots),
                   framework_states=118,short_scan=False,properties=[],boot_lock_rows=[])
        if args.free_routes:
            out['routes']=[dict(source=group[0],read=group[1],word=w)
                           for (group,w),i in z.items() if result.x[i]>0.5]
            assert len(out['routes'])==len(group_constraints)
            for route in out['routes']:
                group=route['source'],route['read']
                for pre,target in group_constraints[group]:
                    w=route['word']
                    for bit in pre:
                        w=g[w][int(bit)]
                    assert w==target
        # Track every mutable ancestor of each offending path. If a fallback
        # old word is inactive, activating it is also a legitimate repair.
        bad=[]
        all_paths=[]
        def ep(i,path,chosen,inactive):
            if i in byast:
                return wp(byast[i],path,chosen,inactive)
            node=source['ast_dag'][i]
            if node[0]=='L':
                all_paths.append(path)
                if max(map(len,path.split('1')))>args.zero_bound or len(path)>64:
                    bad.append((chosen,inactive))
                return
            ep(node[1],path+'0',chosen,inactive)
            ep(node[2],path+'1',chosen,inactive)
        def wp(w,path,chosen,inactive):
            if len(w)==1:
                return ep(source['atoms'][symbols[w]]['ast'],path,chosen,inactive)
            if w in g:
                pair=g[w]
                chosen=chosen|{y[w,pair]}
            else:
                pair=old[w]
                if w in x:
                    inactive=inactive|{x[w]}
            wp(pair[0],path+'0',chosen,inactive)
            wp(pair[1],path+'1',chosen,inactive)
        ep(source['original_ast'],'',frozenset(),frozenset())
        info.update(depth=max(map(len,all_paths)),maximum_zero_run=max(len(z) for p in all_paths for z in p.split('1')),
                    scanner_violating_leaves=len(bad))
        out['properties']=[len(all_paths[0]),info['maximum_zero_run'],info['depth']]
        out['milp']=info
        (args.output/f'candidate-{iteration:02}.json').write_text(json.dumps(out,indent=2)+'\n')
        print(json.dumps(info),flush=True)
        if not bad:
            info['scope']='Valid abstract source properties; literal binary realization and initialization are separate.'
            break
        added=0
        for chosen,inactive in bad:
            key=tuple(sorted(chosen)),tuple(sorted(inactive))
            if key in cutkeys:
                continue
            cutkeys.add(key)
            assert chosen or inactive,'Immutable path violates the requested bound'
            add({**{i:1 for i in chosen},**{i:-1 for i in inactive}},hi=len(chosen)-1)
            added+=1
        info['new_validity_cuts']=added
        assert added
        (args.output/'search-record.json').write_text(json.dumps(record,indent=2)+'\n')
    (args.output/'search-record.json').write_text(json.dumps(record,indent=2)+'\n')


if __name__=='__main__':
    main()

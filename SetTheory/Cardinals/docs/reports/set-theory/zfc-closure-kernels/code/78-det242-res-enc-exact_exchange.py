#!/usr/bin/env python3
"""Exact fixed-route one- and two-definition exchanges in a finite dictionary.

The candidate neighborhood retains roots and current route-entry words. It
deletes at most two shared definitions, reparses every direct consumer jointly,
and introduces at most one new definition whose two children already exist.
All source words, orientations, route projections and bootstrap locks are exact.
This is a grammar search, not a TM correctness proof.
"""
from pathlib import Path
from itertools import combinations
from functools import lru_cache
import argparse,json,time

HERE=Path(__file__).resolve().parent

def load_context():
    lines=(HERE/'fine-grammar.txt').read_text().strip().splitlines()
    nr,nroot,na=map(int,lines[0].split())
    old={w:(w[:int(k)],w[int(k):]) for k,w,q in map(str.split,lines[1:1+nr])}
    roots=lines[1+nr:1+nr+nroot]
    allowed={w:int(m) for w,m in map(str.split,lines[1+nr+nroot:])}
    assert len(allowed)==na
    toks=iter((HERE/'fine-constraints.txt').read_text().split())
    groups=[]
    for i in range(int(next(toks))):
        source,read,word,nc=int(next(toks)),int(next(toks)),next(toks),int(next(toks))
        cs=[(next(toks),next(toks)) for j in range(nc)]
        groups.append((source,read,word,cs))
    ne,root,natom=int(next(toks)),int(next(toks)),int(next(toks))
    expr=[]
    for i in range(ne):
        k=next(toks)
        if k=='W':expr.append((k,next(toks)))
        elif k=='N':expr.append((k,int(next(toks)),int(next(toks))))
        else:expr.append((k,))
    atoms={next(toks):int(next(toks)) for i in range(natom)}
    assert list(toks)==[]
    locks=[tuple(x.split()) for x in (HERE/'fine-lock54.txt').read_text().strip().splitlines()[1:]]
    roots=list(dict.fromkeys(roots+[q for q,p,t in locks]))
    return old,roots,allowed,groups,expr,root,atoms,locks

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--input',type=Path,default=HERE/'baseline_fine_grammar.json');ap.add_argument('--output',type=Path,default=HERE/'exact_exchange_result.json');ap.add_argument('--max-branches',type=int,default=50000);ap.add_argument('--seconds',type=float,default=300)
    a=ap.parse_args();old,roots,allowed,groups,expr,root,atoms,locks=load_context()
    data=json.loads(a.input.read_text());base={w:(l,r) for w,l,r in data['rules']}
    routes={(r['source'],r['read']):r['word'] for r in data['routes']}
    checks=locks+[(routes[s,b],p,t) for s,b,w,cs in groups for p,t in cs]
    mandatory=set(roots)|set(routes.values())|{t for q,p,t in locks}
    terminals=set(allowed);known=set(base)|terminals
    def permitted(l,r):return (l not in allowed or allowed[l]&1) and (r not in allowed or allowed[r]&2)
    def options(w,available):
        return [(w[:k],w[k:]) for k in range(1,len(w)) if w[:k] in available and w[k:] in available and permitted(w[:k],w[k:])]
    original_splits={w:options(w,known) for w in base}
    def valid_checks(g,mutable=frozenset(),assigned=frozenset()):
        for q,p,target in checks:
            unfinished=False
            for c in p:
                if q in mutable and q not in assigned:unfinished=True;break
                if q not in g:return False
                q=g[q][int(c)]
            if not unfinished and q!=target:return False
        return True
    def collect(g):
        live=set();todo=list(roots)+list(routes.values())
        while todo:
            q=todo.pop()
            if q in terminals or q in live:continue
            if q not in g:return None
            live.add(q);todo.extend(g[q])
        return {q:g[q] for q in live}
    def properties(g):
        seen=set()
        def join(x,y):return 1+x[0],max(1+x[0],x[1],y[1]),1+max(x[2],y[2])
        @lru_cache(None)
        def ep(i):
            x=expr[i]
            return (0,0,0) if x[0]=='L' else wp(x[1]) if x[0]=='W' else join(ep(x[1]),ep(x[2]))
        @lru_cache(None)
        def wp(w):
            if w in seen:raise ValueError('recursive word')
            seen.add(w)
            if w in terminals:r=ep(atoms[w])
            else:r=join(*(wp(c) for c in g.get(w,old.get(w))))
            seen.remove(w);return r
        return ep(root)
    assert valid_checks(base)
    assert len(collect(base))==len(base)==128
    assert properties(base)[1]<=6
    begin=time.monotonic();stats=dict(erased_sets=0,one_new_trials=0,complete_assignments=0,route_valid=0,branch_caps=0,finite_property_rejections=0)
    best=base;bestprops=properties(base);bestmeta=None
    eligible=sorted(set(base)-mandatory,key=lambda w:(len(w),w))
    def solve(erased,z=None):
        nonlocal best,bestprops,bestmeta
        available=known-erased
        changed={p for p,(l,r) in base.items() if p not in erased and (l in erased or r in erased)}
        splits={p:[lr for lr in original_splits[p] if not(set(lr)&erased)] for p in changed}
        if z is not None:
            splits[z]=options(z,available)
            if not splits[z]:return False
            for p in changed:splits[p]=options(p,available|{z})
        if any(not x for x in splits.values()):return False
        current={w:lr for w,lr in base.items() if w not in erased}
        order=sorted(splits,key=lambda w:(len(splits[w]),len(w),w));mutable=set(order)
        # Old splits can be retained if they have become valid after a peer edit.
        assigned=set();visited=0
        def backtrack(i):
            nonlocal visited,best,bestprops,bestmeta
            visited+=1
            if visited>a.max_branches:return False
            if not valid_checks(current,mutable,assigned):return False
            if i==len(order):
                stats['complete_assignments']+=1
                cg=collect(current)
                if cg is None or len(cg)>=len(best):return False
                stats['route_valid']+=1
                try:prop=properties(cg)
                except (ValueError,TypeError,RecursionError):return False
                if prop[1]>6 or prop[2]>64:stats['finite_property_rejections']+=1;return False
                best,bestprops=cg,prop
                bestmeta=dict(erased=sorted(erased),introduced=z,reparsed={w:list(current[w]) for w in order},visited=visited)
                print('FOUND',len(best),stats,flush=True);return True
            w=order[i];assigned.add(w)
            for lr in splits[w]:
                current[w]=lr
                if backtrack(i+1):return True
            assigned.remove(w)
            return False
        found=backtrack(0)
        if visited>a.max_branches:stats['branch_caps']+=1
        return found
    stop=False
    for size in (1,2):
        if stop:break
        for values in combinations(eligible,size):
            if time.monotonic()-begin>a.seconds:stop=True;break
            erased=set(values);stats['erased_sets']+=1
            if solve(erased):stop=True;break
            if size==1:continue
            available=known-erased
            affected={p for p,(l,r) in base.items() if p not in erased and (l in erased or r in erased)}
            forced=[p for p in affected if not any(not(set(lr)&erased) for lr in original_splits[p])]
            all_have_old_splits=not forced
            if not forced:forced=list(affected)
            common=None
            for p in forced:
                pool=set()
                for k in range(1,len(p)):
                    l,r=p[:k],p[k:]
                    if not permitted(l,r):continue
                    if l in available and r not in known:pool.add(r)
                    if r in available and l not in known:pool.add(l)
                common=pool if common is None else common|pool if all_have_old_splits else common&pool
                if not common and not all_have_old_splits:break
            for z in sorted(common or (),key=lambda w:(len(w),w)):
                stats['one_new_trials']+=1
                if solve(erased,z):stop=True;break
            if stop:break
            if stats['erased_sets']%500==0:print('PROGRESS',stats,round(time.monotonic()-begin,2),flush=True)
    record=dict(status='FOUND_SMALLER_GRAMMAR' if len(best)<len(base) else 'NO_SMALLER_IN_SEARCHED_NEIGHBORHOOD',seconds=time.monotonic()-begin,stats=stats,eligible=len(eligible),initial_count=len(base),best_count=len(best),best_properties=bestprops,change=bestmeta,scope=__doc__)
    a.output.write_text(json.dumps(record,indent=2)+'\n')
    if bestmeta:
        result=dict(data,rules_count=len(best),properties=list(bestprops),rules=[[w,*best[w]] for w in sorted(best)],exact_exchange=record)
        a.output.with_suffix('.grammar.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(record,indent=2))

if __name__=='__main__':main()

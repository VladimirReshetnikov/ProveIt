#!/usr/bin/env python3
"""Safe logical clause permutations, with the original rho6/rho8 retained.

Each changed A -> (B -> C) is a permutation of its three-literal classical
clause. Pure implication exchanges use no falsum; the remaining four forms
use explosion/DNE already proved from retained rho6/rho8. This is a finite
encoding screen, not a proof of a globally optimal state count.
"""
from functools import lru_cache
from pathlib import Path
import argparse
import itertools
import json
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
import a10_source_search as a

z, s = a.z, a.s
I = z.I
N = z.N
ROOT = Path(__file__).resolve().parents[1]


def nodes(n):
    found = set()
    todo = [n]
    while todo:
        t = todo.pop()
        if t in found:
            continue
        found.add(t)
        if not s.leaf(t):
            todo.extend(t)
    return found


oldnodes = nodes(a.old)
known_word = {}
for n in oldnodes:
    if s.boundary(n) == (0, 0, False):
        known_word.setdefault(z.flat(n), []).append(n)


def emit(f, perm):
    pushes = dict(zip(('a','b','c'), perm))
    pushes[1] = z.MACRO[177]
    def go(t):
        if not isinstance(t, tuple):
            return [pushes[t]]
        op, x, y = t
        if op == 'I' and y == 1:
            return go(x) + [z.MACRO[218]]
        return go(x) + go(y) + [z.MACRO[{'I':119,'R':181,'E':182,'Q':180}[op]]]
    return go(f)


def clause_forms(f):
    _, A, rest = f
    assert rest[0] == 'I'
    _, B, C = rest
    return [I(A,I(B,C)), I(B,I(A,C)),
            I(N(C),I(B,N(A))), I(B,I(N(C),N(A))),
            I(N(C),I(A,N(B))), I(A,I(N(C),N(B)))]


def parses(atoms, width=8):
    """Token-boundary DP favors whole old subtrees and shared new subtrees."""
    words = [z.flat(n) for n in atoms]
    pref = [()]
    for w in words:
        pref.append(pref[-1] + w)
    @lru_cache(None)
    def profile(n):
        if s.leaf(n):
            return 0, 0, 0
        la,za,ha=profile(n[0]);lb,zb,hb=profile(n[1])
        return 1+la,max(1+la,za,zb),1+max(ha,hb)
    @lru_cache(None)
    def fresh(n):
        if n in oldnodes:
            return frozenset()
        return frozenset({n}) if s.leaf(n) else fresh(n[0])|fresh(n[1])|{n}
    @lru_cache(None)
    def go(i,j):
        word = pref[j][len(pref[i]):]
        candidates = set(known_word.get(word, ()))
        if j == i+1:
            candidates.add(atoms[i])
        for k in range(i+1,j):
            for l in go(i,k):
                for r in go(k,j):
                    n = l,r
                    p = profile(n)
                    if p[1] <= 7 and p[2] <= 50:
                        candidates.add(n)
        return tuple(sorted(candidates,key=lambda n:(len(fresh(n)),profile(n)[1],profile(n)[2],str(n)))[:width])
    return go(0,len(atoms))


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--forms',type=int,default=2)
    ap.add_argument('--width',type=int,default=6)
    ap.add_argument('--beam',type=int,default=8)
    ap.add_argument('--out',type=Path,default=ROOT/'theory_notes/antecedent_variants')
    args=ap.parse_args()
    args.out.mkdir(exist_ok=True)
    objective=a.hw.make(a.table,a.old)[0]
    pushes=(z.MACRO[166],z.MACRO[121],z.MACRO[168])
    layouts={}
    results=[]
    best=999
    start=time.monotonic()
    for name in ('rho2','rho3','rho5','G'):
        lo,hi=z.INTERVALS[name]
        layouts[name]=[]
        for fi,f in enumerate(clause_forms(z.FORMULAS[name])[:args.forms]):
            for pi,perm in enumerate(itertools.permutations(pushes)):
                for ni,n in enumerate(parses(emit(f,perm),args.width)):
                    for last in (False,True):
                        new=a.splice(a.old,lo,hi,n,last)
                        cost=objective(new)
                        metric=s.metrics(new)
                        row=dict(row=name,form=fi,permutation=pi,parse=ni,insert_last=last,hardware_lower_bound=cost,metrics=metric)
                        results.append(row)
                        layouts[name].append((cost['cost_lower_bound'],metric['dag_nodes'],row,n,last))
                        if cost['cost_lower_bound']<best:
                            best=cost['cost_lower_bound']
                            print('BEST',json.dumps(row),flush=True)
                        if cost['cost_lower_bound']<=221:
                            d=args.out/f'{name}_f{fi}_p{pi}_n{ni}_i{int(last)}'
                            d.mkdir(exist_ok=True)
                            rows=s.sites(new)
                            assert s.graph_arithmetic(rows)[0]==s.graph_intervals(rows)
                            (d/'sites.json').write_bytes(s.compact(rows))
                            (d/'receipt.json').write_text(json.dumps(row,indent=2)+'\n')
        layouts[name].sort(key=lambda x:(x[0],x[1]))
        print('ROW',name,'tested',len(layouts[name]),'best',layouts[name][0][:2], 'seconds',time.monotonic()-start,flush=True)
    (args.out/'individual_results.json').write_text(json.dumps(results,indent=2)+'\n')
    # A small sequential beam composes independent row replacements. Work from
    # high to low original ordinal intervals so all remaining offsets persist.
    beam=[(a.old,[],objective(a.old))]
    combined=[]
    for name in ('rho2','rho3','rho5','G'):
        lo,hi=z.INTERVALS[name]
        candidates=[]
        seen=set()
        for tree,recipe,prior in beam:
            for _,_,row,n,last in layouts[name][:args.beam*3]:
                new=a.splice(tree,lo,hi,n,last)
                if new in seen:continue
                seen.add(new)
                rec=recipe+[row]
                score=objective(new)
                candidates.append((score['cost_lower_bound'],s.metrics(new)['dag_nodes'],new,rec,score))
        candidates.sort(key=lambda x:x[:2])
        beam=[(new,rec,score)for _,_,new,rec,score in candidates[:args.beam]]
        if not beam:break
        new,rec,score=beam[0]
        status=dict(rows=[r['row']for r in rec],metrics=s.metrics(new),hardware_lower_bound=score)
        combined.append(status)
        print('COMBINED',json.dumps(status),flush=True)
        if score['cost_lower_bound']<=221:
            d=args.out/('combined_'+name);d.mkdir(exist_ok=True)
            rows=s.sites(new)
            assert s.graph_arithmetic(rows)[0]==s.graph_intervals(rows)
            (d/'sites.json').write_bytes(s.compact(rows))
            (d/'receipt.json').write_text(json.dumps(dict(recipe=rec,**status),indent=2)+'\n')
    (args.out/'combined_results.json').write_text(json.dumps(combined,indent=2)+'\n')
    print('DONE',len(results),time.monotonic()-start,flush=True)


if __name__=='__main__':
    main()

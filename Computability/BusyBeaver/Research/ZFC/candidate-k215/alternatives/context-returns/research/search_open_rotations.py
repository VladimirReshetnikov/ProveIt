#!/usr/bin/env python3
"""Bounded exact-CFG source reassociation search, including open factors.

Conditional decrements keep both targets. Only CB/CC depths may be repaired.
This is a source optimizer, not a binary correctness checker.
"""
import importlib.util
from pathlib import Path
import json, time, hashlib

HERE = Path(__file__).resolve().parent
BASE = HERE.parent/'machine'
spec=importlib.util.spec_from_file_location('s', HERE.parent/'code/source_language.py')
s=importlib.util.module_from_spec(spec);spec.loader.exec_module(s)

def internal(n,p=''):
    if s.leaf(n): return
    yield p,n
    yield from internal(n[0],p+'0')
    yield from internal(n[1],p+'1')

def relevel(n, expected):
    rows=s.sites((n,('CH',None)))
    leaves={r[0]:i for i,r in enumerate(rows)}
    intervals={}
    def visit(path):
        if path in leaves:
            a,b=leaves[path],leaves[path]+1
        else:
            a,_=visit(path+'0');_,b=visit(path+'1')
        intervals[path]=(a,b);return a,b
    visit('');N=len(rows)
    def target(path,edge,k):
        while path:
            last,path=path[-1],path[:-1]
            if last==edge:
                k-=1
                if not k:return intervals[path][1]%N if edge=='0' else intervals[path][0]
        return 0
    for i,(path,op,arg) in enumerate(rows):
        before=expected[i]
        if op=='CD':
            if target(path,'0',1)!=before[1][0]:return None
        elif op in ('CB','CC'):
            edge='0' if op=='CB' else '1';goal=before[1][0]
            if target(path,edge,arg)!=goal:
                good=[k for k in range(1,5) if target(path,edge,k)==goal]
                if not good:return None
                rows[i][2]=min(good)
    root=s.tree(rows)
    if s.graph_intervals(rows)!=expected:return None
    ans=root[0]
    if s.boundary(ans)[:2]!=(0,0):return None
    return ans

def main():
    source=HERE/'sites-cachemp.json'
    full=s.tree(json.loads(source.read_text()))
    path='110100101';orig=s.subtree(full,path)
    expected=s.graph_intervals(s.sites((orig,('CH',None))))
    def cost(n):return s.metrics(s.replace(full,path,n))['dag_nodes']
    seen={orig};beam=[orig];best=cost(orig);saved=[];trials=valid=0
    started=time.monotonic();rounds=0
    for rnd in range(12):
        pool={n:cost(n) for n in beam}
        for n in beam:
            for p,node in internal(n):
                candidates=[]
                if not s.leaf(node[1]):
                    a,(b,c)=node;candidates.append(((a,b),c))
                if not s.leaf(node[0]):
                    (a,b),c=node;candidates.append((a,(b,c)))
                for replacement in candidates:
                    trials+=1
                    candidate=relevel(s.replace(n,p,replacement),expected)
                    if candidate is None or candidate in seen:continue
                    valid+=1;seen.add(candidate);v=cost(candidate)
                    if v<=best:
                        if v<best:best=v;saved=[]
                        saved.append(candidate)
                        print('BEST',best,'trial',trials,'round',rnd,flush=True)
                        raw=s.compact(s.sites(s.replace(full,path,candidate)))
                        (HERE/f'cache-open-best-{best}-{len(saved)-1}.json').write_bytes(raw)
                    if v<=202:pool[candidate]=v
        rounds=rnd+1
        ordered=sorted(pool,key=lambda n:(pool[n],len(s.sites(n)),repr(n)))
        nxt=ordered[:32]
        if nxt==beam or time.monotonic()-started>90:break
        beam=nxt
    result={'trials':trials,'valid_new_graphs':valid,'best_DAG':best,'rounds':rounds,'seconds':time.monotonic()-started,'scope':'Exact source CFG preservation inside MP, including control-depth repair; finite bounded search, no binary allocation or lower bound.'}
    (HERE/'open_rotation_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()

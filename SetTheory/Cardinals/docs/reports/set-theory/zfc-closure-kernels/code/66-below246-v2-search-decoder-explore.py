#!/usr/bin/env python3
"""Discover decoder associations; only a bisimulation certificate proves semantics."""
from pathlib import Path
import sys,json,collections

ROOT=Path(__file__).resolve().parents[2]
BASE=ROOT/'reference/context246'
sys.path.insert(0,str(BASE/'code'))
sys.path.insert(0,str(ROOT/'reference/jeff/ZF/m254/tools/prog'))
from rebuild_machines import build,program_sites,PHYSICAL
import rmpath

T=build()
SITES=program_sites()
EOP={'CI':'inc','CD':'dec','CB':'brk','CC':'cont','CH':'halt'}
trie={}
for p,op,arg in SITES:
    c=trie
    for b in p[:-1]:c=c.setdefault(int(b),{})
    c[int(p[-1])]=('L',(EOP[op],) if op=='CH' else (EOP[op],arg))

STATES=collections.defaultdict(list)
PREFIXES=collections.defaultdict(list)
EDGES=collections.defaultdict(set)
NODESTATES=set()

def tree(c,q=96,p=''):
    if not isinstance(c,dict):return c
    if q is not None:
        NODESTATES.add(q)
        PREFIXES[q].append(p)
    childs=[]
    for b in (0,1):
        w,d,t=T[q,b] if q is not None else (None,None,None)
        e=c[b]
        if isinstance(e,dict):
            if q is not None:EDGES[q,b].add(('N',t))
            childs.append(tree(e,t if (w,d)==(b,'R') else None,p+str(b)))
        else:
            if q is not None:EDGES[q,b].add(e)
            childs.append(e)
    out=('N',*childs)
    if q is not None and out not in STATES[q]:STATES[q].append(out)
    return out

ORIGINAL=tree(trie)
GRAPH={k:next(iter(v)) for k,v in EDGES.items() if len(v)==1}
PURE={q for q in NODESTATES if all(T[q,z][:2]==(z,'R') for z in(0,1))}
INCOMING=collections.defaultdict(list)
for k,(_,_,q) in T.items():INCOMING[q].append(k)

def bc(t):
    if t[0]=='L':
        e=t[1]
        return (1 if e[0]=='dec' else e[1] if e[0]=='brk' else 0,
                e[1] if e[0]=='cont' else 0)
    ab,ac=bc(t[1]);bb,bc_=bc(t[2])
    return max(ab-1,bb,0),max(ac,bc_-1,0)

def paths(t,p=''):
    if t[0]=='L':return [(p,t[1])]
    return paths(t[1],p+'0')+paths(t[2],p+'1')

def maxzeros(t):
    ps=paths(t)
    return max(max(map(len,p.split('1'))) for p,_ in ps)

def fromgraph(graph):
    memo={};active=set()
    def go(q):
        if q in memo:return memo[q]
        assert q not in active,('cycle',q)
        active.add(q)
        def edge(e):return go(e[1]) if e[0]=='N' else e
        t=('N',edge(graph[q,0]),edge(graph[q,1]));active.remove(q);memo[q]=t
        return t
    return go(96)

def main():
    print('node states',len(NODESTATES),'pure source nodes',len(PURE),'leaves',len(paths(ORIGINAL)))
    print('original bounds',bc(ORIGINAL),'maxzeros',maxzeros(ORIGINAL))
    print('self certificate',len(rmpath.certificate(ORIGINAL,ORIGINAL)))
    for q in (76,86,98,113,23,34):
        print('q',q,'paths',PREFIXES[q],'distincttrees',len(STATES[q]),'bc',[bc(t) for t in STATES[q]],'children',GRAPH.get((q,0)),GRAPH.get((q,1)))
        t=STATES[q][0]
        if t[1][0]=='N': print('rotation side condition',bc(t[1][1])[0],bc(t[2])[1])

if __name__=='__main__':main()

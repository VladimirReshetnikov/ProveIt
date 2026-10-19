"""Minimal source-only context for the attributed finite-dictionary optimizer."""
from pathlib import Path
from functools import lru_cache
from types import SimpleNamespace
import json
HERE=Path(__file__).resolve().parent
BASE=HERE/'data'
source=json.loads((BASE/'original203.json').read_text())
original={int(i):tuple(map(tuple,p)) for i,p in source['nodes'].items()}
original_root=source['root']
def edge_bounds(nodes):
    @lru_cache(None)
    def bound(e):
        if e[0]!='N':return 0,(e[1] if e[0]=='B' else int(e[0]=='D')),(e[1] if e[0]=='C' else 0)
        h0,b0,c0=bound(nodes[e[1]][0]);h1,b1,c1=bound(nodes[e[1]][1])
        return 1+max(h0,h1),max(b0-1,b1),max(c0,c1-1)
    return bound

def zero_metrics(nodes,root):
    @lru_cache(None)
    def calc(e):
        if e[0]!='N':return 0,0,0
        l,r=map(calc,nodes[e[1]]);p=l[0]+1
        return p,max(p,l[1],r[1]),1+max(l[2],r[2])
    return calc(('N',root))
rot=SimpleNamespace(edge_bounds=edge_bounds,zero_metrics=zero_metrics)

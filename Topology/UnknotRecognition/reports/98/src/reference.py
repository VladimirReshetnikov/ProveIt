"""Capped literal graph oracle and explicit-root-state baseline.

Exponential algorithms intended only for independent small tests/paired controls.
No imports from gauge_cuts or checker.
"""
from __future__ import annotations
from itertools import product
from typing import Any

class ExpansionLimit(ValueError): pass

def expand(g: dict, max_vertices: int=16, max_edges: int=256) -> list[dict]:
    graphs=[]
    for z in g["nodes"]:
        if z["op"]=="leaf":
            cur={"op":"leaf","vertices":z["vertices"][:],"edges":[e[:] for e in z["edges"]],"terminals":z["terminals"][:]}
        else:
            children=[graphs[j] for j in z["children"]]
            q=len(set(v for mp in z["maps"] for v in mp))
            n=sum(len(a["vertices"])-len(a["terminals"]) for a in children)+q
            m=sum(len(a["edges"]) for a in children)
            if n>max_vertices or m>max_edges: raise ExpansionLimit("literal reference cap")
            edges=[]; nxt=q
            for a,mp in zip(children,z["maps"]):
                old_to_new=dict(zip(a["terminals"],mp))
                for v in a["vertices"]:
                    if v not in old_to_new: old_to_new[v]=nxt; nxt+=1
                edges.extend([[old_to_new[u],old_to_new[v],w] for u,v,w in a["edges"]])
            cur={"op":"leaf","vertices":list(range(n)),"edges":edges,"terminals":z["keep"][:]}
        if len(cur["vertices"])>max_vertices or len(cur["edges"])>max_edges: raise ExpansionLimit("literal reference cap")
        graphs.append(cur)
    return graphs

def graph_components(z: dict) -> list[int]:
    n=len(z["vertices"]); adj=[[] for _ in range(n)]
    for u,v,_ in z["edges"]: adj[u].append(v); adj[v].append(u)
    own=[-1]*n; c=0
    for r in range(n):
        if own[r]>=0: continue
        own[r]=c; todo=[r]
        for v in todo:
            for w in adj[v]:
                if own[w]<0: own[w]=c; todo.append(w)
        c+=1
    return own

def literal_atlas(z: dict,k: int) -> set[tuple]:
    """All 2^n actual colorings, then quotient only the visible component gauges."""
    n=len(z["vertices"]); ts=z["terminals"]; own=graph_components(z)
    first={}; vis=[]
    for t in ts:
        if own[t] not in first: first[own[t]]=t; vis.append(own[t])
    out=set()
    for word in range(1<<n):
        d=0; tags=[0]*(max(own,default=-1)+1)
        for u,v,w in z["edges"]:
            a=(word>>u)&1; b=(word>>v)&1
            if a!=b: d+=w
            else: tags[own[u]]|=1<<a
        if d>k: continue
        p=0
        for j,t in enumerate(ts): p|=(((word>>t)^(word>>first[own[t]]))&1)<<j
        relative=[]
        for c in vis:
            mask=0; shift=(word>>first[c])&1
            for a in (0,1):
                if tags[c]&(1<<a): mask|=1<<(a^shift)
            relative.append(mask)
        hidden=0
        for c,a in enumerate(tags):
            if c not in first: hidden|=a
        out.add((d,p,tuple(relative),hidden))
    return out

def literal_response(z: dict,k: int) -> set[tuple[int,int,int]]:
    n=len(z["vertices"]); ts=z["terminals"]; out=set()
    for word in range(1<<n):
        d=0; flags=0
        for u,v,w in z["edges"]:
            a=(word>>u)&1; b=(word>>v)&1
            if a!=b: d+=w
            else: flags|=1<<a
        if d<=k: out.add((d,sum(((word>>t)&1)<<j for j,t in enumerate(ts)),flags))
    return out

def dense_compile(g: dict) -> dict:
    """Original-style exact response tables with explicit component root colors.

Used for small audit cases and component-factor benchmarks only.
"""
    k=g["k"]; tabs=[]; counts=[]; work=0
    for z in g["nodes"]:
        if z["op"]=="leaf":
            if len(z["vertices"])>20: raise ExpansionLimit("explicit leaf coloring cap")
            tab=literal_response(z,k); work+=1<<len(z["vertices"])
        else:
            tab=set(); ch=z["children"]
            if len(ch)==1: candidates=((r,) for r in tabs[ch[0]])
            else: candidates=product(tabs[ch[0]],tabs[ch[1]])
            for rs in candidates:
                d=sum(r[0] for r in rs)
                if d>k: continue
                work+=1; colors={}; valid=True; flags=0
                for row,mp in zip(rs,z["maps"]):
                    flags|=row[2]
                    for j,v in enumerate(mp):
                        b=(row[1]>>j)&1
                        if v in colors and colors[v]!=b: valid=False; break
                        colors[v]=b
                    if not valid: break
                if valid:
                    p=sum(colors[v]<<j for j,v in enumerate(z["keep"]))
                    tab.add((d,p,flags))
        tabs.append(tab); counts.append(len(tab))
    return {"tables":tabs,"peak_states":max(counts),"total_states":sum(counts),"candidate_work":work}

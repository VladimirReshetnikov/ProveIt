"""Static register-copy coalescing on the macro CFG with nine physical slots.

Graph vertices are storage live ranges, not logical registers. Transfers with
zero destination are candidate copy edges. Exact source masks justify splitting
live ranges wherever a register is definitely zero. No full table is emitted.
"""
from pathlib import Path
from collections import deque,defaultdict,Counter
import json,time,sys,random
import dynamic_renaming as d
ROOT=Path(__file__).parent

class DSU:
    def __init__(self,n):self.p=list(range(n));self.size=[1]*n
    def find(self,x):
        while x!=self.p[x]:self.p[x]=self.p[self.p[x]];x=self.p[x]
        return x
    def union(self,a,b):
        a=self.find(a);b=self.find(b)
        if a==b:return a
        if self.size[a]<self.size[b]:a,b=b,a
        self.p[b]=a;self.size[a]+=self.size[b];return a

def graph():
    edges={};seen={d.first};q=deque([d.first])
    while q:
        site=q.popleft()
        if site in d.swaps:
            r,t,dst=d.swaps[site];out=[(dst,('move',r,t))]
        else:
            out=[]
            for ci in d.by[site]:
                if d.transfer(d.values[site],ci) is None:continue
                dst=d.targets[ci]
                if dst is not None:out.append((dst,('step',ci)))
        edges[site]=out
        for dst,_ in out:
            if dst not in seen:seen.add(dst);q.append(dst)
    masks={site:d.entry_values.get(site,d.values[site]) for site in seen}
    variables={(site,r):i for i,(site,r) in enumerate((s,r) for s in sorted(seen) for r in range(9) if masks[s][r]!=1)}
    uf=DSU(len(variables));copies=[]
    for site,out in edges.items():
        for dst,kind in out:
            moved=kind[0]=='move'
            r,t=kind[1:] if moved else (-1,-1)
            for reg in range(9):
                if moved and reg in (r,t):continue
                if (site,reg) in variables and (dst,reg) in variables:
                    uf.union(variables[site,reg],variables[dst,reg])
            if moved and (site,r) in variables and (dst,t) in variables:
                copies.append((site,variables[site,r],variables[dst,t],r,t))
    ranges={uf.find(v) for v in variables.values()}
    adjacent={x:set() for x in ranges}
    for site in seen:
        active=[uf.find(variables[site,r]) for r in range(9) if (site,r) in variables]
        assert len(active)==len(set(active))
        for x in active:
            adjacent[x].update(y for y in active if x!=y)
    copies=[(site,uf.find(a),uf.find(b),r,t) for site,a,b,r,t in copies]
    return seen,edges,masks,variables,uf,adjacent,copies

def coalesce(adj,copies,mode='optimistic',seed=0,weights=None):
    graph={q:set(s) for q,s in adj.items()};mapping={q:q for q in adj}
    def find(x):
        while mapping[x]!=x:mapping[x]=mapping[mapping[x]];x=mapping[x]
        return x
    work=list(copies)
    if seed:random.Random(seed).shuffle(work)
    accepted=[];rejected=[]
    for site,a,b,r,t in work:
        a=find(a);b=find(b)
        if a==b:accepted.append(site);continue
        if b in graph[a]:rejected.append((site,'interference'));continue
        neigh=(graph[a]|graph[b])-{a,b}
        if mode=='briggs' and sum(len(graph[n])>=9 for n in neigh)>=9:
            rejected.append((site,'conservative_degree'));continue
        if len(graph[a])<len(graph[b]):a,b=b,a
        mapping[b]=a;graph[a]=neigh;del graph[b]
        for n in neigh:graph[n].discard(b);graph[n].add(a)
        accepted.append(site)
    # DSATUR greedy: exact edge verification follows, but count is an upper bound.
    color={};sat={q:set() for q in graph}
    preferences={q:Counter() for q in graph}
    if weights is not None:
        for q,w in weights.items():preferences[find(q)].update(w)
    while len(color)<len(graph):
        q=max((q for q in graph if q not in color),key=lambda q:(len(sat[q]),len(graph[q]),-q))
        choices=[c for c in range(9) if c not in sat[q]]
        if choices and weights is not None:
            c=max(choices,key=lambda c:(preferences[q][c],-c))
        else:
            c=0
            while c in sat[q]:c+=1
        color[q]=c
        for n in graph[q]:sat[n].add(c)
    assert all(color[a]!=color[b] for a in graph for b in graph[a])
    count=max(color.values())+1
    return dict(mode=mode,seed=seed,accepted=len(accepted),rejected=len(rejected),coalesced_ranges=len(graph),colors=count,accepted_sites=sorted(accepted),rejections=rejected),{q:color[find(q)] for q in mapping}

def main():
    t=time.monotonic();seen,edges,masks,variables,uf,adj,copies=graph()
    summary=dict(sites=len(seen),edges=sum(map(len,edges.values())),variables=len(variables),ranges=len(adj),interference_edges=sum(map(len,adj.values()))//2,candidate_copies=len(copies),copy_conflicts=sum(b in adj[a] for _,a,b,_,_ in copies))
    print(summary,flush=True)
    weights={q:Counter() for q in adj}
    for (site,r),v in variables.items():weights[uf.find(v)][r]+=1
    results=[];best=None
    for mode in ('optimistic','briggs'):
        for seed in range(40):
            result,colors=coalesce(adj,copies,mode,seed,weights=weights if '--prefer-logical' in sys.argv else None);results.append(result)
            metric=(result['colors']>9,-result['accepted'],result['colors'])
            if best is None or metric<best[0]:
                best=(metric,result,colors);print('best', {k:v for k,v in result.items() if k not in ('accepted_sites','rejections')},flush=True)
    result=dict(summary=summary,seconds=time.monotonic()-t,best=best[1],results=[{k:v for k,v in r.items() if k not in ('accepted_sites','rejections')} for r in results],allocation={str(site):[best[2][uf.find(variables[site,r])] if (site,r) in variables else None for r in range(9)] for site in sorted(seen)})
    (ROOT/'static-coalescing.json').write_text(json.dumps(result))
    print('seconds',result['seconds'],flush=True)

if __name__=='__main__':main()

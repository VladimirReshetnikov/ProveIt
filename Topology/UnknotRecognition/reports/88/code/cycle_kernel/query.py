"""Bounded-flow engine for the existence of a cut with both monochromatic marks."""
from collections import deque
from .model import Graph

def anchors(g:Graph):
    for i,e in enumerate(g.edges):
        for j in range(i+1,len(g.edges)):
            if set(e).isdisjoint(g.edges[j]):yield i,j

def capacities(g:Graph,i:int,j:int,limit:int):
    n=g.n;adj=[{} for _ in range(n+2)]
    def add(a,b,c):
        adj[a][b]=adj[a].get(b,0)+c
        adj[b].setdefault(a,0)
    for a,b in g.edges:
        if a!=b:add(a,b,1);add(b,a,1)
    for a in set(g.edges[i]):add(n,a,limit)
    for b in set(g.edges[j]):add(b,n+1,limit)
    return adj

def solve_graph(g:Graph,k:int=3)->dict:
    if type(k)is not int or k<0:raise ValueError('invalid cut threshold')
    limit=k+1;exclusions=[]
    for i,j in anchors(g):
        adj=capacities(g,i,j,limit);source=g.n;sink=g.n+1;flow=0;paths=[]
        while flow<limit:
            pred={source:None};todo=deque([source])
            while todo and sink not in pred:
                a=todo.popleft()
                for b,c in adj[a].items():
                    if c>0 and b not in pred:pred[b]=a;todo.append(b)
            if sink not in pred:
                colors=[0 if v in pred else 1 for v in range(g.n)]
                cut=[e for e,(a,b) in enumerate(g.edges) if colors[a]!=colors[b]]
                return dict(verdict='LOW_MARKED_CUT',threshold=k,colors=colors,cut_edges=cut,anchors=[i,j])
            path=[];a=sink
            while a is not None:path.append(a);a=pred[a]
            path.reverse();amount=min(limit-flow,min(adj[a][b] for a,b in zip(path,path[1:])))
            for a,b in zip(path,path[1:]):adj[a][b]-=amount;adj[b][a]+=amount
            flow+=amount;paths.append(dict(vertices=path,amount=amount))
        exclusions.append(dict(anchors=[i,j],paths=paths))
    return dict(verdict='NO_LOW_MARKED_CUT',threshold=k,exclusions=exclusions)

def closed_source_is_cubic(tile:Graph)->bool:
    tile.validate_tile();deg=[0]*tile.n
    for a,b in tile.edges:deg[a]+=1;deg[b]+=1
    ports=set(tile.left+tile.right)
    return all(deg[v]==3 for v in range(tile.n) if v not in ports) and all(deg[a]+deg[b]==3 for a,b in zip(tile.left,tile.right))

"""Direct edge-kernel, unique-giant and finite-fragment checks through n=6."""
from collections import Counter
from itertools import permutations
from math import factorial
from pathlib import Path
import contextlib, io, json
# Import also replays the independent direct graph census.
with contextlib.redirect_stdout(io.StringIO()):
    import check_graphs as direct

def edge_data(key):
    k,l,flip,cols=key
    edges=[(i,j) for j in range(l) for i in range(k) for _ in range(cols[j][i])]
    parent=list(range(k+l))
    def find(x):
        while parent[x]!=x:x=parent[x]
        return x
    for i,j in edges:parent[find(i)]=find(k+j)
    sizes=Counter(find(i) for i,j in edges)
    return edges,sorted(sizes.values())

def leaf_action(rmap,cmap,edges):
    rm=[i for i,v in enumerate(rmap) if i!=v]
    cm=[i for i,v in enumerate(cmap) if i!=v]
    if len(rm)==2 and not cm:
        i,j=rm
        ei=[v for u,v in edges if u==i]
        ej=[v for u,v in edges if u==j]
        return len(ei)==len(ej)==1 and ei==ej and rmap[i]==j and rmap[j]==i
    if len(cm)==2 and not rm:
        i,j=cm
        ei=[u for u,v in edges if v==i]
        ej=[u for u,v in edges if v==j]
        return len(ei)==len(ej)==1 and ei==ej and cmap[i]==j and cmap[j]==i
    return False

rows=[];permutations_checked=0;types=0
for n in range(7):
    ps=list(direct.rgs(n));graphs={direct.canonical(p,q) for p in ps for q in ps}
    fragments=Counter();no_giant=0;cosets_total=0;leaf_lifts_total=0
    for key in graphs:
        types+=1;k,l,flip,cols=key;edges,sizes=edge_data(key)
        kernel=1
        for m in Counter(edges).values():kernel*=factorial(m)
        fibers=Counter()
        for p in permutations(range(n)):
            permutations_checked+=1;rmap=[None]*k;cmap=[None]*l;valid=True
            for t,(u,v) in enumerate(edges):
                a,b=edges[p[t]]
                if (rmap[u] is not None and rmap[u]!=a) or (cmap[v] is not None and cmap[v]!=b):
                    valid=False;break
                rmap[u]=a;cmap[v]=b
            if valid and len(set(rmap))==k and len(set(cmap))==l:
                fibers[(tuple(rmap),tuple(cmap))]+=1
        aut,L,ncomponents,nedge=direct.statistics(key)
        assert len(fibers)==aut
        assert all(v==kernel for v in fibers.values())
        leaf_lifts=sum(v for (rmap,cmap),v in fibers.items() if leaf_action(rmap,cmap,edges))
        assert leaf_lifts==L*kernel
        cosets_total+=len(fibers);leaf_lifts_total+=leaf_lifts
        giant=max(sizes,default=0)
        if giant>n/2:fragments[n-giant]+=1
        else:no_giant+=1
    if n:
        expected={j:direct.A[j]*direct.C[n-j] for j in range((n-1)//2+1)}
        assert dict(fragments)==expected,(n,fragments,expected)
        assert len(graphs)==no_giant+sum(expected.values())
    rows.append(dict(n=n,graphs=len(graphs),no_giant=no_giant,fragment_counts=dict(sorted(fragments.items())),vertex_cosets=cosets_total,leaf_lifts=leaf_lifts_total))
result=dict(status='PASS',maximum_n=6,graph_types=types,edge_permutations_checked=permutations_checked,rows=rows,method='Enumerate edge stabilizers independently, map every stabilizer element to its vertex action, check uniform parallel-edge-kernel fibers and marked leaf fibers; directly compute all component edge sizes.')
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS',types,'graph types;',permutations_checked,'edge permutations; kernel cosets, leaf lifts, unique giant and all fragment-size counts')

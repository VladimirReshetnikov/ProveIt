"""Bounded literal source-cell-cover audit, not an encoded-input recognition path."""
from collections import Counter
from .normalize import raw_components,shifted

def source_cell_cover(nf,n=5):
    if type(n)is not int or not 3<=n<=12:raise ValueError('literal audit cap')
    u=nf.source;th=set(nf.through)
    ls={nf.labels[v] for v in u.left};rs={nf.labels[v] for v in u.right}
    pieces=[raw_components(u,nf.groups,th,0),raw_components(u,nf.groups,th,n-1),
            raw_components(u,nf.groups,ls-th,0),raw_components(u,nf.groups,rs-th,n-1)]
    pieces += [z.raw for z in nf.seams if z.kind in ('L','B')]
    pieces += [shifted(z.raw,n-2) for z in nf.seams if z.kind=='R']
    pieces += [shifted(nf.raw_templates[a],j) for j in range(1,n-1) for a in nf.through]
    floating=set(range(len(nf.groups)))-ls-rs
    pieces += [raw_components(u,nf.groups,floating,j) for j in range(n)]
    pieces += [shifted(z.raw,j) for j in range(n-1) for z in nf.seams if z.kind=='F']
    edges=Counter();eq=Counter();nodes=set()
    for p in pieces:
        edges.update(p.edges);eq.update(p.pairs);nodes.update(p.nodes)
    expected_edges=Counter((j,e) for j in range(n) for e in range(len(u.edges)))
    expected_eq=Counter(((j,a),(j+1,b)) for j in range(n-1) for a,b in zip(u.right,u.left))
    expected_nodes={(j,v) for j in range(n) for v in range(u.n)}
    return dict(valid=edges==expected_edges and eq==expected_eq and nodes==expected_nodes,
                edges=len(expected_edges),equalities=len(expected_eq),vertices=len(expected_nodes))

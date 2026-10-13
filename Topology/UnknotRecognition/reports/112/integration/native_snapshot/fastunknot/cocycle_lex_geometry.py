"""Trusted source geometry for Euler-edge/span lexicographic optimization."""
from collections import Counter
from itertools import combinations
from .integer_codec import encoded_integer
from .normal_surface_geometry import _EDGES,_edge,NormalOrbitError


def edge_model(prepared, heights, check):
    vertices=[prepared['vertex_roots'][4*t:4*t+4] for t in range(len(prepared['tetrahedra']))]
    if type(heights) is not list or len(heights)!=len(vertices):
        raise NormalOrbitError('four integral heights per tetrahedron are required')
    h=[]
    for row in heights:
        check()
        if type(row) is not list or len(row)!=4:
            raise NormalOrbitError('four integral heights per tetrahedron are required')
        try:h.append([encoded_integer(x) for x in row])
        except ValueError as exc:raise NormalOrbitError('invalid integral height') from exc
    labels=sorted(set(prepared['vertex_roots']));index={v:i for i,v in enumerate(labels)}
    global_edges={}
    for t,row in enumerate(h):
        for j,(a,b) in enumerate(_EDGES):
            check()
            u,v,c=vertices[t][a],vertices[t][b],row[b]-row[a]
            if prepared['edge_orientations'][6*t+j]:u,v,c=v,u,-c
            root=prepared['edge_roots'][6*t+j]
            if root in global_edges and global_edges[root]!=(u,v,c):
                raise NormalOrbitError('heights do not define one global cocycle')
            global_edges[root]=u,v,c
    degree=Counter()
    for t,f in prepared['boundary_faces']+[(t,f) for t,f,u,g,p in prepared['pairs']]:
        check()
        for a,b in combinations([v for v in range(4) if v!=f],2):
            degree[prepared['edge_roots'][_edge(t,a,b)]]+=1
    edges=[]
    for root,(a,b,c) in sorted(global_edges.items()):
        check()
        if degree[root]<2:raise NormalOrbitError('Euler edge penalty has negative weight')
        edges.append([index[a],index[b],c,degree[root]-2])
    return labels,[[index[v] for v in row] for row in vertices],h,edges


def span_network(vertices, heights, edges, flows, potential, check):
    """The complete verified primary optimum face and span epigraph."""
    n=len(potential);constraints=[];objective=[];initial=list(potential)
    for (a,b,c,w),raw_flow in zip(edges,flows):
        check();f=encoded_integer(raw_flow)
        if not w:continue
        if f<w:constraints.append([a,b,-c])
        if f>-w:constraints.append([b,a,c])
    for t,(vs,hs) in enumerate(zip(vertices,heights)):
        check();upper,lower=n+2*t,n+2*t+1
        values=[z+potential[v] for v,z in zip(vs,hs)]
        initial.extend([max(values),min(values)])
        objective.append([lower,upper,0,1])
        for v,z in zip(vs,hs):constraints.extend([[upper,v,-z],[v,lower,z]])
    return objective,constraints,initial


def span_value(vertices,heights,potential,check):
    total=0
    for vs,hs in zip(vertices,heights):
        check();values=[z+potential[v] for v,z in zip(vs,hs)]
        total+=max(values)-min(values)
    return total

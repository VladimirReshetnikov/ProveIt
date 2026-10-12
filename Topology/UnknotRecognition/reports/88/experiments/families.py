from cycle_kernel import Graph

def permuted_prisms(cycle_lengths):
    r=sum(cycle_lengths);pi=list(range(r));start=0
    for ell in cycle_lengths:
        for j in range(ell):pi[start+j]=start+(j+1)%ell
        start+=ell
    edges=[];w=2*r
    for a,b in enumerate(pi):
        edges.extend([(2*a,w+2*b),(2*a+1,w+2*b+1),(w+2*b,w+2*b+1)])
    return Graph(2*w,tuple(edges),tuple(range(w)),tuple(range(w,2*w)))

def cap_prism():
    # One through prism brick and a cap/cup pair. Every closed power is cubic.
    return Graph(8,((0,4),(1,5),(4,5),(2,3),(6,7),(6,7)),(0,1,2,3),(4,5,6,7))

from pattern_kernel.core import Tile


def star_triangle():
    """Aligned partitions {0},{1,2}; one closure is the tetrahedron graph."""
    return Tile(7, ((0,6),(4,6),(5,6),(1,2),(2,3),(3,1)),
                (0,1,2), (3,4,5))


def connected_context():
    """Degree-preserving two-switch connects the star/triangle source tile."""
    return Tile(7, ((0,1),(4,6),(5,6),(6,2),(2,3),(3,1)),
                (0,1,2), (3,4,5))


def routed_edges(permutation):
    w = len(permutation)
    return Tile(2*w, tuple((i, w+permutation[i]) for i in range(w)),
                tuple(range(w)), tuple(range(w,2*w)))


def routed_beads(permutation):
    """Two-terminal cubic pieces with input degree one/output degree two."""
    w = len(permutation)
    local_edges = ((0,2),(1,3),(1,4),(2,3),(2,4),(3,4))
    edges = tuple((5*i+a,5*i+b) for i in range(w) for a,b in local_edges)
    left = tuple(5*i for i in range(w))
    right = [None]*w
    for i,j in enumerate(permutation):
        right[j] = 5*i+1
    return Tile(5*w, edges, left, tuple(right))


def permutation_cycles(lengths):
    result = []
    for h in lengths:
        start = len(result)
        result.extend(start+(i+1)%h for i in range(h))
    return result

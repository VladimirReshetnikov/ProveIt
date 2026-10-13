"""Documented abstract families, plus one reconstructed maintained source matrix."""
from activation_forest import Instance


def repository_loop():
    return Instance(2, ((0,1),(0,1),(0,1),(0,1),(1,1)),
                    ((0,0,1,0,0),(1,1,0,0,0),(0,1,0,1,1),(1,0,1,1,1),(0,1,1,1,0)),5)


def parallel_obstruction(m):
    if m < 3:
        raise ValueError('obstruction family needs at least three rows')
    return Instance(2, ((0,1),)*m, ((1,),)*m,1)


def generic_positive():
    return Instance(4, ((0,1),(1,2),(2,3),(3,0)), ((1,),(1,),(1,),(0,)),1)


def generic_negative():
    return Instance(3, ((0,1),(1,2),(0,2),(0,1)), ((1,),(1,),(1,),(0,)),1)


def choice_arms(g):
    """Two good alternatives and one bad edge per arm; no geometric realization claim.

    Every successful tree chooses a good edge on every arm. A loop row is activated only after every good row disappears. One higher-support
    column has all good rows as nonunit prerequisites. Exact counts satisfy dual-cycle parity.
    """
    if g < 1:
        raise ValueError('positive arm count required')
    m, c = 3*g+1, 2*g+1
    edges = tuple((0,i+1) for i in range(g) for _ in range(3)) + ((0,0),)
    rows = [[0]*c for _ in range(m)]
    for i in range(g):
        bad, a, b = 3*i, 3*i+1, 3*i+2
        rows[a][2*i] = rows[b][2*i] = 1
        rows[bad][2*i+1], rows[a][2*i+1] = 1, 3
        rows[a][-1] = rows[b][-1] = 2
    rows[-1][-1] = 1
    return Instance(g+1, edges, tuple(tuple(row) for row in rows), c)


def random_instance(rng, max_m=8):
    v = rng.randrange(1, min(5,max_m+1)+1)
    edges = [(rng.randrange(i),i) for i in range(1,v)]
    m = rng.randrange(len(edges), max_m+1)
    edges.extend((rng.randrange(v),rng.randrange(v)) for _ in range(m-len(edges)))
    c = rng.randrange(0,6)
    rows = tuple(tuple(rng.choice((0,0,0,1,1,2)) for _ in range(c)) for _ in range(m))
    return Instance(v, tuple(edges), rows, c)

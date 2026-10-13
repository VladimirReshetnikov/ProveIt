"""Explicit matrix families, not asserted to be native normal-cut exports."""

def complete_blocks(q, size=3, bridges=True):
    a = {r: {size*b+c: 1 for c in range(size)}
         for b in range(q) for r in range(size*b, size*(b+1))}
    if bridges:
        for b in range(q-1):
            c = size*q+b
            a[size*b+size-1][c] = 1
            a[size*(b+1)][c] = 1
    return a


def ball_blocks(q):
    # Matrix of the predecessor's geometric family; not a native cut fixture.
    return {2*i: {2*i: 1, 2*i+1: 1} for i in range(q)} | {
        2*i+1: {2*i: 1, 2*i+1: 2} for i in range(q)}


def one_column(n):
    return {r: {0: 1} for r in range(n)}


def triangular(n):
    return {r: {r: 1, **({r+1: 2} if r+1<n else {})} for r in range(n)}


def random_local(n, seed=0):
    import random
    rng = random.Random(seed)
    return {r: {c: rng.choice((1,1,2)) for c in range(max(0,r-2),min(n,r+3))
                if rng.random()<0.7} for r in range(n)}


def complete_chain_decomposition(q):
    """Width-three decomposition of complete_blocks(q), with its dense labels."""
    from ordered_kernel.decomposition import Decomposition
    if type(q) is not int or q < 1:
        raise ValueError('q must be positive')
    bags=[]; parent=[]
    for i in range(q):
        rows=tuple(range(3*i,3*i+3))
        for c in range(3*i,3*i+3):
            bags.append(rows+(3*q+c,))
            parent.append(3*i if c!=3*i else (None if i==0 else 3*q+i-1))
    for i in range(q-1):
        bags.append((3*i+2, 6*q+i, 3*i+3))
        parent.append(3*i)
    return Decomposition(bags,parent)


def source_scc_fan(q):
    a=ball_blocks(q);sink=2*q;a[sink]={}
    for i in range(q):
        c=2*q+i;a[2*i][c]=2;a[sink][c]=1
    return a

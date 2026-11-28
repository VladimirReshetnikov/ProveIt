"""Verify Ehrhart numerators by rational polytope inequalities. Standard library only."""
from functools import lru_cache
from itertools import combinations
from math import comb


def cycle(n):
    return {tuple(sorted((i, (i+1) % n))) for i in range(n)}


def vectors(n, budget, cap):
    if n == 0:
        yield ()
    else:
        for u in range(min(budget,cap)+1):
            for tail in vectors(n-1,budget-u,cap):
                yield (u,) + tail


def fractions(n, edges):
    """Twice the relevant half-integral fractional stable-set vectors."""
    normals = set()
    for subset in range(1 << n):
        ones = {i for i in range(n) if subset & (1 << i)}
        if any(a in ones and b in ones for a,b in edges):
            continue
        zero = ({b for a,b in edges if a in ones}
                | {a for a,b in edges if b in ones})
        normals.add(tuple(2 if i in ones else 0 if i in zero else 1 for i in range(n)))
    return [v for v in normals
            if not any(w != v and all(x <= y for x,y in zip(v,w)) for w in normals)]


def path_indep(weights):
    last, current = 0, 0
    for x in weights:
        last, current = current, max(current, last+x)
    return current


def hstar(n, edges, top, is_cycle=False):
    normals = [] if is_cycle else fractions(n, edges)
    counts = []
    for k in range(top+1):
        tally = 0
        for x in vectors(n,2*k,k):
            if is_cycle:
                inside = max(path_indep(x[1:]), x[0]+path_indep(x[2:-1])) <= k
            else:
                inside = all(sum(a*b for a,b in zip(w,x)) <= 2*k for w in normals)
            tally += inside
        counts.append(tally)
    return [sum((-1)**j*comb(n+1,j)*counts[i-j] for j in range(i+1))
            for i in range(top+1)]


def pms(n, edges):
    @lru_cache(None)
    def match(mask):
        if not mask:
            return True
        bit = mask & -mask
        u = bit.bit_length()-1
        return any(mask & (1 << v) and tuple(sorted((u,v))) in edges and
                   match(mask ^ bit ^ (1 << v)) for v in range(n) if v != u)
    return [sum(match(sum(1 << v for v in choice)) for choice in combinations(range(n),2*j))
            for j in range(n//2+1)]


def main():
    for n in range(4,11):
        edges = cycle(n)
        top = (n+1)//2
        p = pms(n,edges)
        if n % 2:
            p.append(1)
        actual = hstar(n,edges,top,True)
        assert actual == p
        print(f"C{n}: {actual}")
    # Three internally disjoint paths of lengths 2, 3 and 3 between 0 and 1.
    edges = {(0,2),(1,2),(0,3),(3,4),(1,4),(0,5),(5,6),(1,6)}
    actual = hstar(7,edges,3)
    diff = [x-y for x,y in zip(actual,pms(7,edges))]
    assert diff == [0,0,0,2]
    print("Theta graph with path lengths 2,3,3: h* - p through degree 3 =", diff)
    # A graph with one 5-cycle and a leaf on each of two adjacent vertices.
    edges = cycle(5) | {(0,5),(1,6)}
    diff = [x-y for x,y in zip(hstar(7,edges,3),pms(7,edges))]
    assert diff == [0,0,0,1]
    print("5-cycle with two attached leaves: h* - p through degree 3 =", diff)


if __name__ == '__main__':
    main()

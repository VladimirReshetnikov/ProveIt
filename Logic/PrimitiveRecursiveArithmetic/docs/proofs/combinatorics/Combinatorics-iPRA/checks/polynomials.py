"""Compare three independent evaluations on every simple graph with four vertices or fewer."""
from itertools import combinations, product
from math import prod


def components(n, edges):
    label = list(range(n))
    for i,j in edges:
        before, after = label[j], label[i]
        label = [after if t == before else t for t in label]
    return len(set(label))


def audit(n, all_edges):
    for mask in range(2**len(all_edges)):
        edges = [e for k,e in enumerate(all_edges) if mask >> k & 1]
        subgraphs = [[e for k,e in enumerate(edges) if m >> k & 1] for m in range(2**len(edges))]
        counts = [(len(A),components(n,A)) for A in subgraphs]
        kE = components(n,edges)
        def tutte(x,y):
            return sum((x-1)**(k-kE)*(y-1)**(e-n+k) for e,k in counts)
        assert tutte(2,2) == len(subgraphs)
        for q in range(4):
            for v in (-1,0,2):
                by_spins = sum(prod(1+v*(s[i] == s[j]) for i,j in edges) for s in product(range(q),repeat=n))
                by_subsets = sum(q**k*v**e for e,k in counts)
                assert by_spins == by_subsets
                if v == -1:
                    assert by_spins == (-1)**(n-kE)*q**kE*tutte(1-q,0)
        for x,y in product(range(4), repeat=2):
            assert sum(((x-1)*(y-1))**k*(y-1)**e for e,k in counts) == (x-1)**kE*(y-1)**n*tutte(x,y)


if __name__ == '__main__':
    for n in range(5):
        audit(n, list(combinations(range(n),2)))
    audit(3, [(0,0),(0,1),(0,1),(1,2)])
    print('PASS: Potts, chromatic and Tutte expansions through four vertices, and a multigraph with loop and parallel edges.')

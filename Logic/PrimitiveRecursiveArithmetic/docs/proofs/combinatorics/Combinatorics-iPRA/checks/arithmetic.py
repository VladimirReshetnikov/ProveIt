"""Finite audits of the additive, word, necklace and Markov constructions."""
from itertools import combinations, combinations_with_replacement, product
from math import gcd, prod


def prime(n):
    return n >= 2 and all(n % d for d in range(2, n))


def egz(values, n):
    """Return original position indices from the inductive proof."""
    assert len(values) == 2 * n - 1
    if n == 1:
        return [0]
    if prime(n):
        perm = sorted(range(len(values)), key=lambda i: values[i] % n)
        for i in range(n):
            if values[perm[i]] % n == values[perm[i+n-1]] % n:
                return perm[i:i+n]
        paths = {0: []}
        for i in range(n-1):
            extended = {}
            for r, path in paths.items():
                for j in (perm[i], perm[i+n-1]):
                    extended.setdefault((r + values[j]) % n, path + [j])
            paths = extended
        return paths[-values[perm[-1]] % n] + [perm[-1]]
    a = next(d for d in range(2, n) if n % d == 0)
    b = n // a
    unused = list(range(len(values)))
    blocks = []
    for _ in range(2*b-1):
        picked = egz([values[i] for i in unused[:2*a-1]], a)
        block = [unused[i] for i in picked]
        blocks.append(block)
        unused = [i for i in unused if i not in block]
    selected = egz([sum(values[i] for i in block)//a for block in blocks], b)
    return [i for j in selected for i in blocks[j]]


def sumsets():
    for p in (2, 3, 5, 7):
        subs = [set(comb) for k in range(1,p+1) for comb in combinations(range(p), k)]
        for a in subs:
            for b in subs:
                assert len({(x+y)%p for x in a for y in b}) >= min(p,len(a)+len(b)-1)
            if len(a) >= 2:
                assert len({(x+y)%p for x,y in combinations(a,2)}) >= min(p,2*len(a)-3)
    for n in range(1, 10):
        if n <= 5:
            cases = combinations_with_replacement(range(n), 2*n-1)
        else:
            cases = ([(i*i*u+i*v+u*v) % (5*n) - 2*n for i in range(2*n-1)]
                     for u in range(n) for v in range(n))
        for values in cases:
            indices = egz(values, n)
            assert len(set(indices)) == len(indices) == n
            assert all(0 <= i < len(values) for i in indices)
            assert sum(values[i] for i in indices) % n == 0


def words_and_necklaces():
    for m in range(9):
        for j in range(m):
            assert sum((-1)**(x.bit_count()%2)*x**j for x in range(2**m)) == 0
    for n in range(11):
        for w in product(range(2), repeat=n):
            periods = [p for p in range(1,n+2) if w[:max(0,n-p)] == w[p:]]
            for p,q in product(periods, repeat=2):
                if n >= p+q-gcd(p,q):
                    assert gcd(p,q) in periods
            if n%2 == 0 and sum(w)%2 == 0:
                assert any(2*sum(w[i:i+n//2]) == sum(w) for i in range(n//2+1))


def tree_weights(W):
    n = len(W)
    totals = []
    for r in range(n):
        others = [i for i in range(n) if i != r]
        total = 0
        for heads in product(range(n), repeat=n-1):
            parent = dict(zip(others, heads))
            for start in others:
                x = start
                for _ in range(n):
                    x = parent.get(x, r)
                if x != r:
                    break
            else:
                total += prod(W[i][parent[i]] for i in others)
        totals.append(total)
    return totals


def markov():
    for n,D in ((1,1),(2,4),(3,2)):
        rows = [v for v in product(range(D+1),repeat=n) if sum(v) == D]
        for W in product(rows,repeat=n):
            T = tree_weights(W)
            assert all(sum(T[i]*W[i][j] for i in range(n)) == D*T[j] for j in range(n))
            s = sum(min(row[j] for row in W) for j in range(n))
            if s:
                assert sum(T) > 0
            for r,t in combinations(range(n),2):
                assert sum(abs(a-b) for a,b in zip(W[r],W[t])) <= 2*(D-s)


if __name__ == '__main__':
    sumsets(); words_and_necklaces(); markov()
    print('PASS: prime sumsets and restricted sums, EGZ selectors, Fine-Wilf, Prouhet, two-cut necklaces, stationary tree weights and contraction.')

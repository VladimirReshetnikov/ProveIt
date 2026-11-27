"""Exact finite-law checks. Run python3 verify.py (standard library only)."""
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import product
from math import prod


def rank_mod(rows, q):
    rows = [list(row) for row in rows]
    rank = 0
    for col in range(len(rows[0]) if rows else 0):
        pivot = next((i for i in range(rank, len(rows)) if rows[i][col] % q), None)
        if pivot is None:
            continue
        rows[pivot], rows[rank] = rows[rank], rows[pivot]
        lead = pow(rows[rank][col] % q, -1, q)
        for row in rows[rank + 1:]:
            factor = row[col] * lead
            for k in range(col, len(row)):
                row[k] = (row[k] - factor * rows[rank][k]) % q
        rank += 1
    return rank


@lru_cache(None)
def choose(q, n, k):
    if k < 0 or k > n:
        return 0
    return prod(q**n - q**i for i in range(k)) // prod(q**k - q**i for i in range(k))


@lru_cache(None)
def embeddings(q, N, v, s):
    r = v - 2*s
    if r < 0 or s+r > N:
        return 0
    return (prod((q**(2*(N-i))-1)*q**(2*(N-i)-1) for i in range(s)) *
            prod(q**(2*(N-s)-i)-q**i for i in range(r)))


def probability(q, N, H, J, M):
    a, b = len(H), len(J)
    top = [list(H[i]) + [-M[j][i] for j in range(b)] for i in range(a)]
    bottom = [list(M[j]) + list(J[j]) for j in range(b)]
    C = top + bottom
    s = rank_mod(C, q)//2
    h = a+b-2*s
    p = a-rank_mod([row[:a] for row in C], q)
    t = b-rank_mod([row[a:] for row in C], q)
    u = h-p-t
    total = 0
    for e in range(min(p,t)+1):
        graphs = choose(q,p,e)*choose(q,t,e)*prod(q**e-q**i for i in range(e))
        for k in range(u+1):
            kernels = graphs*choose(q,u,k)*q**(k*(p+t-e))
            total += kernels*embeddings(q,N,a+b-e-k,s)
    assert (total > 0) == (s+max(p,t) <= N)
    den = embeddings(q,N,a,rank_mod(H,q)//2)*embeddings(q,N,b,rank_mod(J,q)//2)
    return Fraction(total, den)


def omega(x, y, q):
    return sum(x[i]*y[i+1]-x[i+1]*y[i] for i in range(0,len(x),2)) % q


def gram(X,Y,q):
    return tuple(tuple(omega(x,y,q) for y in Y) for x in X)


def representative(N, v, s):
    columns = list(range(2*s)) + [2*s+2*i for i in range(v-2*s)]
    return tuple(tuple(int(i == j) for j in range(2*N)) for i in columns)


def check(q, N, a, source_rank, b, target_rank):
    X0 = representative(N,a,source_rank//2)
    B = representative(N,b,target_rank//2)
    H, J = gram(X0,X0,q), gram(B,B,q)
    vectors = list(product(range(q), repeat=2*N))
    counts = Counter()
    for X in product(vectors, repeat=a):
        if gram(X,X,q) == H and rank_mod(X,q) == a:
            counts[gram(B,X,q)] += 1
    n = sum(counts.values())
    assert n == embeddings(q,N,a,source_rank//2)
    for batch in product(range(q), repeat=b*a):
        M = tuple(tuple(batch[i*a:(i+1)*a]) for i in range(b))
        assert probability(q,N,H,J,M) == Fraction(counts[M],n), (q,N,M)
    print(f"q={q}  dim={2*N}  source=({a},{source_rank})  target=({b},{target_rank})"
          f"  frames={n}  supported={len(counts)}/{q**(a*b)}  PASS")


if __name__ == "__main__":
    # (field size, ambient half-dimension, source dimension/rank, target dimension/rank)
    for case in [(2,2,2,2,2,2),(3,2,2,2,2,2),(2,2,2,0,2,0),
                 (2,2,2,0,3,2),(2,2,3,2,3,2),(3,1,1,0,2,2),
                 (2,2,4,4,2,0),(2,3,2,0,3,2)]:
        check(*case)

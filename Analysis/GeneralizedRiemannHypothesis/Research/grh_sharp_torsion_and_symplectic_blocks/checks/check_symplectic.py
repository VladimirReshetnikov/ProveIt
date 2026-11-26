"""Exact checks of the symplectic compression formulas over small prime fields."""

from collections import Counter
from fractions import Fraction
from itertools import product
from math import prod


def gaussian(n, i, q):
    numerator = prod(q**n - q**j for j in range(i))
    denominator = prod(q**i - q**j for j in range(i))
    return numerator // denominator


def predicted_full_row_rank(m, c, q):
    return sum(
        Fraction((-1)**i * q**(i*(i-1)//2) * gaussian(m-c, i, q),
                 prod(q**k + 1 for k in range(m-i+1, m+1)))
        for i in range(m-c+1)
    )


def dot_mod(a, b, q):
    return sum(x*y for x, y in zip(a, b)) % q


def rank(rows, q):
    pivot_rows = {}
    for vector in rows:
        work = list(vector)
        for i in sorted(pivot_rows):
            scale = work[i]
            if scale:
                work = [(x-scale*y) % q for x, y in zip(work, pivot_rows[i])]
        i = next((j for j, x in enumerate(work) if x), None)
        if i is not None:
            scale = pow(work[i], -1, q)
            pivot_rows[i] = tuple(scale*x % q for x in work)
    return len(pivot_rows)


def independent_isotropic_frames(m, a, q):
    """Enumerate ordered independent isotropic a-frames, each once."""
    n = 2*m
    vectors = list(product(range(q), repeat=n))
    duals = {v: tuple((-x) % q for x in v[m:]) + v[:m] for v in vectors}
    orth = {
        v: [w for w in vectors if dot_mod(duals[v], w, q) == 0]
        for v in vectors
    }

    def visit(prefix, candidates, span):
        if len(prefix) == a:
            yield prefix
            return
        for v in candidates:
            if v in span:
                continue
            if len(prefix) + 1 == a:
                yield prefix + (v,)
                continue
            new_span = {
                tuple((x+t*y) % q for x, y in zip(s, v))
                for s in span for t in range(q)
            }
            allowed = set(orth[v])
            yield from visit(prefix+(v,), [w for w in candidates if w in allowed], new_span)

    yield from visit((), vectors, {vectors[0]})


def check_case(m, a, b, q):
    """Witt extension makes the enumerated frames equiprobable under uniform g."""
    counts = Counter()
    for frame in independent_isotropic_frames(m, a, q):
        block = tuple(tuple(v[m+i] for v in frame) for i in range(b))
        counts[block] += 1
    total = sum(counts.values())
    expected_orbit = prod(q**(2*m-i) - q**i for i in range(a))
    assert total == expected_orbit
    n_matrices = q**(a*b)
    full = Fraction(sum(count for block, count in counts.items() if rank(block, q) == b), total)
    tv = (sum(abs(Fraction(count, total) - Fraction(1, n_matrices))
              for count in counts.values()) + Fraction(n_matrices-len(counts), n_matrices))/2
    if a == m:
        assert full == predicted_full_row_rank(m, m-b, q)
        by_deficiency = Counter()
        mass_per_block = {}
        for block, count in counts.items():
            d = b-rank(block, q)
            by_deficiency[d] += count
            assert count == mass_per_block.setdefault(d, count)
        assert len(counts) == n_matrices
        rank_tv = Fraction(0)
        for d in range(b+1):
            qbin = gaussian(b, d, q)
            symplectic_d = (Fraction(qbin, prod(1+q**j for j in range(m-d+1, m+1)))
                            * predicted_full_row_rank(m-d, m-b, q))
            uniform_d = (Fraction(qbin, q**(m*d))
                         * prod(1-Fraction(1,q**j) for j in range(m-b+d+1, m+1)))
            assert Fraction(by_deficiency[d], total) == symplectic_d
            rank_tv += abs(symplectic_d-uniform_d)/2
        assert rank_tv == tv
    if a == b == m:
        assert full == prod(Fraction(q**k, q**k+1) for k in range(1, m+1))
    # Every frame tested here spans an isotropic subspace; the exact stabilizer
    # probabilities for both sides are reciprocals of their isotropic orbit sizes.
    square_bound = Fraction(0)
    for j in range(1, min(a,b)+1):
        orbit = prod(q**(2*m-i)-q**i for i in range(j))
        rank_count = gaussian(a,j,q)*prod(q**b-q**i for i in range(j))
        square_bound += Fraction(rank_count*q**(2*m*j), 4*orbit**2)
    assert tv**2 <= square_bound
    uniform_full = prod(1-Fraction(1, q**(a-i)) for i in range(b))
    assert tv >= abs(full-uniform_full)
    print(f"q={q}, n={2*m}, a={a}, b={b}: {total} frames, "
          f"P(full)={full}, P_uniform(full)={uniform_full}, TV={tv}")


if __name__ == "__main__":
    for parameters in [(1,1,1,2), (2,2,2,2), (2,2,1,2), (2,2,2,3),
                       (2,2,1,3), (3,3,3,2), (3,3,2,2), (3,3,1,2),
                       (3,2,2,2)]:
        check_case(*parameters)

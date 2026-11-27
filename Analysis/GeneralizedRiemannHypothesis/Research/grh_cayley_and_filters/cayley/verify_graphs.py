#!/usr/bin/env python3
"""Exhaust all oriented Cayley connection sets for the finite groups listed below.

No nonintegral arithmetic occurs: a primitive N-th root is the residue class
of X modulo the monic cyclotomic polynomial Phi_N(X). Each inverse pair is
absent or takes either orientation, and involutions are forced to zero.
"""
from functools import lru_cache
from itertools import product
from math import gcd, isqrt, lcm
import json


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def phi(n):
    return sum(gcd(k, n) == 1 for k in range(1, n + 1))


def squarefree(n):
    return all(n % (p*p) for p in range(2, isqrt(n) + 1))


def fundamental_negative(f):
    d = -f
    if d % 4 == 1:
        return squarefree(f)
    return d % 4 == 0 and (d//4) % 4 in (2, 3) and squarefree(f//4)


def kronecker(d, n):
    if n == 0:
        return int(abs(d) == 1)
    value = 1
    while n % 2 == 0:
        n //= 2
        if d % 2 == 0:
            return 0
        if d % 8 in (3, 5):
            value = -value
    a = d % n
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5):
                value = -value
        if a % 4 == n % 4 == 3:
            value = -value
        a, n = n % a, a
    return value if n == 1 else 0


def monic_quotient(a, b):
    rem = a[:]
    quotient = [0] * (len(a) - len(b) + 1)
    for k in reversed(range(len(quotient))):
        c = rem[k + len(b) - 1]
        quotient[k] = c
        for j, coefficient in enumerate(b):
            rem[k + j] -= c * coefficient
    assert not any(rem)
    return quotient


@lru_cache(maxsize=None)
def cyclotomic(n):
    coeffs = [-1] + [0] * (n - 1) + [1]
    for d in divisors(n)[:-1]:
        coeffs = monic_quotient(coeffs, cyclotomic(d))
    return coeffs


def powers(N):
    modulus = cyclotomic(N)
    deg = len(modulus) - 1
    one = tuple([1] + [0] * (deg - 1))
    z = one
    out = []
    for _ in range(N):
        out.append(z)
        z = tuple(v - z[-1]*m for v, m in zip((0,) + z[:-1], modulus[:-1]))
    assert z == one
    return out


def fourier_row(terms, gauss):
    """Return linear tests for exact multiples of gauss, plus the multiple."""
    pivot = next(i for i, c in enumerate(gauss) if c)
    denom = gauss[pivot]
    first = [t[pivot] for t in terms]
    linear = []
    for j in range(len(gauss)):
        coeffs = [denom*t[j] - gauss[j]*c for t, c in zip(terms, first)]
        if any(coeffs):
            linear.append(coeffs)
    return first, denom, linear



def rank_one_periodic(connection, rows):
    """Purely rational rank <= 1 of all eigenvalues tests commensurability."""
    first = None
    for row in rows:
        spectrum = [sum(s*c for s,c in zip(connection, column)) for column in row]
        if not any(spectrum):
            continue
        if first is None:
            first = spectrum
            pivot = next(j for j,v in enumerate(first) if v)
        elif any(v*first[pivot] != spectrum[pivot]*a for v,a in zip(spectrum,first)):
            return False
    return first is not None

def check_group(moduli):
    N = lcm(*moduli)
    group = list(product(*(range(n) for n in moduli)))
    size = len(group)
    conductors = [f for f in divisors(N) if fundamental_negative(f)]
    reps = [x for x in group if x < tuple(-t % n for t, n in zip(x, moduli))]
    phases = {y: [sum(t*k*(N//n) for t, k, n in zip(x, y, moduli)) % N
                  for x in reps] for y in group}
    order = {y: lcm(*(n//gcd(n, k) for n, k in zip(moduli, y))) for y in group}
    roots = powers(N)
    differences = [tuple(a-b for a,b in zip(roots[j], roots[-j % N])) for j in range(N)]
    results = []
    enumerations = 3**len(reps)
    # Involutions and inverse-dual representatives have zero or redundant rows.
    chars = sorted(reps, key=order.get, reverse=True)
    orientations = list(product((-1, 0, 1), repeat=len(reps)))
    for f in conductors:
        gauss = [sum(kronecker(-f,j)*roots[j*(N//f)][i] for j in range(f))
                 for i in range(len(roots[0]))]
        rows = [fourier_row([differences[j] for j in phases[y]], gauss) for y in chars]
        # Precompute a collision-free integer encoding of the finitely many
        # exact linear rationality equations for faster exhaustive evaluation.
        linear = sorted(set(tuple(z) for _, _, equations in rows for z in equations))
        radix = 2 * max([sum(map(abs, z)) for z in linear] + [1]) + 1
        fingerprint = [sum(z[j]*radix**i for i,z in enumerate(linear))
                       for j in range(len(reps))]
        top = size//f
        fastest_expected = set()
        for y in group:
            m = order[y]
            if m != f and not (f % 2 and m == 2*f):
                continue
            signs = []
            for phase in phases[y]:
                assert (m*phase) % N == 0
                j = m*phase//N
                val = kronecker(-f, j)
                signs.append(-val if m == 2*f and j % 2 else val)
            fastest_expected.add(tuple(signs))
            fastest_expected.add(tuple(-s for s in signs))
        observed = {}
        minimum = {}
        fastest_actual = set()
        for connection in orientations:
            if not any(connection):
                continue
            if sum(x*c for x,c in zip(connection,fingerprint)):
                continue
            spacing = 0
            for coeffs, denom, _ in rows:
                v = sum(x*c for x,c in zip(connection,coeffs))
                if v % denom:
                    spacing = 0
                    break
                spacing = gcd(spacing, v//denom)
            if not spacing:
                continue
            observed[spacing] = observed.get(spacing, 0) + 1
            degree = sum(abs(s) for s in connection)
            minimum[spacing] = min(minimum.get(spacing, size), degree)
            if spacing == top:
                fastest_actual.add(connection)
        assert sorted(observed) == divisors(top), (moduli,f,observed)
        assert all(2*deg == a*phi(f) for a,deg in minimum.items())
        counts = sum(1 for m in order.values() if m == f)//phi(f)
        if f % 2:
            counts += sum(1 for m in order.values() if m == 2*f)//phi(2*f)
        assert len(fastest_actual) == 2*counts
        assert fastest_actual == fastest_expected, (moduli,f,len(fastest_actual),len(fastest_expected))
        results.append({'f': f, 'graphs_by_exact_gcd': observed,
                        'min_outdegree_by_exact_gcd': minimum, 'fastest_fixed_field':len(fastest_actual)})
    direct_rows = [list(zip(*(differences[j] for j in phases[y]))) for y in chars]
    direct_count = sum(rank_one_periodic(connection,direct_rows) for connection in orientations if any(connection))
    assert direct_count == sum(sum(row['graphs_by_exact_gcd'].values()) for row in results)
    criterion = [4] if N % 4 == 0 else []
    criterion += [p for p in divisors(N) if p%4 == 3 and len(divisors(p))==2]
    assert min(conductors,default=None) == min(criterion,default=None)
    return {'group': moduli, 'size': size, 'exponent':N, 'inverse_pairs':len(reps),
            'all_oriented_connection_sets':enumerations, 'direct_rank_one_periodic':direct_count, 'fastest_f':min(conductors,default=None),
            'fields':results}


if __name__ == '__main__':
    groups = [(2,2,2),(3,),(4,),(5,),(6,),(7,),(8,),(9,),(11,),(12,),
              (15,),(16,),(18,),(20,),(21,),(24,),(2,4),(2,6),(3,3),(2,8),(2,12),
              (2,2,4),(3,6),(4,4)]
    results = [check_group(g) for g in groups]
    print(json.dumps({'checked_group_presentations':len(results),
                      'raw_group_connection_sets':sum(g['all_oriented_connection_sets'] for g in results),
                      'nontrivial_periodic_connection_sets':sum(g['direct_rank_one_periodic'] for g in results),
                      'conductor_group_cases':sum(len(g['fields']) for g in results),
                      'checked':results}, indent=2))

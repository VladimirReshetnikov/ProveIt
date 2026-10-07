#!/usr/bin/env python3
"""Exact finite regression checks for critical_phase_removal.tex.

Python >= 3.10 and NumPy are required. No network, CAS, random floating-point
optimizer, or proof-assistant results are used. Random cases have a fixed seed.
All pass/fail decisions use integers or Fraction, including the localization
moment checks. These finite checks are NOT proofs of the universal theorems.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, product
from math import comb, factorial, prod
from pathlib import Path
import json
import platform
import random
import time

try:
    import numpy as np
except ImportError as exc:
    raise SystemExit("Install the dependency with: python -m pip install numpy") from exc

SEED = 20261007


def require(condition: bool, message: str) -> None:
    """Do not use assert: checks must also run under python -O."""
    if not condition:
        raise RuntimeError(message)


@lru_cache(None)
def points(p: int, n: int) -> tuple[tuple[int, ...], ...]:
    return tuple(product(range(p), repeat=n))


@lru_cache(None)
def multiindices(n: int, degree: int) -> tuple[tuple[int, ...], ...]:
    if n == 1:
        return ((degree,),)
    return tuple((j,) + tail for j in range(degree + 1)
                 for tail in multiindices(n - 1, degree - j))


@lru_cache(None)
def difference_terms(alpha: tuple[int, ...]) -> tuple[tuple[tuple[int, ...], int], ...]:
    d = sum(alpha)
    return tuple((j, (-1) ** (d - sum(j)) * prod(comb(a, b) for a, b in zip(alpha, j)))
                 for j in product(*(range(a + 1) for a in alpha)))


def difference(values: dict[tuple[int, ...], int], p: int, modulus: int,
               x: tuple[int, ...], alpha: tuple[int, ...]) -> int:
    return sum(weight * values[tuple((u + v) % p for u, v in zip(x, j))]
               for j, weight in difference_terms(alpha)) % modulus


def frobenius_matrix(coeff: dict[tuple[int, ...], int], p: int, n: int) -> list[list[int]]:
    out = []
    for i in range(n):
        row = []
        for j in range(n):
            a = [0] * n
            a[i] += p
            a[j] += 1
            row.append(coeff[tuple(a)] % p)
        out.append(row)
    return out


def primitive(coeff: dict[tuple[int, ...], int], p: int, n: int
              ) -> tuple[dict[tuple[int, ...], int], int]:
    """Article's construction, with the COMPLETE low-depth symbol subtracted.

    Values are integer residues modulo modulus, representing value/modulus in R/Z.
    """
    d = p + 1
    F = frobenius_matrix(coeff, p, n)
    require(all(F[i][j] == F[j][i] for i in range(n) for j in range(n)),
            "primitive called on nonintegrable input")
    modulus = 8 if p == 2 else p * p
    values: dict[tuple[int, ...], int] = {}
    for x in points(p, n):
        if p == 2:
            num = sum(F[i][i] * x[i] for i in range(n))
            num += 2 * sum(F[i][j] * x[i] * x[j]
                           for i in range(n) for j in range(i + 1, n))
        else:
            inv2 = pow(2, -1, p)
            num = sum((-F[i][i] * inv2 % p) * x[i] ** 2 for i in range(n))
            num += sum((-F[i][j] % p) * x[i] * x[j]
                       for i in range(n) for j in range(i + 1, n))
        values[x] = num % modulus
    zero = (0,) * n
    residual: dict[tuple[int, ...], int] = {}
    for a in multiindices(n, d):
        top = difference(values, p, modulus, zero, a)
        require((top * p) % modulus == 0, "top value is not p-torsion")
        r = (coeff[a] - top * p // modulus) % p
        if max(a) >= p:
            require(r == 0, "repeated coefficient survived residual correction")
        elif r:
            residual[a] = r * pow(prod(factorial(j) for j in a) % p, -1, p) % p
    for x in points(p, n):
        correction = sum(c * prod(pow(u, a, p) for u, a in zip(x, alpha))
                         for alpha, c in residual.items()) % p
        values[x] = (values[x] + correction * (modulus // p)) % modulus
    return values, modulus


def check_primitive(coeff: dict[tuple[int, ...], int], p: int, n: int) -> int:
    values, modulus = primitive(coeff, p, n)
    d = p + 1
    checks = 0
    for x in points(p, n):
        for a in multiindices(n, d):
            require(difference(values, p, modulus, x, a) == coeff[a] * (modulus // p),
                    f"top symbol mismatch p={p}, n={n}, a={a}, x={x}")
            checks += 1
        for a in multiindices(n, d + 1):
            require(difference(values, p, modulus, x, a) == 0,
                    f"degree bound failed p={p}, n={n}, a={a}, x={x}")
            checks += 1
    return checks


def integration_checks(rng: random.Random) -> list[dict]:
    report = []
    for p, n, exhaustive in [(2, 2, True), (2, 3, True), (3, 2, True),
                              (3, 3, False), (5, 2, False)]:
        keys = multiindices(n, p + 1)
        total = tested = equations = 0
        if exhaustive:
            cases = product(range(p), repeat=len(keys))
        else:
            # Generate 40 coefficient vectors and enforce the linear F=F^t constraints.
            generated = []
            for _ in range(40):
                coeff = dict(zip(keys, (rng.randrange(p) for _ in keys)))
                for i in range(n):
                    for j in range(i + 1, n):
                        a = [0] * n
                        b = [0] * n
                        a[i], a[j] = p, 1
                        b[i], b[j] = 1, p
                        coeff[tuple(b)] = coeff[tuple(a)]
                generated.append(tuple(coeff[k] for k in keys))
            cases = generated
        for vector in cases:
            total += 1
            coeff = dict(zip(keys, vector))
            F = frobenius_matrix(coeff, p, n)
            if not all(F[i][j] == F[j][i] for i in range(n) for j in range(n)):
                continue
            tested += 1
            equations += check_primitive(coeff, p, n)
        if exhaustive:
            require(tested == p ** (len(keys) - comb(n, 2)), "integrable tensor census mismatch")
        report.append(dict(p=p, n=n, degree=p + 1, exhaustive=exhaustive,
                           coefficient_vectors_examined=total, primitives_checked=tested,
                           exact_difference_equations=equations,
                           checks="all top basis coefficients and all degree+1 basis differences at every base point"))
    return report


def matrix_rank(A: list[list[int]], p: int) -> int:
    A = [[v % p for v in row] for row in A]
    n = len(A)
    m = len(A[0]) if n else 0
    r = 0
    for j in range(m):
        pivot = next((i for i in range(r, n) if A[i][j]), None)
        if pivot is None:
            continue
        A[r], A[pivot] = A[pivot], A[r]
        inv = pow(A[r][j], -1, p)
        A[r] = [v * inv % p for v in A[r]]
        for i in range(n):
            if i != r and A[i][j]:
                a = A[i][j]
                A[i] = [(u - a * v) % p for u, v in zip(A[i], A[r])]
        r += 1
        if r == n:
            break
    return r


def gaussian(n: int, k: int, p: int) -> int:
    if k < 0 or k > n:
        return 0
    return prod(p ** (n - i) - 1 for i in range(k)) // prod(p ** (k - i) - 1 for i in range(k))


def symplectic_isotropic(r: int, k: int, p: int) -> int:
    if k < 0 or k > r:
        return 0
    return prod(p ** (2 * r - j) - p ** j for j in range(k)) // prod(p ** k - p ** j for j in range(k))


def isotropic_count(n: int, r: int, k: int, p: int) -> int:
    z = n - 2 * r
    return sum(gaussian(z, u, p) * symplectic_isotropic(r, k - u, p)
               * p ** ((k - u) * (z - u))
               for u in range(max(0, k - r), min(z, k) + 1))


def rref_subspaces(n: int, k: int, p: int):
    """Each k-dimensional subspace occurs exactly once, via its RREF basis."""
    for pivots in combinations(range(n), k):
        free = [(i, j) for i, pivot in enumerate(pivots)
                for j in range(pivot + 1, n) if j not in pivots]
        for vals in product(range(p), repeat=len(free)):
            A = [[0] * n for _ in range(k)]
            for i, pivot in enumerate(pivots):
                A[i][pivot] = 1
            for (i, j), v in zip(free, vals):
                A[i][j] = v
            yield A


def algebra_counts() -> list[dict]:
    report = []
    n = 4
    for p in (2, 3, 5):
        pairs = list(combinations(range(n), 2))
        ranks = Counter()
        for vals in product(range(p), repeat=len(pairs)):
            A = [[0] * n for _ in range(n)]
            for (i, j), v in zip(pairs, vals):
                A[i][j], A[j][i] = v, (-v) % p
            ranks[matrix_rank(A, p)] += 1
        expected_ranks = {
            2*r: gaussian(n, 2*r, p) * p ** (r * (r-1))
                 * prod(p ** (2*i-1) - 1 for i in range(1, r+1))
            for r in range(n//2+1)}
        require(dict(ranks) == expected_ranks, "alternating rank distribution failed")
        isotropic = {r: [] for r in range(n//2+1)}
        for k in range(n + 1):
            subspaces = list(rref_subspaces(n, k, p))
            require(len(subspaces) == gaussian(n, k, p), "RREF enumeration failed")
            for r in range(n//2+1):
                count = sum(all(sum(u[2*j] * v[2*j+1] - u[2*j+1] * v[2*j]
                                        for j in range(r)) % p == 0
                                    for u in H for v in H) for H in subspaces)
                require(count == isotropic_count(n, r, k, p), "isotropic subspace formula failed")
                isotropic[r].append(count)
        for r, counts in isotropic.items():
            require(max(k for k, c in enumerate(counts) if c) == n-r, "optimal repair dimension failed")
            require(counts[n-r] == prod(p ** i + 1 for i in range(1, r+1)), "maximal repair count failed")
        # Independent pair-query census on a 2-dimensional nonzero alternating block.
        failures = sum((x[0]*y[1]-x[1]*y[0]) % p != 0
                       for x in points(p, 2) for y in points(p, 2))
        require(Fraction(failures, p**4) == (1-Fraction(1,p))*(1-Fraction(1,p**2)),
                "rank-two pair-query failure law failed")
        report.append(dict(p=p, n=n, alternating_matrices=p ** comb(n, 2),
                           rank_distribution=dict(sorted(ranks.items())),
                           isotropic_subspaces_by_rank_half_and_dimension=isotropic,
                           rank_two_pair_query_failures=failures, rank_two_pair_query_total=p**4))
    return report


def cube_arrays(p: int, n: int, d: int):
    """Vectorized enumeration, but only exact integer arithmetic is used."""
    pts = np.asarray(points(p, n), dtype=np.int64)
    q = len(pts)
    ids = np.asarray(list(product(range(q), repeat=d+1)), dtype=np.int64)
    x = pts[ids[:, 0]]
    h = pts[ids[:, 1:]]
    vertices, signs = [], []
    weights = p ** np.arange(n-1, -1, -1, dtype=np.int64)
    for J in product((0,1), repeat=d):
        point = x.copy()
        for j, present in enumerate(J):
            if present:
                point += h[:,j]
        vertices.append(((point % p)*weights).sum(axis=1))
        signs.append((-1) ** (d-sum(J)))
    return np.stack(vertices, axis=1), np.asarray(signs, dtype=np.int64), h


def root_of_unity_energy(codes: np.ndarray, vertices: np.ndarray, signs: np.ndarray,
                        twist: np.ndarray | int = 0) -> Fraction:
    """Exact for p=3, with code -1 denoting zero and 0,1,2 denoting powers of omega."""
    values = codes[vertices]
    valid = np.all(values >= 0, axis=1)
    exp = (values @ signs - twist) % 3
    counts = np.bincount(exp[valid], minlength=3)
    require(int(counts[1]) == int(counts[2]), "cube energy unexpectedly non-real")
    out = Fraction(int(counts[0])-int(counts[1]), len(vertices))
    require(out >= 0, "cube energy unexpectedly negative")
    return out


def root_lower(x: Fraction, degree: int, bits: int = 72) -> Fraction:
    """Rational lower bound to x**(1/degree), certified by integer comparison."""
    require(0 <= x <= 1, "root input outside [0,1]")
    Q = 1 << bits
    lo, hi = 0, Q
    while lo < hi:
        mid = (lo + hi + 1)//2
        if mid ** degree * x.denominator <= x.numerator * Q ** degree:
            lo = mid
        else:
            hi = mid - 1
    bound = Fraction(lo, Q)
    require(bound ** degree <= x, "invalid lower-root certificate")
    return bound


def localization_checks(rng: random.Random) -> dict:
    p, n, d = 3, 2, 4
    vertices, signs, h = cube_arrays(p,n,d)
    # Canonical A_{a,b}: a=first coordinate, b=second coordinate.
    twist = sum(h[:,j,1] * np.prod(h[:,[i for i in range(d) if i != j],0],axis=1)
                for j in range(d)) % p
    hv, hs, _ = cube_arrays(p,1,d)
    # Check a nontrivial ninth-root gauge on every cube independently of the
    # energy summation. Its restriction to H is the critical primitive x^2/9.
    # The coset differences are lower-degree, nonclassical phases, not just
    # classical linear phases.
    gauge_values = {(x,y): (x*x+x*y) % 9 for x,y in points(3,2)}
    gauge_array = np.asarray([gauge_values[x] for x in points(3,2)],dtype=np.int64)
    gauge_coeff = {}
    for alpha in multiindices(2,4):
        value = difference(gauge_values,3,9,(0,0),alpha)
        require(value % 3 == 0, "gauge top symbol is not 3-torsion")
        gauge_coeff[alpha] = value // 3
    gauge_tensor = np.zeros(len(vertices),dtype=np.int64)
    for assignment in product((0,1),repeat=4):
        k = sum(assignment)
        term = np.prod(np.stack([h[:,j,assignment[j]] for j in range(4)],axis=1),axis=1)
        gauge_tensor += gauge_coeff[(4-k,k)]*term
    require(bool(np.all((gauge_array[vertices] @ signs - 3*gauge_tensor) %9 ==0)),
            "full ninth-root gauge identity failed")
    for c in range(3):
        lower_phase = np.asarray([(gauge_values[(x,c)]-x*x)%9 for x in range(3)],dtype=np.int64)
        require(bool(np.all((lower_phase[hv] @ hs)%9 ==0)),
                "common-primitive coset gauge has nonzero fourth derivative")
    examples = []
    for t in range(24):
        codes = np.asarray([rng.choice((-1,0,1,2)) for _ in range(9)], dtype=np.int64)
        E = root_of_unity_energy(codes, vertices, signs, twist)
        L = [root_of_unity_energy(codes[[3*x+c for x in range(3)]], hv, hs) for c in range(3)]
        require(E <= sum(L, Fraction())/3, "arithmetic-mean localization failed")
        lower = (sum((root_lower(z,d+1) for z in L),Fraction())/3) ** (d+1)
        # A positive exact equality involving non-dyadic roots could evade this
        # sufficient check; our one-coset equality is verified separately below.
        require(E <= lower, "rational lower certificate for moment bound failed")
        examples.append(dict(index=t, codes=codes.tolist(), energy=str(E),
                             local_energies=[str(v) for v in L],
                             certified_moment_lower_bound=str(lower)))
    codes = np.asarray([0 if y == 1 else -1 for x,y in points(3,2)], dtype=np.int64)
    E = root_of_unity_energy(codes, vertices, signs, twist)
    L = [root_of_unity_energy(codes[[3*x+c for x in range(3)]],hv,hs) for c in range(3)]
    require(E == Fraction(1,3**5) and L == [0,1,0], "supported-coset equality failed")
    constant_E = root_of_unity_energy(np.zeros(9,dtype=np.int64), vertices, signs, twist)
    require(constant_E == Fraction(11,27), "canonical ternary block energy failed")
    return dict(p=p,n=n,d=d,enumerated_global_cubes=len(vertices),
                enumerated_cubes_per_coset=len(hv), tested_random_functions=len(examples),
                root_certificate_denominator_power=72, cases=examples,
                supported_coset_energy=str(E), supported_coset_local_energies=[str(v) for v in L],
                canonical_block_constant_function_energy=str(constant_E),
                ninth_root_gauge=dict(primitive="(x_1^2+x_1*x_2)/9 mod 1",
                    local_primitive="x_1^2/9 mod 1",
                    full_cube_identities=len(vertices),
                    lower_degree_coset_identities=3*len(hv),
                    top_symbol_coefficients={str(k):v for k,v in gauge_coeff.items()}))


def ternary_symbol_census() -> dict:
    p, d = 3, 4
    pts = np.asarray(points(p,2),dtype=np.int64)
    triples = np.asarray(list(product(range(9),repeat=3)),dtype=np.int64)
    h = pts[triples]
    # Coefficient t_j means j occurrences of e_2 in the symmetric basis multiset.
    # Build exact weights of t_j in T(h1,h2,h3,e1/e2).
    weights = np.zeros((len(triples),2,5),dtype=np.int64)
    for a in product((0,1),repeat=3):
        val = np.prod(np.stack([h[:,i,a[i]] for i in range(3)],axis=1),axis=1)
        for last in (0,1):
            weights[:,last,sum(a)+last] += val
    distribution = Counter()
    tensors = 0
    for coeff in product(range(3),repeat=5):
        if (coeff[1]-coeff[3])%3 != 1:
            continue
        functional = np.tensordot(weights,np.asarray(coeff,dtype=np.int64),axes=([2],[0])) %3
        zero = int(np.count_nonzero(np.all(functional==0,axis=1)))
        distribution[zero] += 1
        tensors += 1
    expected = {217:9,241:24,249:24,265:12,297:12}
    require(dict(sorted(distribution.items()))==expected and tensors==81,
            "ternary symbol census failed")
    return dict(exhaustive=True, p=3,n=2,d=4,defect_constraint="t_1-t_3=1 (mod 3)",
                tensor_count=tensors, triples_per_tensor=729,
                zero_functional_triple_distribution=dict(sorted(distribution.items())),
                maximum_energy=str(Fraction(max(distribution),729)),
                limitation="Exhausts critical tensor symbols with fixed defect, not arbitrary bounded functions.")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path,default=Path("data/verification.json"))
    args=parser.parse_args()
    started=time.monotonic()
    rng=random.Random(SEED)
    result = dict(status="PASS", seed=SEED, python=platform.python_version(), numpy=np.__version__,
                  method="exact integers and rational arithmetic; finite regression checks, not formal verification")
    print("Checking critical primitives...",flush=True)
    result["critical_primitives"]=integration_checks(rng)
    print("Checking alternating matrices and all repair subspaces in dimension four...",flush=True)
    result["algebraic_counts"]=algebra_counts()
    print("Checking lossless localization with exact root certificates...",flush=True)
    result["localization"]=localization_checks(rng)
    print("Checking the exhaustive ternary critical-symbol census...",flush=True)
    result["ternary_census"]=ternary_symbol_census()
    result["elapsed_seconds"]=round(time.monotonic()-started,3)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
    print(f"PASS: report written to {args.output}",flush=True)


if __name__=="__main__":
    main()

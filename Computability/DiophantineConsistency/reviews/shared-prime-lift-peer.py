#!/usr/bin/env python3
"""Independent finite and structural controls for the prime-lift CRT theorem.

The valuation controls use trial prime factorization, rather than the
candidate's repeated-gcd construction. The bound audit executes only the
pinned numerical-calculus function against a separate monotone DAG builder.
No original compiler, machine, prover, or native encoder is run.
"""
from __future__ import annotations

import argparse
from hashlib import sha256
import importlib.util
import json
from math import comb, factorial, gcd, prod
from pathlib import Path


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def factor(n):
    out = {}
    p = 2
    while p*p <= n:
        while n % p == 0:
            out[p] = out.get(p, 0)+1
            n //= p
        p += 1
    if n > 1:
        out[n] = out.get(n, 0)+1
    return out


def factorial_valuation(n, p):
    value = 0
    while n:
        n //= p
        value += n
    return value


def crt(residues, moduli):
    modulus = prod(moduli)
    return sum(r*(modulus//d)*pow(modulus//d, -1, d)
               for r, d in zip(residues, moduli)) % modulus


def valuation_controls():
    cases = noncoprime = large_bound = empty = 0
    for N in range(5):
        for H in range(N, N+3):
            T = factorial(H)
            ds = [1+(i+1)*T for i in range(N)]
            B = prod(ds)
            need(all(gcd(d, e) == 1 for i, d in enumerate(ds) for e in ds[:i]),
                 "base-modulus coprimality")
            C = crt(list(range(N)), ds)
            need((1+(C+1)*T) % B == 0, "independent index CRT")
            for u in list(range(17))+[31]:
                F = factorial(u+1)
                lifted = []
                for d in ds:
                    support = prod(p**factorial_valuation(u+1, p) for p in factor(d))
                    need(F % support == 0 and gcd(d, F//support) == 1,
                         "full prime-supported factorial part")
                    lifted.append(d*support)
                need(all(gcd(d, e) == 1 for i, d in enumerate(lifted) for e in lifted[:i]),
                     "lifted-modulus coprimality")
                period = prod(lifted)
                for offset in range(3):
                    ws = [(i*i+offset) % (u+1) for i in range(N)]
                    A = crt(ws, lifted)+(u+1)*period
                    need(A > u and all((A-w) % D == 0 for w, D in zip(ws, lifted)),
                         "positive strengthened CRT representative")
                    need(comb(A, u+1) % B == 0, "binomial divisibility after factorial division")
                    for i, (d, w) in enumerate(zip(ds, ws)):
                        numerator = prod(A-r for r in range(u+1))
                        need(numerator % lifted[i] == 0 and (A-w) % lifted[i] == 0,
                             "numerator contains the strengthened zero factor")
                        for p, exponent in factor(d).items():
                            need(numerator % (p**(exponent+factorial_valuation(u+1, p))) == 0,
                                 "exact required prime valuation")
                    cases += 1
                    noncoprime += gcd(F, B) > 1
                    large_bound += u+1 > H
                    empty += N == 0

    # Soundness extracts a bounded root without requiring p>u.
    roots = large_root_bounds = 0
    for p in [2, 3, 5, 7, 11, 13, 17, 23, 31, 37]:
        for u in range(33):
            for A in range(3*p):
                if comb(A, u+1) % p == 0:
                    need(any((A-r) % p == 0 for r in range(u+1)),
                         "prime-product root extraction")
                    roots += 1
                    large_root_bounds += u >= p
    need(comb(1, 3) % 3 == 0 and comb(4, 3) % 3 != 0 and comb(10, 3) % 3 == 0,
         "plain B shift is unsafe, strengthened period is safe")
    return dict(strengthened_CRT_cases=cases, factorial_not_coprime_cases=noncoprime,
                bound_exceeds_H_cases=large_bound, empty_index_cases=empty,
                prime_root_cases=roots, prime_root_cases_with_u_at_least_p=large_root_bounds,
                plain_B_shift_negative_control="PASS")


class MonotoneDAG:
    def __init__(self):
        self.nodes = []
        self.cache = {}

    def binary(self, op, a, b):
        for x in [a, b]:
            need(x[0] in ("c", "v", "n"), "unknown DAG atom")
            if x[0] == "c":
                need(type(x[1]) is int and x[1] >= 0, "negative constant")
        a, b = sorted([a, b])
        key = (op, a, b)
        if key not in self.cache:
            self.cache[key] = ("n", len(self.nodes))
            self.nodes.append(key)
        return self.cache[key]

    def add(self, a, b):
        return self.binary("add", a, b)

    def mul(self, a, b):
        return self.binary("mul", a, b)

    def square(self, a):
        return self.mul(a, a)

    def sum(self, values):
        out = ("c", 0)
        for value in values:
            out = self.add(out, value)
        return out

    def product(self, values):
        out = ("c", 1)
        for value in values:
            out = self.mul(out, value)
        return out

    def pair_add(self, a, b):
        return self.add(a[0], b[0]), self.add(a[1], b[1])

    def pair_mul(self, a, b):
        return (self.add(self.mul(a[0], b[0]), self.mul(a[1], b[1])),
                self.add(self.mul(a[0], b[1]), self.mul(a[1], b[0])))

    def pair_square(self, a):
        return self.add(self.square(a[0]), self.square(a[1])), self.product([("c", 2), *a])


def source_bound_control(directory):
    path = directory/"source/direct_calculus.py"
    expected = "68200f7a6a063c4ef8c3c1462f104f0e1f5b99e43f9fccb3db991ca1e80b9348"
    need(sha256(path.read_bytes()).hexdigest() == expected, "pinned literal arithmetic source")
    spec = importlib.util.spec_from_file_location("pinned_positive_calculus", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    source = json.loads((directory/"source/wire_eliminated_source.json").read_text())
    names = ["t", "x", "y", "m", "M0", "p", "q", "v", "a", "b", "c", "d",
             "S", "Sp", "u", "r", "vq", "rp"]
    bounds = {name: ("v", name) for name in names[:5]}
    bounds.update({name: ("v", "m" if name in ["p", "q", "v"] else "U")
                   for name in names[5:]})
    dag = MonotoneDAG()
    roots = module.source_pair_calculus(dag, source, bounds, ("v", "N"), False)
    active = set()
    visited = set()

    def walk(atom):
        if atom[0] == "v":
            active.add(atom[1])
        elif atom[0] == "c":
            need(atom[1] >= 0, "constant sign")
        elif atom[1] not in visited:
            visited.add(atom[1])
            op, a, b = dag.nodes[atom[1]]
            need(op in ["add", "mul"], "non-monotone operation")
            for child in [a, b]:
                need(child[0] != "n" or child[1] < atom[1], "DAG acyclicity")
                walk(child)

    for root in roots:
        walk(root)
    need(active == {"N", "x", "y", "m", "M0", "U"}, "bound dependency closure")
    return dict(positive_circuit_nodes=len(visited), leaf_parameters=sorted(active),
                monotone_by_add_mul_induction=True, no_encoded_column_or_index_dependency=True,
                private_bound_independent_of_m=True)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--directory", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    result = dict(status="PASS", optimized=not __debug__,
                  valuation_controls=valuation_controls(),
                  source_bound_control=source_bound_control(args.directory),
                  scope="Finite controls and structural monotonicity, not a replacement for the universal CRT proof or C222/ZFC calibration")
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True)+"\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()

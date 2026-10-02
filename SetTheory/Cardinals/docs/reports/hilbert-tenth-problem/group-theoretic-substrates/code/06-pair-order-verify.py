#!/usr/bin/env python3
"""Independent exact checks for the accompanying article; standard library."""
from __future__ import annotations
from collections import defaultdict
from functools import lru_cache
from itertools import product
from pathlib import Path
from random import Random
import hashlib
import json
import sys
from pair_geometry import (Poly, binary_word, canonical_c2, corner_bounds,
                           gap_bounds, gap_system, gap_vectors, general_bounds,
                           normalization_path, pair_profile, realize_gaps)

@lru_cache(None)
def profiles(a: int, b: int, c: int) -> frozenset[tuple[int, int, int]]:
    # Independent last-letter recurrence: coordinates are AB, AC, BC.
    if (a, b, c) == (0, 0, 0):
        return frozenset({(0, 0, 0)})
    answer = set()
    if a:
        answer.update(profiles(a-1, b, c))
    if b:
        answer.update((k+a, p, q) for k, p, q in profiles(a, b-1, c))
    if c:
        answer.update((k, p+a, q+b) for k, p, q in profiles(a, b, c-1))
    return frozenset(answer)


def check_intervals_and_gaps() -> dict:
    boxes = slices = triples = endpoint_checks = 0
    for a, b, c in product(range(6), range(6), range(5)):
        actual = profiles(a, b, c)
        by_slice = defaultdict(set)
        for k, p, q in actual:
            by_slice[p, q].add(k)
        assert len(by_slice) == (a*c+1)*(b*c+1)
        for (p, q), values in by_slice.items():
            assert values == set(range(min(values), max(values)+1))
            # Full gap-vector union, not just endpoints.
            union = set()
            for x in gap_vectors(a, c, p):
                for y in gap_vectors(b, c, q):
                    lo, hi = gap_bounds(x, y)
                    union.update(range(lo, hi+1))
            assert union == values
            if c == 2:
                assert corner_bounds(a, b, p, q) == (min(values), max(values))
                endpoint_checks += 1
            slices += 1
        boxes += 1
        triples += len(actual)
    return {"count_boxes": boxes, "ranges": "0<=a,b<=5; 0<=c<=4",
            "nonempty_slices": slices, "realizable_profiles": triples,
            "c2_corner_endpoint_checks": endpoint_checks}


def check_normalization() -> dict:
    endpoints = {}
    words = edges = 0
    for n in range(9):
        for letters in product("ABC", repeat=n):
            word = "".join(letters)
            counts, (k, p, q) = pair_profile(word)
            previous = k
            path = list(normalization_path(word))
            for vertex in path:
                cn, (kk, pp, qq) = pair_profile(vertex)
                assert (cn, pp, qq) == (counts, p, q)
                assert abs(kk-previous) <= 1
                previous = kk
            key = counts, p, q
            if key in endpoints:
                assert endpoints[key] == path[-1]
            endpoints[key] = path[-1]
            words += 1; edges += len(path)-1
    return {"word_lengths": "0 through 8", "words": words,
            "checked_edges": edges, "canonical_fibres": len(endpoints)}


def check_canonical() -> dict:
    system, _ = canonical_c2()
    poly = system.polynomial()
    assert len(system.witnesses) == len(system.residuals) == 24
    assert max(f.degree for f in system.residuals) == 2
    assert poly.degree == 4
    checked = accepted = mutated = 0
    good = []
    # Use one prebuilt symbolic system for verification, with separately
    # computed candidate assignments.  These are not a zero-set exhaustion.
    for a, b in product(range(6), repeat=2):
        actual = profiles(a, b, 2)
        for p, q in product(range(2*a+2), range(2*b+2)):
            bounds = corner_bounds(a, b, p, q)
            for k in range(a*b+2):
                truth = (k, p, q) in actual
                decision = bounds is not None and bounds[0] <= k <= bounds[1]
                assert truth == decision
                checked += 1
            # Endpoint, immediate outside, and boundary domain samples.
            sample_ks = {0, a*b+1}
            if bounds:
                lo, hi = bounds
                sample_ks.update((lo, hi, hi+1, max(0, lo-1)))
            for k in sample_ks:
                _, env = canonical_c2(dict(a=a, b=b, p=p, q=q, k=k))
                assert env is not None
                assert not any(system.residual_values(env))
                is_natural = all(v >= 0 for v in env.values())
                assert is_natural == ((k, p, q) in actual)
                if is_natural:
                    assert system.verify(env)
                    accepted += 1
                    if len(good) < 150:
                        good.append(env)
    for env in good:
        for name in system.witnesses:
            for delta in (-1, 1):
                new = dict(env); new[name] += delta
                if new[name] >= 0:
                    assert not system.verify(new)
                    mutated += 1
    rng = Random(20261002)
    for _ in range(250):
        env = {n: rng.randrange(-8, 9) for n in system.parameters + system.witnesses}
        values = system.residual_values(env)
        assert poly.evaluate(env) == sum(v*v for v in values)
    # Much larger inputs: exact integer arithmetic and no word generation.
    large_cases = []
    for power in (20, 100, 300):
        a, b = 10**power+1, 10**(power-1)+7
        p, q = a+3, b+5
        bounds = corner_bounds(a, b, p, q)
        assert bounds is not None
        for k in bounds:
            _, env = canonical_c2(dict(a=a, b=b, p=p, q=q, k=k))
            assert env is not None and system.verify(env)
        large_cases.append(power)
    return {"complete_profile_decisions": checked, "canonical_acceptance_samples": accepted,
            "one_coordinate_mutations_rejected": mutated,
            "signed_off_zero_polynomial_checks": 250,
            "large_input_decimal_exponents": large_cases,
            "witnesses": len(system.witnesses), "residuals": len(system.residuals),
            "quartic_degree": poly.degree, "quartic_monomials": len(poly.terms)}


def all_words(counts: tuple[int, ...], alphabet: str):
    remaining = list(counts)
    def go(prefix):
        if not any(remaining):
            yield prefix; return
        for i, ch in enumerate(alphabet):
            if remaining[i]:
                remaining[i] -= 1
                yield from go(prefix+ch)
                remaining[i] += 1
    yield from go("")


def check_four_letter() -> dict:
    d = defaultdict(set)
    words = 0
    for word in all_words((2,2,2,2), "ABCD"):
        _, pair = pair_profile(word, "ABCD")
        d[pair[1:]].add(pair[0]); words += 1
    key = (2,2,2,4,3)
    assert d[key] == {0,2}
    families = []
    for n, b in ((0,2), (1,2), (2,2), (3,2), (4,2), (3,3), (4,3)):
        vals = set()
        for word in all_words((n,b,2,2), "ABCD"):
            _, pairs = pair_profile(word, "ABCD")
            if pairs[1:] == (n,n,b,2*b,3):
                vals.add(pairs[0])
        assert vals == {b*j for j in range(n//2+1)}
        families.append({"n": n, "b": b, "spectrum": sorted(vals)})
    return {"two_each_words": words, "fixed_other_pairs": list(key),
            "spectrum": sorted(d[key]), "all_noninterval_fibres": sum(len(v)!=max(v)-min(v)+1 for v in d.values()),
            "family_checks": families}


def mm(a, b):
    return tuple(tuple(sum(a[i][k]*b[k][j] for k in range(3)) for j in range(3)) for i in range(3))

def mat(t):
    a, b, c = t
    return ((1,a,c), (0,1,b), (0,0,1))


def check_heisenberg() -> dict:
    rng = Random(8873)
    checks = 0
    for _ in range(2000):
        gs = [tuple(rng.randrange(-4,5) for _ in range(3)) for _ in range(3)]
        word = "".join(rng.choice("ABC") for _ in range(rng.randrange(30)))
        counts, (k,p,q) = pair_profile(word)
        ns = counts
        Ks = {(0,1): k, (0,2): p, (1,2): q}
        for i,j in list(Ks):
            Ks[j,i] = ns[i]*ns[j]-Ks[i,j]
        for i in range(3): Ks[i,i] = ns[i]*(ns[i]-1)//2
        predicted = (sum(ns[i]*gs[i][0] for i in range(3)),
                     sum(ns[i]*gs[i][1] for i in range(3)),
                     sum(ns[i]*gs[i][2] for i in range(3)) +
                     sum(Ks[i,j]*gs[i][0]*gs[j][1] for i in range(3) for j in range(3)))
        actual = mat((0,0,0))
        for ch in word: actual = mm(actual, mat(gs["ABC".index(ch)]))
        assert mat(predicted) == actual
        checks += 1
    # Repository's strict-interior false positives, without copying its code.
    for m in range(3,100):
        assert corner_bounds(m,2,2,1) == (2,m+2)
        assert realize_gaps(m,2,2,2,1,1) is None
    return {"independent_matrix_products": checks, "repository_false_family_m": "3 through 99"}


def check_domains_and_ownership() -> dict:
    count = 0
    for bad in (-1, 0.5, "1", True, None):
        try: corner_bounds(bad, 2, 1, 1)
        except (ValueError, TypeError): count += 1
        else: raise AssertionError("invalid parameter accepted")
    original = [[['x'], 2]]
    p = Poly(original)
    original[0][0].append('y')
    original[0][1] = 99
    assert p.evaluate({'x': 3}) == 6
    for a,b in product(range(8),repeat=2):
        for k in range(a*b+1):
            w = binary_word(a,b,k)
            assert pair_profile(w) == ((a,b,0),(k,0,0))
    for c in range(7):
        sys = gap_system(c)
        assert len(sys.witnesses) == 2*c+4 and len(sys.residuals) == 6
        assert sys.polynomial().degree == 4
    return {"invalid_inputs_rejected": count, "owned_immutable_polynomial": True,
            "binary_constructor_range": "0<=a,b<=7, all k", "general_c_ledgers_checked": "0 through 6"}


def main():
    output = Path(__file__).resolve().parents[1] / "data" / "verification_receipt.json"
    result = {"status": "PASS", "scope": "Finite exact tests supplement the article's proofs; no Lean formalization.",
              "interval_and_gap_tests": check_intervals_and_gaps(),
              "normalization": check_normalization(),
              "canonical_compiler": check_canonical(),
              "four_letter_obstruction": check_four_letter(),
              "matrix_lift": check_heisenberg(),
              "validation": check_domains_and_ownership()}
    export_path = output.with_name("canonical_c2_quartic.json")
    rebuilt, _ = canonical_c2()
    assert json.loads(export_path.read_text(encoding="utf-8")) == rebuilt.serial(), "export mismatch"
    result["export_replay"] = "Complete JSON residuals and expanded polynomial match rebuilt source."
    source = Path(__file__).with_name("pair_geometry.py").read_bytes()
    result["compiler_sha256"] = hashlib.sha256(source).hexdigest()
    text = json.dumps(result, indent=2)+"\n"
    if "--write" in sys.argv:
        output.write_text(text, encoding="utf-8")
    elif output.exists():
        assert json.loads(output.read_text(encoding="utf-8")) == result, "receipt mismatch"
    print(text)

if __name__ == "__main__": main()

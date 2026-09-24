#!/usr/bin/env python3
"""Reproduce finite consistency checks and the worked length-330 certificate.

These tests check implementation and examples, not the universal theorem.
Run from any directory: python code/verify.py
"""
from __future__ import annotations
import hashlib
import json
import random
import time
from itertools import combinations, permutations
from pathlib import Path
from reverse_reply import (Template, bound, construct_reply, isolate, monotone,
                           shadow_direct, standardize, monotone_indices)

ROOT = Path(__file__).resolve().parents[1]
RNG = random.Random(20260920)  # Test seed, NOT the area-selection randomness.


def nonmono(sh):
    return frozenset(q for q in sh if not monotone(q))


def core_occurrence(T: Template, t: int):
    return tuple(j if j < T.index else j + t - 1
                 for j in range(len(T.beta)) if j != T.index)


def exhaustive_small():
    rows = []
    for k in (3, 4):
        count = pairs = arbitrary_sets = 0
        all_nonmono = tuple(p for p in permutations(range(1, k + 1)) if not monotone(p))
        for beta in permutations(range(1, k + 2)):
            for i in range(k + 1):
                for sign in (1, -1):
                    T = Template(beta, i, sign)
                    sh = T.stable_shadow(k)
                    for t in (k - 1, k, k + 1):
                        assert nonmono(shadow_direct(T.inflate(t), k)) == sh
                    for p in sorted(sh):
                        Q = {p, p[::-1]}
                        U, _ = isolate(T, Q)
                        direct = nonmono(shadow_direct(U.inflate(k - 1), k))
                        assert direct <= sh and len(direct & Q) == 1
                        # Check minimality independently by direct enumeration.
                        for j in range(len(U.beta)):
                            if j != U.index:
                                assert not shadow_direct(U.delete(j).inflate(k - 1), k) & Q
                        pairs += 1
                    if k == 3:
                        for mask in range(1, 1 << len(all_nonmono)):
                            Q = {p for j, p in enumerate(all_nonmono) if (mask >> j) & 1}
                            if sh & Q:
                                U, _ = isolate(T, Q)
                                assert len(shadow_direct(U.inflate(k + 1), k) & Q) == 1
                                arbitrary_sets += 1
                    count += 1
        rows.append({"k": k, "templates": count, "block_lengths_per_template": 3,
                     "reverse_pair_minimizations": pairs,
                     "arbitrary_target_set_minimizations": arbitrary_sets})
    return rows


def sampled_large():
    rows = []
    for k in (5, 6, 7):
        count = 0
        for _ in range(120):
            beta = list(range(1, k + 2)); RNG.shuffle(beta)
            T = Template(tuple(beta), RNG.randrange(k + 1), RNG.choice((-1, 1)))
            sh = T.stable_shadow(k)
            assert nonmono(shadow_direct(T.inflate(k - 1), k)) == sh
            assert nonmono(shadow_direct(T.inflate(k + 1), k)) == sh
            if sh:
                targets = set(RNG.sample(sorted(sh), min(4, len(sh))))
                targets.update(p[::-1] for p in list(targets))
                U, _ = isolate(T, targets)
                assert len(shadow_direct(U.inflate(k - 1), k) & targets) == 1
            count += 1
        rows.append({"k": k, "sampled_templates": count})
    return rows


def constructive_tests():
    rows = []
    for k in range(3, 8):
        universe = frozenset(p for p in permutations(range(1, k + 1)) if not monotone(p))
        checked = 0
        while checked < 20:
            beta = list(range(1, k + 2)); RNG.shuffle(beta)
            T = Template(tuple(beta), RNG.randrange(k + 1), RNG.choice((-1, 1)))
            p = standardize(T.beta[:T.index] + T.beta[T.index + 1:])
            if monotone(p):
                continue
            sh = T.stable_shadow(k)
            F = universe - sh - frozenset(q[::-1] for q in sh)
            n = bound(k)
            t = n - k
            pi = T.inflate(t)
            reply, cert = construct_reply(pi, p, core_occurrence(T, t), F)
            assert len(reply) == n and sorted(reply) == list(range(1, n + 1))
            data = cert["minimal_template"]
            U = Template(tuple(data["beta"]), data["marked_index_zero_based"], data["sign"])
            small = U.inflate(k + 1)
            if cert["reverse_output"]:
                small = small[::-1]
            direct = nonmono(shadow_direct(small, k))
            assert p not in direct and p[::-1] in direct and not direct & F
            assert direct == frozenset(tuple(q) for q in cert["stable_nonmonotone_shadow"])
            checked += 1
        rows.append({"k": k, "n": bound(k), "certified_replies": checked})
    return rows


def extraction_on_unstructured_permutations():
    rows = []
    for k in range(3, 8):
        for _ in range(20):
            pi = list(range(1, bound(k) + 1)); RNG.shuffle(pi)
            ix = tuple(range(k))
            p = standardize(pi[:k])
            if monotone(p):
                ix = tuple(sorted(RNG.sample(range(len(pi)), k)))
                p = standardize(tuple(pi[j] for j in ix))
            if monotone(p):
                continue
            reply, cert = construct_reply(tuple(pi), p, ix)
            assert len(reply) == len(pi)
        rows.append({"k": k, "attempted_extractions": 20})
    return rows


def worked_example():
    k = 5
    found = None
    for beta in permutations(range(1, k + 2)):
        for i in range(k + 1):
            p = standardize(beta[:i] + beta[i + 1:])
            if monotone(p):
                continue
            for s in (1, -1):
                T = Template(beta, i, s)
                sh = T.stable_shadow(k)
                if p[::-1] in sh:
                    U, trace = isolate(T, {p, p[::-1]})
                    if len(trace) >= 2 and U.singletons >= 2:
                        found = T, p
                        break
            if found: break
        if found: break
    assert found is not None
    T, p = found
    sh = T.stable_shadow(k)
    universe = frozenset(q for q in permutations(range(1, k + 1)) if not monotone(q))
    F = universe - sh - frozenset(q[::-1] for q in sh)
    n = bound(k); t = n - k
    pi = T.inflate(t)
    reply, cert = construct_reply(pi, p, core_occurrence(T, t), F)
    cert.update({"original_template": T.record(), "input_permutation": list(pi),
                 "reply_permutation": list(reply),
                 "input_stable_nonmonotone_shadow": [list(q) for q in sorted(sh)]})
    (ROOT / "data" / "worked_certificate.json").write_text(json.dumps(cert, indent=2) + "\n")
    return {"k": k, "n": n, "p": list(p), "original_template": T.record(),
            "forbidden_count": len(F), "minimal_template": cert["minimal_template"],
            "reverse_output": cert["reverse_output"],
            "deletion_steps": len(cert["deletion_trace"]) - 1,
            "certificate_file": "data/worked_certificate.json"}


def es_boundary_tests():
    for h in range(2, 10):
        m = h - 1
        p = tuple(x for b in range(m) for x in range((b + 1) * m, b * m, -1))
        try:
            monotone_indices(p, h)
        except ValueError:
            pass
        else:
            raise AssertionError("ES boundary example unexpectedly has length h")
        for _ in range(20):
            a = list(range(m*m + 1)); RNG.shuffle(a)
            ix, s = monotone_indices(a, h)
            assert len(ix) == h and all(s * (a[ix[j+1]] - a[ix[j]]) > 0 for j in range(h-1))
    return {"h_values": list(range(2, 10)), "random_sequences_per_h": 20,
            "sharp_boundary_examples": 8}


def main():
    start = time.monotonic()
    (ROOT / "data").mkdir(exist_ok=True)
    result = {"test_seed": 20260920, "arithmetic": "exact integers only",
              "status": "PASS", "scope": "finite checks, not a proof of the universal theorem"}
    for name, fn in [("exhaustive_small", exhaustive_small),
                     ("sampled_large", sampled_large),
                     ("constructive_tests", constructive_tests),
                     ("unstructured_extractions", extraction_on_unstructured_permutations),
                     ("es_boundary_tests", es_boundary_tests),
                     ("worked_example", worked_example)]:
        result[name] = fn()
        print(name, json.dumps(result[name]), flush=True)
    result["bounds"] = {str(k): bound(k) for k in range(3, 11)}
    result["elapsed_seconds"] = round(time.monotonic() - start, 3)
    result["code_sha256"] = {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                             for p in (Path(__file__), Path(__file__).with_name("reverse_reply.py"))}
    (ROOT / "data" / "verification.json").write_text(json.dumps(result, indent=2) + "\n")
    print("ALL CHECKS PASSED", result["elapsed_seconds"], "seconds", flush=True)

if __name__ == "__main__":
    main()

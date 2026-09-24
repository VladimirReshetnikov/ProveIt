"""Reproducible finite checks. Run: python3 code/check_finite.py

Do not run with -O: assertions are the checks. A finite run is not a proof of
the infinite minimal-pair or jump claims. Absence of a bounded witness is NEVER
treated as an answer to an unbounded halting query.
"""
from __future__ import annotations

import json
import random
from itertools import product
from pathlib import Path
from finite_model import (
    Condition, Query, Return, Tree, column_count, column_index, column_point,
    cross_witness, evaluate, realizations, sparse_encode, tail_count,
)


def main() -> None:
    if not __debug__:
        raise RuntimeError("Run without -O; this program uses assertion checks")
    rng = random.Random(20260918)
    counts: dict[str, int] = {}

    checks = 0
    for n in range(2049):
        observed = [0] * 13
        for x in range(n):
            observed[column_index(x)] += 1
        for k in range(12):
            assert observed[k] == column_count(k, n)
            assert sum(observed[k:]) == tail_count(k, n)
            checks += 2
    for k in range(16):
        for t in range(257):
            assert column_index(column_point(k, t)) == k
            checks += 1
    counts["column_and_tail_identities"] = checks

    checks = 0
    for length in range(4):
        for stem in product((0, 1), repeat=length):
            for k in range(3):
                for frozen in product((0, 1), repeat=k):
                    p = Condition(stem, frozen)
                    for bit in (0, 1):
                        q = p.freeze_next(bit)
                        for gamma in q.extensions(8):
                            assert p.allows(gamma)
                            checks += 1
                    for alpha in p.extensions(5):
                        q = p.extend(alpha)
                        for gamma in q.extensions(8):
                            assert p.allows(gamma)
                            checks += 1
    counts["condition_inclusions"] = checks

    checks = 0
    for _ in range(1500):
        a = tuple(rng.randrange(2) for _ in range(8))
        k, length, n = rng.randrange(6), rng.randrange(15), rng.randrange(16, 100)
        stem = tuple(rng.randrange(2) for _ in range(length))
        p = Condition(stem, a[:k])
        bits = list(stem)
        for x in range(length, n):
            b = p.fixed_bit(x)
            bits.append(rng.randrange(2) if b is None else b)
        errors = sum(bits[x] != a[column_index(x)] for x in range(n))
        assert errors <= length + tail_count(k, n)
        checks += 1
    counts["density_restraint_inequalities"] = checks

    # Concrete convergent array, not a jump oracle.
    a = lambda k: ((k * 17 + 5) ^ (k >> 1)) & 1
    threshold = lambda k: 3 * k * k + 2
    approximation = lambda k, t: a(k) ^ int(t < threshold(k))
    d = lambda x: approximation(column_index(x), ((x + 1) >> column_index(x)) // 2)
    checks = 0
    for k in range(10):
        t = 2 * threshold(k) + 1
        majority = int(2 * sum(d(column_point(k, j)) for j in range(t)) > t)
        assert majority == a(k)
        checks += 1
    for k in range(1, 9):
        finite_errors = sum(threshold(j) for j in range(k))
        for n in (1, 2, 7, 31, 256, 2048, 16384):
            errors = sum(d(x) != a(column_index(x)) for x in range(n))
            assert errors <= finite_errors + tail_count(k, n)
            checks += 1
    counts["limit_array_and_majority_checks"] = checks

    def table_tree(values: tuple[int | None, ...]) -> Tree:
        return Query(0, Query(1, Return(values[0]), Return(values[1])),
                     Query(1, Return(values[2]), Return(values[3])))

    trees = [table_tree(values) for values in product((None, 0, 1), repeat=4)]
    conditions = [Condition(), Condition((), (0,)), Condition((1,), (0,)),
                  Condition((0, 1), (1, 0))]
    mismatch, nosplit, total_common = 0, 0, 0
    for p in conditions:
        for q in conditions:
            for lt in trees:
                for rt in trees:
                    witness = cross_witness(p, q, (lt,), (rt,))
                    lv, rv = realizations(p, lt), realizations(q, rt)
                    if witness is not None:
                        n, alpha, beta = witness
                        assert n == 0 and p.allows(alpha) and q.allows(beta)
                        assert evaluate(lt, alpha) != evaluate(rt, beta)
                        assert evaluate(lt, alpha) is not None
                        assert evaluate(rt, beta) is not None
                        mismatch += 1
                    else:
                        nosplit += 1
                        lconv = {x for x in lv if x is not None}
                        rconv = {x for x in rv if x is not None}
                        if lconv and rconv:
                            assert len(lconv | rconv) == 1
                            total_common += 1
    counts["finite_cross_disagreement_cases"] = mismatch
    counts["finite_no_cross_split_cases"] = nosplit
    counts["finite_common_convergent_output_cases"] = total_common

    checks = 0
    base = lambda n: (n * 31 + n // 7) & 1
    payload = lambda j: (j * j + j // 3) & 1
    for j in range(20):
        assert sparse_encode(base, payload, 1 << j) == payload(j)
        checks += 1
    for n in range(1, 4097):
        changes = sum(sparse_encode(base, payload, x) != base(x) for x in range(n))
        assert changes <= (n - 1).bit_length()
        checks += 1
    counts["sparse_padding_checks"] = checks

    p = Condition((1, 0, 1), ())
    q = p.freeze_next(0)
    assert q.stem == (1, 0, 1)
    assert q.pad(10).stem[:3] == p.stem
    assert q.pad(10).stem[4] == 0
    counts["old_stem_regressions"] = 3

    output = {
        "status": "PASS", "seed": 20260918, "checks": counts,
        "total_checked_cases": sum(counts.values()),
        "scope": "Finite identities, restraints, and finite-query toy computations only",
        "not_verified_by_this_program": [
            "actual membership in the second Turing jump",
            "unbounded halting queries in the infinite construction",
            "the infinite minimal-pair theorem",
            "any Lean formalization",
        ],
    }
    destination = Path(__file__).resolve().parents[1] / "verification" / "finite_checks.json"
    destination.parent.mkdir(exist_ok=True)
    destination.write_text(json.dumps(output, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()

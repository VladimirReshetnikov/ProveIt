"""Finite gluing and generalized two-modulus CRT: exact reference checks."""
from itertools import product
from pathlib import Path
from math import gcd
import json


def glue(n, m, masks, sections):
    assert n >= 0 and m >= 0 and len(masks) == len(sections)
    domains = [tuple(x for x in range(n) if mask >> x & 1) for mask in masks]
    assert all(0 <= mask < 2 ** n for mask in masks)
    assert all(len(s) == len(d) and all(0 <= v < m for v in s)
               for s, d in zip(sections, domains))
    local = [dict(zip(d, s)) for d, s in zip(domains, sections)]
    out = []
    for x in range(n):
        patches = [i for i in range(len(masks)) if x in local[i]]
        if not patches:
            return {"status": "uncovered", "point": x}
        v = local[patches[0]][x]
        for i in patches:
            if local[i][x] != v:
                return {"status": "incompatible", "point": x,
                        "patches": (patches[0], i)}
        out.append(v)
    return {"status": "glued", "table": tuple(out)}


def extended_gcd(a, b):
    assert a > 0 and b > 0
    r0, r1, u0, u1, v0, v1 = a, b, 1, 0, 0, 1
    for _ in range(a + b + 1):
        assert r0 == u0 * a + v0 * b and r1 == u1 * a + v1 * b
        if r1 == 0:
            assert r0 == gcd(a, b)
            return r0, u0, v0
        q = r0 // r1
        r0, r1, u0, u1, v0, v1 = (r1, r0 - q * r1,
                                  u1, u0 - q * u1, v1, v0 - q * v1)
    raise AssertionError("The displayed Euclidean step bound failed")


def crt_pullback(a, b, r, s):
    assert a > 0 and b > 0 and 0 <= r < a and 0 <= s < b
    g, u, _ = extended_gcd(a, b)
    if (s - r) % g:
        return None
    modulus = a * (b // g)
    t = (u * ((s - r) // g)) % (b // g)
    return (r + a * t) % modulus, modulus


def check():
    counts = {"gluing_inputs": 0, "glued_tables": 0, "rejected_covers_or_overlaps": 0,
              "crt_pairs": 0, "crt_compatible_pairs": 0, "crt_inverse_values": 0}
    for n in range(4):
        for m in range(3):
            for masks in product(range(2 ** n), repeat=2):
                domains = [tuple(x for x in range(n) if mask >> x & 1) for mask in masks]
                for sections in product(*(tuple(product(range(m), repeat=len(d))) for d in domains)):
                    result = glue(n, m, masks, sections)
                    counts["gluing_inputs"] += 1
                    candidates = [f for f in product(range(m), repeat=n)
                                  if all(tuple(f[x] for x in d) == s
                                         for d, s in zip(domains, sections))]
                    covered = all(any(x in d for d in domains) for x in range(n))
                    compatible = all(s[domains[0].index(x)] == t[domains[1].index(x)]
                                     for x in set(domains[0]) & set(domains[1])
                                     for s, t in [sections])
                    if result["status"] == "glued":
                        assert covered and compatible and candidates == [result["table"]]
                        counts["glued_tables"] += 1
                    else:
                        assert not covered or not compatible
                        counts["rejected_covers_or_overlaps"] += 1
    # Include a genuinely empty cover, not only two empty masks.
    assert glue(0, 0, (), ()) == {"status": "glued", "table": ()}
    assert glue(1, 1, (), ())["status"] == "uncovered"
    for a in range(1, 13):
        for b in range(1, 13):
            l = a * b // gcd(a, b)
            fibres = {(r, s): [] for r in range(a) for s in range(b)}
            for x in range(l):
                fibres[x % a, x % b].append(x)
                answer = crt_pullback(a, b, x % a, x % b)
                assert answer == (x, l)
                counts["crt_inverse_values"] += 1
            for r in range(a):
                for s in range(b):
                    answer = crt_pullback(a, b, r, s)
                    counts["crt_pairs"] += 1
                    if answer is None:
                        assert not fibres[r, s]
                    else:
                        x, mod = answer
                        assert mod == l and fibres[r, s] == [x]
                        counts["crt_compatible_pairs"] += 1
    result = {"status": "passed", "scope": "finite exact diagnostics",
              "counts": counts,
              "gluing_example": glue(5, 7, (7, 28), ((0, 1, 4), (4, 2, 2))),
              "crt_example": {"moduli": [12, 18], "residues": [5, 11],
                              "solution_and_modulus": crt_pullback(12, 18, 5, 11)}}
    path = Path(__file__).resolve().parents[1] / "validation" / "descent_checks.json"
    path.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    check()

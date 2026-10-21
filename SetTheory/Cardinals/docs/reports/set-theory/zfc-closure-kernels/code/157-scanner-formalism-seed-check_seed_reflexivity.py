#!/usr/bin/env python3
"""Independent forward checker for the concrete native theorem code 3.

The accepted C222 calculus has derived K/S schemata. This checker makes that
inherited propositional basis explicit; it does not assume arbitrary
substitution as an object-language inference or GEN under assumptions.
"""
from collections import Counter
from pathlib import Path
import hashlib
import json
import sys

ZERO = ("zero",)


def freeze(x):
    return tuple(freeze(a) for a in x) if isinstance(x, list) else x


def imp(a, b):
    return ("I", a, b)


def rel(a, b):
    return ("R", a, b)


def eq(a, b):
    return ("E", a, b)


def all_(i, a):
    return ("Q", i, a)


FALSE = rel(ZERO, ZERO)


def neg(a):
    return imp(a, FALSE)


def exists(i, a):
    return neg(all_(i, neg(a)))


def expected_axiom(rule, args):
    if rule == "K":
        a, b = args
        return imp(a, imp(b, a))
    if rule == "S":
        a, b, c = args
        return imp(imp(a, imp(b, c)), imp(imp(a, b), imp(a, c)))
    if rule == "rho1":
        i, a = args
        return exists(i, eq(i, a))
    if rule == "rho2":
        i, a, b = args
        return imp(all_(i, imp(a, b)), imp(all_(i, a), all_(i, b)))
    if rule == "rho6":
        i, a = args
        return imp(exists(i, all_(i, a)), a)
    if rule == "G":
        a, b, c = args
        return imp(eq(c, a), imp(eq(c, b), all_(rel(a, b), eq(a, b))))
    raise AssertionError(("unknown axiom", rule))


def check(path):
    raw = path.read_bytes()
    data = json.loads(raw)
    assert data["format"] == "closed_native_hilbert_v1"
    previous = []
    kinds = Counter()
    for k, entry in enumerate(data["nodes"]):
        assert entry["id"] == k
        f = freeze(entry["formula"])
        args = freeze(entry["args"])
        parents = entry["parents"]
        assert all(type(p) is int and 0 <= p < k for p in parents)
        rule = entry["rule"]
        if rule == "mp":
            assert len(parents) == 2 and not args
            major, minor = (previous[p] for p in parents)
            assert major == imp(minor, f), ("modus ponens", k)
        elif rule == "gen":
            assert len(parents) == len(args) == 1
            # Every retained node is a closed theorem; no hypothesis rule exists.
            assert f == all_(args[0], previous[parents[0]])
        else:
            assert not parents
            assert f == expected_axiom(rule, args), ("axiom", k)
        previous.append(f)
        kinds[rule] += 1
    assert data["root"] == len(previous) - 1
    assert previous[-1] == eq(ZERO, ZERO)
    # E(a,b)=4*((a+b)*(a+b+1)//2+b)+3; E(0,0)=3.
    assert 4 * ((0 + 0) * (0 + 0 + 1) // 2 + 0) + 3 == 3
    return {
        "status": "PASS",
        "sha256": hashlib.sha256(raw).hexdigest(),
        "closed_proof_nodes": len(previous),
        "rules": dict(sorted(kinds.items())),
        "native_conclusion": 3,
        "ordinary_interpretation": "Every expression denotes its literal native natural code; structural equality suffices for MP even when I(0,0)=0.",
        "inherited_basis": "K and S derived from unrestricted native rho8, as in the accepted C222 calibration.",
        "scope": "Finite ordinary certificate, not a new proof-assistant endpoint."
    }


if __name__ == "__main__":
    path = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).with_name("seed_reflexivity_proof.json")
    print(json.dumps(check(path), indent=2))

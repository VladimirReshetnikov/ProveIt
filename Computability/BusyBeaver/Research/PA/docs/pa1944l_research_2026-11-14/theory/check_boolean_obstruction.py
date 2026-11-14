#!/usr/bin/env python3
"""Exact finite checks of the Boolean countermodel (not a TM certificate).

The accompanying theorem covers every numerical instance by structural
induction. This executable independently checks exact, potentially large
formula codes, and all truth assignments for the propositional head.
"""
from functools import lru_cache
from itertools import product
from math import isqrt
import json
from pathlib import Path


def pair(a, b):
    return (a + b) * (a + b + 1) // 2 + b


def unpair(n):
    s = (isqrt(8 * n + 1) - 1) // 2
    b = n - s * (s + 1) // 2
    return s - b, b


class CodedCalculus:
    def __init__(self, radix):
        assert radix in (3, 4)
        self.radix = radix

    def I(self, a, b):
        return self.radix * pair(a, b)

    def M(self, a, b):
        return self.radix * pair(a, b) + 1

    def U(self, a, b):
        return self.radix * pair(b, a) + 2

    def E(self, a, b):
        assert self.radix == 4
        return 4 * pair(a, b) + 3

    def N(self, a):
        return self.I(a, 1)

    def conjunction(self, a, b):
        return self.N(self.I(a, self.N(b)))

    def equivalence(self, a, b):
        return self.conjunction(self.I(a, b), self.I(b, a))

    def exists(self, a, b):
        return self.N(self.U(a, self.N(b)))

    @lru_cache(maxsize=None)
    def value(self, code):
        if code == 0:
            return True
        n, tag = divmod(code, self.radix)
        a, b = unpair(n)
        assert a < code and b < code
        if tag == 0:
            return not self.value(a) or self.value(b)
        if tag == 1:
            return False if a == b else self.value(a)
        if tag == 2:
            return self.value(a)
        assert tag == 3 and self.radix == 4
        return False

    def gamma(self, b):
        return self.I(b, self.U(b, b))

    def head1(self, a, c):
        return self.I(self.exists(a, self.U(a, c)), c)

    def head2(self, a, b, c):
        return self.I(self.U(a, self.U(b, c)), self.U(b, self.U(a, c)))

    def head3(self, c, a, b):
        return self.I(self.M(c, a), self.I(self.E(c, b), self.M(b, a)))

    def head4(self, c, a, b):
        return self.I(self.E(c, a), self.I(self.M(b, c), self.M(b, a)))

    def head5(self, a, c):
        return self.exists(a, self.E(c, a))

    def head6(self, a, b, c):
        return self.I(self.U(a, b), self.I(self.U(a, self.I(b, c)), self.U(a, c)))

    def rho8(self, d, a, h, u):
        return self.I(self.I(self.I(h, u), d), self.I(self.I(d, h), self.I(a, h)))

    def gate_parts(self, a, b, c):
        v = self.I(self.M(a, b), self.U(c, self.M(a, b)))
        p = self.I(c, self.M(c, b))
        s = self.U(b, self.conjunction(self.I(self.M(a, b), p), self.I(self.M(c, b), c)))
        q = self.U(c, self.I(s, self.N(p)))
        g = self.N(self.I(v, q))
        bundled = self.N(self.I(self.gamma(c), self.I(v, q)))
        return v, p, s, q, g, bundled

    def neighborhood_equality(self, a, b, z):
        return self.conjunction(
            self.U(z, self.equivalence(self.M(a, z), self.M(b, z))),
            self.U(z, self.equivalence(self.M(z, a), self.M(z, b))),
        )


def check(radix, extent=7):
    c = CodedCalculus(radix)
    assert c.value(0) is True
    assert c.value(1) is False
    counts = {key: 0 for key in ("head1", "head2", "head6", "gamma", "rho8", "guarded_gate", "head3", "head4")}
    max_bits = 0
    for a, b in product(range(extent), repeat=2):
        assert c.value(c.head1(a, b))
        counts["head1"] += 1
    for b in range(5000):
        assert c.value(c.gamma(b))
        counts["gamma"] += 1
    for a, b, d in product(range(extent), repeat=3):
        for key in ("head2", "head6"):
            assert c.value(getattr(c, key)(a, b, d))
            counts[key] += 1
        if radix == 4:
            for key in ("head3", "head4"):
                assert c.value(getattr(c, key)(a, b, d))
                counts[key] += 1
        if d != a and d != b:
            parts = c.gate_parts(a, b, d)
            assert [c.value(x) for x in parts] == [True, True, True, False, True, True]
            max_bits = max(max_bits, max(x.bit_length() for x in parts))
            counts["guarded_gate"] += 1
    for a, b, h, u in product(range(extent), repeat=4):
        assert c.value(c.rho8(a, b, h, u))
        counts["rho8"] += 1
    witness = c.exists(1, c.neighborhood_equality(0, 1, 2))
    assert c.value(witness) is False
    if radix == 4:
        assert all(not c.value(c.head5(a, b)) for a, b in product(range(extent), repeat=2))
    return {
        "radix": radix,
        "extent": extent,
        "checked_instances": counts,
        "truth_value": int(c.value(0)),
        "contradiction_value": int(c.value(1)),
        "neighborhood_equality_witness_value": int(c.value(witness)),
        "largest_gate_code_bits": max_bits,
        "status": "all exact finite checks passed; unbounded result is proved in the supplement",
    }


if __name__ == "__main__":
    def implies(a, b):
        return not a or b
    truth_rows = 0
    for a, b, c, u in product((False, True), repeat=4):
        assert implies(implies(implies(c, u), a), implies(implies(a, c), implies(b, c)))
        truth_rows += 1
    result = {
        "kind": "countermodel verification, not a consistency-machine construction",
        "rho8_truth_table_rows": truth_rows,
        "models": [check(3), check(4)],
    }
    Path(__file__).with_name("boolean_obstruction_receipt.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))

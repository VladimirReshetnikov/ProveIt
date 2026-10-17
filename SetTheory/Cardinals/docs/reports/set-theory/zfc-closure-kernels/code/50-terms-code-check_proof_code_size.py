#!/usr/bin/env python3
"""Finite replay of an ordinary proof-code size theorem, not a Lean proof.

Mirrors Code254Proof.{node,RawProof.quote,decodeStep,decodeFuel} at ProveIt
fab89c5d26b81cd2ccab2ee5d213ff23725c7726.  It intentionally does not evaluate
the enormous numerical rho/bundle formulas or assert proof validity.
"""
from __future__ import annotations

import argparse
import json
import math
import random
from dataclasses import dataclass


def pair(a: int, b: int) -> int:
    return (a + b) * (a + b + 1) // 2 + b


def unpair(n: int) -> tuple[int, int]:
    s = (math.isqrt(8 * n + 1) - 1) // 2
    b = n - s * (s + 1) // 2
    return s - b, b


@dataclass(frozen=True)
class Raw:
    tag: int
    fields: tuple[int, ...] = ()
    children: tuple[Raw, ...] = ()

    def size(self) -> int:
        return 1 + sum(x.size() for x in self.children)

    def height(self) -> int:
        return 1 + max((x.height() for x in self.children), default=0)

    def field_weight(self) -> int:
        return math.prod(v + 1 for v in self.fields) * math.prod(
            x.field_weight() for x in self.children)

    def literal_bits(self) -> int:
        """Four-bit tags followed by gamma(v+1) for each numeric field."""
        return (4 + sum(2 * (v + 1).bit_length() - 1 for v in self.fields)
                + sum(x.literal_bits() for x in self.children))

    def quote(self) -> int:
        if self.tag == 0:
            payload = 0
        elif self.tag == 1:
            payload = pair(self.fields[0], pair(*(x.quote() for x in self.children)))
        elif self.tag == 2:
            payload = pair(self.fields[0], self.children[0].quote())
        else:
            payload = self.fields[-1]
            for a in self.fields[-2::-1]:
                payload = pair(a, payload)
        return 12 * payload + self.tag + 1


def decode_fuel(fuel: int, code: int) -> Raw | None:
    if not fuel or not code:
        return None
    tag, payload = (code - 1) % 12, (code - 1) // 12
    a, tail = unpair(payload)
    b, c = unpair(tail)
    if tag == 0:
        return Raw(0) if payload == 0 else None
    if tag == 1:
        p = decode_fuel(fuel - 1, b)
        if p is None:
            return None
        q = decode_fuel(fuel - 1, c)
        return None if q is None else Raw(1, (a,), (p, q))
    if tag == 2:
        p = decode_fuel(fuel - 1, tail)
        return None if p is None else Raw(2, (a,), (p,))
    if tag in (3, 8):
        return Raw(tag, (a, tail))
    if tag == 10:
        e, f = unpair(c)
        return Raw(tag, (a, b, e, f))
    return Raw(tag, (a, b, c))


def small_fuel(code: int) -> int:
    """floor(log2(bitlength(code)+1)), with zero sent to zero."""
    return (code.bit_length() + 1).bit_length() - 1


def random_raw(rng: random.Random, budget: int) -> Raw:
    choices = list(range(3, 12)) + [0]
    if budget >= 2:
        choices.append(2)
    if budget >= 3:
        choices.append(1)
    tag = rng.choice(choices)
    atom = lambda: rng.randrange(16)
    if tag == 0:
        return Raw(0)
    if tag == 1:
        left = rng.randrange(1, budget - 1)
        return Raw(1, (atom(),),
                   (random_raw(rng, left), random_raw(rng, budget - 1 - left)))
    if tag == 2:
        return Raw(2, (atom(),), (random_raw(rng, budget - 1),))
    arity = 2 if tag in (3, 8) else 4 if tag == 10 else 3
    return Raw(tag, tuple(atom() for _ in range(arity)))


def expression_degree_audit() -> dict:
    """Exponents for U(w(x,y)) <= R**(2 max(e_x,e_y)+4), R>=2.

    This is a symbolic reading of the literal fixed templates, not evaluation
    of their natural-number values.  All input fields use exponent one.
    """
    w = lambda a, b: 2 * max(a, b) + 4
    F = 1
    wn = lambda a: w(a, F)
    wa = lambda a, b: wn(w(a, wn(b)))
    wex = lambda a, b: wn(w(a, wn(b)))
    a = b = c = u = 1
    rho = [
        wex(a, w(a, b)),
        w(w(a, w(b, c)), w(w(a, b), w(a, c))),
        w(w(a, b), w(w(c, a), w(c, b))),
        w(w(a, w(b, c)), w(b, w(a, c))),
        w(w(c, a), w(w(c, b), w(a, b))),
        w(wex(a, w(a, b)), b),
        w(w(c, a), w(w(c, b), w(a, b))),
        w(w(w(c, u), a), w(w(a, c), w(b, c))),
    ]
    C = wex(b, wa(
        w(a, w(w(a, b), wa(
            wex(c, wa(w(b, w(w(c, w(w(c, b), w(c, a))), w(b, c))), w(c, b))),
            w(c, w(w(c, a), w(c, b)))))), w(c, b)))
    G = wex(c, wa(
        w(a, w(w(a, b), w(b, w(c, wex(b, wa(c, w(b, c))))))),
        w(b, w(w(b, c), wex(a, c)))))
    bundle = wa(wa(C, G), wa(w(w(a, b), w(c, w(a, b))),
                             w(w(a, b), w(c, w(a, b)))))
    return {"rho_exponents": rho, "container_exponent": C,
            "collection_exponent": G, "bundle_exponent": bundle,
            "chosen_uniform_D": 1 << 28,
            "status": "Symbolic finite-template bound; not a measured runtime constant."}


def run(limit: int, samples: int, seed: int) -> dict:
    parsed = 0
    max_size = 0
    tag_counts = [0] * 12
    for code in range(limit):
        old = decode_fuel(code + 1, code)
        fast = decode_fuel(small_fuel(code), code)
        assert old == fast, ("fuel equivalence", code)
        if old is not None:
            parsed += 1
            size = old.size()
            max_size = max(max_size, size)
            tag_counts[old.tag] += 1
            assert old.quote() == code, ("reverse quote", code)
            assert (1 << size) <= code + 1, ("node bound", code)
            assert (1 << size) * old.field_weight() <= code + 1
            assert (1 << ((1 << old.height()) - 1)) <= code + 1
            assert old.literal_bits() <= 8 * ((code + 1).bit_length() - 1)
    rng = random.Random(seed)
    max_random_bits = max_random_nodes = 0
    for _ in range(samples):
        p = random_raw(rng, rng.randrange(1, 25))
        c = p.quote()
        assert (1 << p.size()) <= c + 1
        assert (1 << p.size()) * p.field_weight() <= c + 1
        assert (1 << ((1 << p.height()) - 1)) <= c + 1
        assert p.literal_bits() <= 8 * ((c + 1).bit_length() - 1)
        assert p.height() <= small_fuel(c)
        assert decode_fuel(small_fuel(c), c) == p
        assert decode_fuel(p.height(), c) == p
        if p.height() > 1:
            assert decode_fuel(p.height() - 1, c) is None
        max_random_bits = max(max_random_bits, c.bit_length())
        max_random_nodes = max(max_random_nodes, p.size())
    for a in range(100):
        for b in range(100):
            assert pair(a, b) + 1 >= (a + 1) * (b + 1)
            assert 12 * pair(a, b) + 3 >= 2 * (b + 1)**2
            assert 12 * pair(a, b) + 4 >= 4 * max(a + 1, b + 1)**2
            assert 4 * pair(a, b) + 3 <= 16 * max(a + 1, b + 1)**2
    return {
        "source_pin": "fab89c5d26b81cd2ccab2ee5d213ff23725c7726",
        "all_code_range": [0, limit], "range_end_exclusive": True,
        "parsed_codes": parsed, "maximum_parsed_tree_nodes": max_size,
        "parsed_root_tag_counts": tag_counts,
        "random_raw_trees": samples, "random_seed": seed,
        "maximum_random_code_bits": max_random_bits,
        "maximum_random_tree_nodes": max_random_nodes,
        "pair_inequality_pairs": 10000,
        "expression_audit": expression_degree_audit(),
        "status": "PASS",
        "scope": "Finite parser/quotation replay, not proof validity, a Lean theorem, or a PA internalization."
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--limit", type=int, default=200000)
    parser.add_argument("--samples", type=int, default=10000)
    parser.add_argument("--seed", type=int, default=20261017)
    args = parser.parse_args()
    print(json.dumps(run(args.limit, args.samples, args.seed), indent=2))

#!/usr/bin/env python3
"""Fresh finite checker for the explicitly specified reversible binary clock.
No upstream code is imported or executed. Uses only the Python standard library.
The full-shift theorem is proved in candidate-specification.md; finite tests
here are supplementary, not an exhaustive certificate for all configurations.
"""
from __future__ import annotations
import argparse
import hashlib
import itertools
import json
import math
import random
from dataclasses import dataclass
from pathlib import Path

@dataclass(frozen=True)
class Rule:
    name: str
    e0: tuple[int, ...]
    e1: tuple[int, ...]
    lo: int
    hi: int

A = (
    Rule("AR", (0, 1), (0, 2), -4, 6),
    Rule("AL", (0, 4), (0, 3), -4, 8),
    Rule("AC", (0, 1, 6), (-1, 2, 7), -5, 8),
)
B = (
    Rule("BR", (0, 2), (1, 2), -4, 6),
    Rule("BL", (0, 3), (-1, 3), -5, 7),
    Rule("BC", (-5, 0, 3), (-5, 0, 1), -5, 8),
)
WRITE_RADIUS = 7
READ_RADIUS = 8
H = 2 * (WRITE_RADIUS + READ_RADIUS)

def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)

def raw(support: frozenset[int], rules: tuple[Rule, ...]):
    """Return (row index, anchor) -> endpoint side; exact finite discovery."""
    out = {}
    for i, rule in enumerate(rules):
        offsets = set(rule.e0) | set(rule.e1)
        # Every endpoint is nonempty, so these are all possible raw anchors.
        anchors = {z - u for z in support for u in offsets}
        for x in anchors:
            local = tuple(sorted(z-x for z in support
                                 if x+rule.lo <= z <= x+rule.hi))
            if local == rule.e0:
                out[i, x] = 0
            elif local == rule.e1:
                out[i, x] = 1
    return out

def swap(support, rules, key, side):
    i, x = key
    rule = rules[i]
    old, new = (rule.e0, rule.e1) if side == 0 else (rule.e1, rule.e0)
    require(all(x+u in support for u in old), "swap missing endpoint")
    return frozenset((set(support) - {x+u for u in old})
                     | {x+u for u in new})

def block_trace(support, rules):
    keys = raw(support, rules)
    selected = {}
    for key, side in keys.items():
        _, x = key
        if any(other != key and abs(other[1]-x) <= H for other in keys):
            continue
        hypothetical = swap(support, rules, key, side)
        after = raw(hypothetical, rules)
        before_local = {k for k in keys if abs(k[1]-x) <= 15}
        after_local = {k for k in after if abs(k[1]-x) <= 15}
        if before_local == after_local:
            selected[key] = side
    result = support
    for key, side in selected.items():
        result = swap(result, rules, key, side)
    return result, keys, selected

def block(support, rules):
    return block_trace(support, rules)[0]

def forward(support):
    return block(block(support, A), B)

def backward(support):
    return block(block(support, B), A)

def section(d):
    return frozenset((0, 5, 6, d))

def phase(d, s):
    ell = 2*d-22
    require(d >= 13 and 0 <= s <= ell, "phase parameters")
    if s == ell:
        return section(d+1)
    if s <= d-11:
        return frozenset((0, 5+s, 6+s, d))
    return frozenset((0, 2*d-18-s, 2*d-14-s, d+1))

def hit(support):
    return all((z in support) == (z in (0, 5, 6)) for z in range(7))

def check_block(support, rules):
    result, keys, selected = block_trace(support, rules)
    repeated, result_keys, result_selected = block_trace(result, rules)
    require(len(result) == len(support), "mass conservation")
    require(repeated == support, "block involution")
    require(set(result_keys) == set(keys), "raw key preservation")
    require(set(result_selected) == set(selected), "selection preservation")
    return len(selected), sum(1 for k in keys
        if not any(j != k and abs(j[1]-k[1]) <= H for j in keys)) - len(selected)

def run(args):
    for rules in (A, B):
        for q in rules:
            require(len(q.e0) == len(q.e1), "equal endpoint weights")
            require(q.e0 != q.e1, "distinct endpoints")
            require(-READ_RADIUS <= q.lo <= q.hi <= READ_RADIUS, "read bound")
            for e in (q.e0, q.e1):
                require(tuple(sorted(set(e))) == e, "canonical support")
                require(all(q.lo <= z <= q.hi for z in e), "endpoint in read")
                require(all(abs(z) <= WRITE_RADIUS for z in e), "write bound")

    orbit_checks = 0
    for d in range(13, args.max_d+1):
        state = section(d)
        for s in range(2*d-22):
            require(state == phase(d, s), "complete phase formula")
            require(hit(state) == (s == 0), "anchored hit exclusivity")
            middle, ak, ae = block_trace(state, A)
            result, bk, be = block_trace(middle, B)
            require(len(ak) == len(ae) == len(bk) == len(be) == 1,
                    "one intended key at each legal half-step")
            require(block(middle, A) == state, "legal A inverse")
            require(block(result, B) == middle, "legal B inverse")
            require(result == phase(d, s+1), "one-step phase formula")
            state = result
            orbit_checks += 1
        require(state == section(d+1), "cycle endpoint")

    large_checks = 0
    for d in (13, 14, 100, 10**10, 10**40, 10**80):
        ell = 2*d-22
        tests = {0, 1, d-12, d-11, d-10, d-9, ell-2, ell-1}
        for s in sorted(x for x in tests if 0 <= x < ell):
            state = phase(d, s)
            require(forward(state) == phase(d, s+1), "large-integer phase")
            require(backward(forward(state)) == state, "large inverse")
            require(hit(state) == (s == 0), "large hit exclusivity")
            large_checks += 1
    for d in (13, 14, 10**30):
        for k in (0, 1, 2, 10**40):
            tk = k*k+(2*d-23)*k
            next_t = (k+1)**2+(2*d-23)*(k+1)
            require(next_t-tk == 2*(d+k)-22, "quadratic increments")

    finite_tests = changed_blocks = multi_selected = rejected_prospective = 0
    for mass in range(args.max_mass+1):
        for positions in itertools.combinations(range(args.support_width), mass):
            support = frozenset(positions)
            for rules in (A, B):
                n, rejected = check_block(support, rules)
                changed_blocks += bool(n)
                multi_selected += n > 1
                rejected_prospective += rejected
            finite_tests += 1

    rng = random.Random(20261004)
    random_tests = 0
    for trial in range(args.random_trials):
        if trial % 2:
            # Independent sparse packets ensure genuinely parallel selections.
            occupied = set()
            for j in range(rng.randrange(1, 9)):
                q = rng.choice(A+B)
                endpoint = rng.choice((q.e0, q.e1))
                base = 70*j + rng.randrange(-5, 6)
                occupied.update(base+u for u in endpoint)
            support = frozenset(occupied)
        else:
            mass = rng.randrange(0, 25)
            support = frozenset(rng.sample(range(-100, 101), mass))
        for rules in (A, B):
            n, rejected = check_block(support, rules)
            changed_blocks += bool(n)
            multi_selected += n > 1
            rejected_prospective += rejected
        require(backward(forward(support)) == support, "composed inverse")
        random_tests += 1

    require(changed_blocks > 0, "nonvacuous finite test")
    require(multi_selected > 0, "nonvacuous simultaneous test")
    receipt = {
        "status": "pass",
        "scope": "finite tests supplement the separate full-shift proof",
        "checker_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "block_write_radius": WRITE_RADIUS,
        "block_read_radius": READ_RADIUS,
        "isolation_distance": H,
        "block_CA_radius_bound": 45,
        "composite_CA_radius_bound": 90,
        "complete_orbit_steps": orbit_checks,
        "legal_half_steps": 2*orbit_checks,
        "large_integer_boundary_steps": large_checks,
        "max_large_integer_gap": str(10**80),
        "exhaustive_support_interval": [0, args.support_width-1],
        "exhaustive_max_mass": args.max_mass,
        "exhaustive_finite_inputs": finite_tests,
        "seeded_malformed_and_parallel_inputs": random_tests,
        "changed_block_tests": changed_blocks,
        "multiple_simultaneous_selection_tests": multi_selected,
        "prospective_rejections_observed": rejected_prospective,
        "initial_support_minimal_parameter": [0,5,6,13],
        "anchored_pattern_interval": [0,6],
        "anchored_pattern": "1000011",
        "hit_times": "k^2+(2*d-23)*k for d>=13 and k>=0",
    }
    result = json.dumps(receipt, indent=2, sort_keys=True)
    if args.output:
        Path(args.output).write_text(result+"\n")
    print(result)

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-d", type=int, default=100)
    parser.add_argument("--support-width", type=int, default=18)
    parser.add_argument("--max-mass", type=int, default=5)
    parser.add_argument("--random-trials", type=int, default=1000)
    parser.add_argument("--output", type=str)
    run(parser.parse_args())


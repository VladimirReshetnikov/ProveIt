#!/usr/bin/env python3
"""Executable finite controls for a single-loop affine Horn certificate.

This is a source-level theorem and a finite regression suite.  It is not a
materialized fixed-dimensional consistency polynomial.  No ZFC refutation is
assumed or searched for.  The tests use small artificial Horn calculi.
"""
from __future__ import annotations
from dataclasses import dataclass
from itertools import combinations, combinations_with_replacement
from math import gcd, lcm, prod
import json
from pathlib import Path


@dataclass(frozen=True)
class Rule:
    p: int
    q: int
    c: int


TRUTH = Rule(0, 0, 0)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def closure_and_parents(rules: tuple[Rule, ...]) -> dict[int, Rule | None]:
    parents: dict[int, Rule | None] = {0: None}
    while True:
        new = [r for r in rules if r.p in parents and r.q in parents
               and r.c not in parents]
        if not new:
            return parents
        for r in new:
            if r.c not in parents:
                parents[r.c] = r


def proof_expansion(parents: dict[int, Rule | None], target: int = 1) -> list[Rule]:
    if target == 0:
        return []
    r = parents[target]
    require(r is not None, "nonzero derivable target needs a rule")
    return [r] + proof_expansion(parents, r.p) + proof_expansion(parents, r.q)


def crt(residues: list[int], moduli: list[int]) -> int:
    x, modulus = 0, 1
    for a, m in zip(residues, moduli):
        require(gcd(modulus, m) == 1, "CRT moduli must be coprime")
        x += modulus * (((a - x) * pow(modulus, -1, m)) % m)
        modulus *= m
        require(0 <= x < modulus, "CRT canonical interval")
    return x


def build_certificate(rules: tuple[Rule, ...]) -> dict | None:
    parents = closure_and_parents(rules)
    if 1 not in parents:
        return None
    steps = proof_expansion(parents)
    horizon = max(1, len(steps), *(r.p + r.q + r.c for r in steps))
    steps += [TRUTH] * (horizon - len(steps))
    common = lcm(*range(1, horizon + 1))
    states = [1 + common]
    for r in steps:
        numerator = states[-1] * (1 + common * r.p) * (1 + common * r.q)
        denominator = 1 + common * r.c
        require(numerator % denominator == 0, "proof expansion must divide exactly")
        states.append(numerator // denominator)
    require(states[-1] == 1, "all proof obligations must discharge")
    # beta's scale is deliberately different from the common multiple.
    beta_scale = common * (max(states) + 1)
    moduli = [1 + (i + 1) * beta_scale for i in range(horizon + 1)]
    beta_word = crt(states, moduli)
    return {
        "T": horizon, "M0": common - 1, "x": beta_word, "y": beta_scale,
        "states": states,
        "steps": [r.__dict__ for r in steps],
        "divisibility_quotients": [common // (i + 1) for i in range(horizon)],
    }


def check_certificate(rules: tuple[Rule, ...], cert: dict) -> bool:
    t, common = cert["T"], cert["M0"] + 1
    if t < 0 or common < 1 or cert["x"] < 0 or cert["y"] < 0:
        return False
    if len(cert["steps"]) != t or len(cert["divisibility_quotients"]) != t:
        return False
    beta = lambda i: cert["x"] % (1 + (i + 1) * cert["y"])
    if beta(0) != common + 1 or beta(t) != 1:
        return False
    available = set(rules) | {TRUTH}
    for i, data in enumerate(cert["steps"]):
        r = Rule(**data)
        if r not in available or min(r.p, r.q, r.c) < 0 or r.p + r.q + r.c > t:
            return False
        k = cert["divisibility_quotients"][i]
        if k < 0 or common != (i + 1) * k:
            return False
        if beta(i + 1) * (1 + common * r.c) != (
                beta(i) * (1 + common * r.p) * (1 + common * r.q)):
            return False
    return True


def main() -> None:
    labels = range(3)
    universe = [Rule(p, q, c) for p, q in combinations_with_replacement(labels, 2)
                for c in labels]
    systems = positive = beta_digits = rejected_mutations = 0
    for count in range(4):
        for rules in combinations(universe, count):
            systems += 1
            cert = build_certificate(rules)
            if cert is None:
                continue
            positive += 1
            require(check_certificate(rules, cert), "constructed certificate rejected")
            beta_digits += cert["T"] + 1
            broken = dict(cert)
            broken["divisibility_quotients"] = cert["divisibility_quotients"].copy()
            broken["divisibility_quotients"][-1] += 1
            require(not check_certificate(rules, broken), "wrong quotient accepted")
            rejected_mutations += 1

    # A counterfeit flow exists if one omits the common-multiple checks.
    # Target1 is not derivable from axiom3 and rule1->0, yet with M=1:
    #    S:2 -> 4 ->1 ->1
    # satisfies the raw affine updates and all label bounds with T=3.
    bad_rules = (Rule(1, 0, 0), Rule(0, 0, 3), TRUTH)
    require(1 not in closure_and_parents(bad_rules), "negative control is derivable")
    states, common = [2, 4, 1, 1], 1
    for i, r in enumerate(bad_rules):
        require(states[i + 1] * (1 + common * r.c) ==
                states[i] * (1 + common * r.p) * (1 + common * r.q),
                "counterfeit raw flow identity")
    require(common % 2 != 0, "common-multiple condition rejects counterfeit")
    require(2 != 1, "T=0 cannot meet the two endpoints for any M>=1")

    sample_rules = (Rule(0, 0, 2), Rule(2, 2, 1))
    sample = build_certificate(sample_rules)
    require(sample is not None and check_certificate(sample_rules, sample), "sample failed")
    result = {
        "status": "pass", "systems": systems,
        "derivable_systems_certified": positive, "verified_beta_digits": beta_digits,
        "rejected_quotient_mutations": rejected_mutations,
        "negative_controls": ["M=1 multiplicative collision", "T=0 endpoints"],
        "sample": sample,
        "scope": "finite regressions of the source-level theorem; no full Diophantine compilation",
    }
    Path(__file__).with_name("SINGLE_LOOP_CHECKS.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k:v for k,v in result.items() if k != "sample"}, indent=2))


if __name__ == "__main__":
    main()

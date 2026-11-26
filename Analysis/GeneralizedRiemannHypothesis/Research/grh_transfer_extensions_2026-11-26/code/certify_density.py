#!/usr/bin/env python3
"""Exact density-gap certificate, with two independent finite verifiers.

The 102-element replacement is inherited from the ProveIt incoming packet
mcnew_density_and_grh_transfers.zip (blob 8c44dba4c1b86207e9bb1ff6d88f9e943da631d0).
This script sharpens its tax and certified local gain. All proof arithmetic
is integral or rational. No numerical optimizer is trusted.

Run: python3 code/certify_density.py
The output JSON contains an independently replayable branch/dual certificate.
"""
from fractions import Fraction as Q
from itertools import combinations
from math import isqrt, lcm
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[1]
N = 10**6
TAX = Q(824341, 10**7)
GAIN = Q(237, 100000)
UNIT = 10**18

def smooth_values():
    vals = [1]
    for p in (2, 3, 5):
        out = []
        for a in vals:
            while a <= N:
                out.append(a)
                a *= p
        vals = out
    return sorted(vals)

def rational_edges(vals):
    """Endpoint enumeration, independent of the direct verifier below."""
    pos = {n: i for i, n in enumerate(vals)}
    out = []
    for i, j in combinations(range(len(vals)), 2):
        b = isqrt(vals[i] * vals[j])
        if b * b == vals[i] * vals[j] and b in pos:
            out.append((i, pos[b], j))
    return out

def build_cover_proof(edges, weights, required):
    order = sorted(range(len(edges)), key=lambda e: min(weights[v] for v in edges[e]), reverse=True)
    visits = 0
    def prove(active, need):
        nonlocal visits
        visits += 1
        if need <= 0:
            return {"paid": True}
        capacity = list(weights)
        total, dual = 0, []
        for i in active:
            edge = edges[i]
            mass = min(capacity[v] for v in edge)
            if mass:
                for v in edge:
                    capacity[v] -= mass
                total += mass
                dual.append([i, mass])
                if total >= need:
                    return {"dual": dual}
        if not active:
            raise AssertionError("requested gain is not certified")
        i = active[0]
        return {"edge": i, "children": [
            prove([j for j in active if v not in edges[j]], need - weights[v])
            for v in edges[i]
        ]}
    return prove(order, required), visits

def replay_cover_proof(proof, edges, weights, required):
    visits = 0
    def visit(node, removed, need):
        nonlocal visits
        visits += 1
        if "paid" in node:
            assert node == {"paid": True} and need <= 0
            return
        if "dual" in node:
            incident = [0] * len(weights)
            total = 0
            for i, mass in node["dual"]:
                assert isinstance(mass, int) and mass > 0
                assert 0 <= i < len(edges)
                assert all(v not in removed for v in edges[i])
                total += mass
                for v in edges[i]:
                    incident[v] += mass
            assert all(a <= b for a, b in zip(incident, weights))
            assert total >= need
            return
        assert set(node) == {"edge", "children"}
        edge = edges[node["edge"]]
        assert all(v not in removed for v in edge)
        assert len(node["children"]) == 3
        for v, child in zip(edge, node["children"]):
            visit(child, removed | {v}, need - weights[v])
    visit(proof, set(), required)
    return visits

def direct_independent_set_check(vals, weights, threshold):
    """Independent enumeration using first and middle terms, not covers."""
    pos = {v: i for i, v in enumerate(vals)}
    implications = [[] for _ in vals]
    for j, middle in enumerate(vals):
        for i in range(j):
            last, rem = divmod(middle * middle, vals[i])
            if rem == 0 and last in pos:
                implications[j].append((1 << i, 1 << pos[last]))
    visits = 0
    def search(free, chosen, upper):
        nonlocal visits
        visits += 1
        if upper <= threshold:
            return
        assert free, "admissible subset violates threshold"
        bit = free & -free
        j = bit.bit_length() - 1
        free ^= bit
        search(free, chosen, upper - weights[j])
        forbidden = 0
        for first, last in implications[j]:
            if chosen & first:
                forbidden |= last
        forbidden &= free
        free ^= forbidden
        while forbidden:
            bit_last = forbidden & -forbidden
            upper -= weights[bit_last.bit_length() - 1]
            forbidden ^= bit_last
        search(free, chosen | bit, upper)
    search((1 << len(vals)) - 1, 0, sum(weights))
    return visits

def primes_up_to(limit):
    live = bytearray([1]) * (limit + 1)
    live[:2] = bytes(2)
    for p in range(2, isqrt(limit) + 1):
        if live[p]:
            live[p*p::p] = bytes((limit - p*p) // p + 1)
    return [p for p in range(2, limit + 1) if live[p]]

def global_gap():
    end = 2_000_000
    primes = primes_up_to(end)
    tail = sum((UNIT + p*p - 1) // (p*p) for p in primes) + (UNIT + end - 1) // end
    product = UNIT
    best = None
    for p in primes:
        if p > 100000:
            break
        tail -= (UNIT + p*p - 1) // (p*p)
        product = product * (p - 1) // p
        if p < 5:
            continue
        gap = product * GAIN.numerator // GAIN.denominator - tail
        if best is None or gap > best["gap_numerator"]:
            best = {"Y": p, "sieve_limit": end, "denominator": UNIT,
                    "product_lower_numerator": product,
                    "prime_tail_upper_numerator": tail,
                    "gap_numerator": gap}
    return best

def main():
    vals = smooth_values()
    B = set(map(int, (ROOT / 'data/density_replacement.txt').read_text().split()))
    assert len(vals) == 507 and len(B) == 102 and B <= set(vals)
    for a in B:
        for r in range(2, isqrt(N // a) + 1):
            assert a*r not in B or a*r*r not in B
    # The integral tail bound is strict; rounding the finite sum upwards
    # proves sum_{r not 5-smooth} r^-2 < TAX, with no floating arithmetic.
    M = 10000
    zeta2_upper = sum((UNIT + n*n - 1) // (n*n) for n in range(1, M + 1)) + UNIT // M
    tax_upper = Q(zeta2_upper, UNIT) - Q(25, 16)
    assert tax_upper < TAX
    weight_B = sum(Q(1, n) for n in B)
    tail = Q(15, 4) - sum(Q(1, n) for n in vals)
    scale = lcm(TAX.denominator, GAIN.denominator) * lcm(*vals)
    weights = [(1 - TAX if n in B else Q(1)) * Q(scale, n) for n in vals]
    assert all(w.denominator == 1 and w > 0 for w in weights)
    weights = [int(w) for w in weights]
    threshold_q = scale * ((1 - TAX) * weight_B - tail - GAIN)
    threshold = threshold_q.numerator // threshold_q.denominator
    required = sum(weights) - threshold
    edges = rational_edges(vals)
    proof, build_visits = build_cover_proof(edges, weights, required)
    replay_visits = replay_cover_proof(proof, edges, weights, required)
    direct_visits = direct_independent_set_check(vals, weights, threshold)
    gap = global_gap()
    assert gap["gap_numerator"] > 134 * UNIT // 1_000_000
    out = {"N": N, "tax": str(TAX), "gain": str(GAIN),
           "tax_rational_upper": str(tax_upper), "vertices": len(vals),
           "replacement_size": len(B), "rational_edges": len(edges),
           "replacement_weight": str(weight_B), "smooth_tail": str(tail),
           "weight_scale": scale, "independent_set_threshold": threshold,
           "required_cover_weight": required, "cover_build_nodes": build_visits,
           "cover_replay_nodes": replay_visits, "direct_search_nodes": direct_visits,
           "global_gap": gap}
    (ROOT / 'data/density_exchange_certificate.json').write_text(json.dumps(proof, separators=(',', ':')) + '\n')
    (ROOT / 'data/density_results.json').write_text(json.dumps(out, indent=2) + '\n')
    print(json.dumps(out, indent=2))

if __name__ == '__main__':
    main()

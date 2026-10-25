#!/usr/bin/env python3
"""A quadratic, cofinal beta spacing replacing the odd-square multiplier.

This checks only literal finite algebra and finite illustrative witnesses.
The unbounded number-theoretic proof is in beta_two_squares_proof.md.
"""
import argparse
import copy
import hashlib
import json
import math
from pathlib import Path


def canonical(obj):
    return (json.dumps(obj, sort_keys=True, separators=(",", ":")) + "\n").encode()


def normalize(terms):
    out = {}
    for c, mon in terms:
        key = tuple(sorted(mon))
        out[key] = out.get(key, 0) + c
    return {m: c for m, c in out.items() if c}


def as_terms(poly):
    return [[c, list(m)] for m, c in sorted(poly.items())]


def expand(eq):
    terms = {}
    for row in eq["residuals"]:
        p = normalize(row["terms"])
        for m, c in p.items():
            for n, d in p.items():
                key = tuple(sorted(m + n))
                terms[key] = terms.get(key, 0) + c * d
    return {m: c for m, c in terms.items() if c}


def changed_equation(source):
    """The selected parent has no shears involving this two-row block."""
    eq = copy.deepcopy(source)
    names = {v["name"]: i for i, v in enumerate(eq["variables"])}
    y, F, R, u, v = [names[n] for n in (
        "y", "crt.growth_majorant_F", "mul.1",
        "beta.odd_square_multiplier", "beta.odd_square_root_half")]
    labels = {row["label"]: i for i, row in enumerate(eq["residuals"])}
    product = labels["bootstrap.beta_base_square_product"]
    square = labels["beta.odd_square_multiplier"]
    expected = {
        product: {(): -1, (y,): 1, tuple(sorted((F, u))): -1},
        square: {(): -1, (u,): 1, (v,): -4, (v, v): -4},
    }
    for index, p in expected.items():
        if normalize(eq["residuals"][index]["terms"]) != p:
            raise ValueError("The supplied beta block is not the pinned translated block")
    for j, row in enumerate(eq["residuals"]):
        if j not in expected and any(u in m or v in m for _, m in row["terms"]):
            raise ValueError("A supposedly private beta witness occurs outside its block")
    if not any(normalize(row["terms"]) == {(R,): 1, (F, F): -1}
               for row in eq["residuals"]):
        raise ValueError("The inherited R=F^2 graph is missing")
    eq["variables"][u] = {"name": "beta.square_u", "kind": "signed_witness"}
    eq["variables"][v] = {"name": "beta.square_v", "kind": "signed_witness"}
    new_row = {"label": "bootstrap.beta_base_two_squares", "terms": as_terms({
        (): -1, (y,): 1, (R,): -1, (u, u): -1, (v, v): -1})}
    eq["residuals"][product] = new_row
    del eq["residuals"][square]
    eq["variant"] += ":cofinal_beta_two_squares"
    change = {
        "schema": "beta_two_squares_mutation_v1",
        "parent_sha256_canonical": hashlib.sha256(canonical(source)).hexdigest(),
        "old_product_row": product,
        "old_square_row": square,
        "new_row": new_row,
        "indices": {"stored_y": y, "F": F, "R": R, "u": u, "v": v},
        "semantic_y": "stored_y - 1",
        "semantic_replacement": "y = F^2 + u^2 + v^2",
        "zero_set_relationship": "Both are equivalent to finite C222 refutability; no coordinate bijection is asserted.",
    }
    return eq, change


def primes_to(n):
    primes = []
    for p in range(2, n + 1):
        if all(p % q for q in primes if q * q <= p):
            primes.append(p)
    return primes


def v_factorial(t, p):
    a, n = 0, t
    while n:
        n //= p
        a += n
    return a


def solve_sum_minus_one(p, exponent):
    """Hensel lift a nonsingular solution a^2+b^2=-1 mod p^exponent."""
    if p <= 2 or exponent < 1:
        raise ValueError("An odd prime and positive exponent are required")
    # Pigeonhole: squares and -1 minus squares each have (p+1)/2 residues.
    squares = {a * a % p: a for a in range((p + 1) // 2)}
    pair = None
    for b in range((p + 1) // 2):
        a = squares.get((-1 - b * b) % p)
        if a is not None:
            pair = [a, b]
            break
    if pair is None:
        raise ArithmeticError("The finite-field pigeonhole construction failed")
    a, b = pair
    pivot = 0 if a % p else 1
    modulus = p
    for _ in range(1, exponent):
        error = (1 + a * a + b * b) // modulus
        coordinate = a if pivot == 0 else b
        delta = (-error * pow(2 * coordinate, -1, p)) % p
        if pivot == 0:
            a += delta * modulus
        else:
            b += delta * modulus
        modulus *= p
        if (1 + a * a + b * b) % modulus:
            raise ArithmeticError("Invalid Hensel lift")
    return a, b, modulus


def crt(residues):
    a, modulus = 0, 1
    for b, n in residues:
        correction = ((b - a) * pow(modulus, -1, n)) % n
        a += modulus * correction
        modulus *= n
    return a, modulus


def witness(t, offset=0):
    F = (2 * (t + 1)) ** t
    local = [solve_sum_minus_one(p, v_factorial(t, p))
             for p in primes_to(t) if p != 2]
    a, odd_modulus = crt([(x, m) for x, _, m in local])
    b, same_modulus = crt([(x, m) for _, x, m in local])
    if odd_modulus != same_modulus:
        raise ArithmeticError("CRT modulus disagreement")
    a += offset * odd_modulus
    u, v = F * a, F * b
    y = F * F + u * u + v * v
    fac = math.factorial(t)
    if y % fac or y <= F + 1 or y % 2:
        raise ArithmeticError("The constructed beta spacing violates the theorem")
    return {"t": t, "F": F, "u": u, "v": v, "y": y,
            "odd_modulus": odd_modulus}


def checks():
    count = 0
    # Exact arithmetic witnesses, including the minimum retained horizon.
    for t in range(16, 81):
        previous = -1
        for shift in (0, 1, 2):
            w = witness(t, shift)
            if w["y"] <= previous:
                raise ArithmeticError("Cofinal family is not increasing")
            previous = w["y"]
            count += 1
    return {"finite_witnesses": count, "horizons": [16, 80],
            "status": "passed", "scope": "Illustrations and exact finite algebra only; the theorem is unbounded."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    original = json.loads(args.source.read_text())
    equation, mutation = changed_equation(original)
    polynomial = expand(equation)
    metrics = {
        "variables": len(equation["variables"]),
        "rows": len(equation["residuals"]),
        "degree": max(map(len, polynomial)),
        "monomials": len(polynomial),
        "height": max(map(abs, polynomial.values())),
        "row_height": max(abs(c) for row in equation["residuals"] for c, _ in row["terms"]),
    }
    args.output.mkdir(parents=True, exist_ok=True)
    files = {"equation.json": equation,
             "expanded_polynomial.json": {"variables": len(equation["variables"]),
                                           "terms": as_terms(polynomial)},
             "mutation.json": mutation, "METRICS.json": metrics,
             "FINITE_CHECKS.json": checks()}
    for name, data in files.items():
        (args.output / name).write_bytes(canonical(data))
    print(json.dumps(metrics, sort_keys=True))


if __name__ == "__main__":
    main()

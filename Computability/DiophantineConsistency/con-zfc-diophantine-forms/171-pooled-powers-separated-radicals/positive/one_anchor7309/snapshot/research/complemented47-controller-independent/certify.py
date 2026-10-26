#!/usr/bin/env python3
"""Independent finite Pc3 and constant checks; Python standard library only."""
import hashlib
import json
import argparse
from math import gcd, isqrt
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
EQUATION = ROOT / "candidates/one-page-compact66-radix55/equation.tex"
PROOF = ROOT / "research/compact66-complemented-three-anchor-radix47/README.md"
HERE = Path(__file__).resolve().parent
RADIX_BITS, L, ORDER = 47, 8807, 101269
RHO, D = 1 << RADIX_BITS, RADIX_BITS * L


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def binding(path):
    raw = path.read_bytes()
    return {"path": str(path.relative_to(ROOT)), "bytes": len(raw), "sha256": sha(raw)}


def canonical(value):
    return json.dumps(value, separators=(",", ":"), sort_keys=True).encode("ascii")


def least_factor(n):
    """A returned None certifies trial division through floor(sqrt(n))."""
    require(n >= 2, "Trial-division input must be at least two")
    if n % 2 == 0:
        return None if n == 2 else 2
    for divisor in range(3, isqrt(n) + 1, 2):
        if n % divisor == 0:
            return divisor
    return None


def prime_record(n):
    factor = least_factor(n)
    return {"n": n, "prime": factor is None, "least_factor": factor,
            "trial_division_bound": isqrt(n)}


def decode_tiles():
    """Transcribe the maintained page's finite decoder and every tile row."""
    tex = EQUATION.read_text(encoding="utf-8")
    seed_part = tex.split("\\begingroup\\fontsize{7.7}{8.2}\\selectfont\\ttfamily\n", 1)[1]
    seed = seed_part.split("\\endgroup", 1)[0].replace("\\par", "").replace("\n", "")
    alphabet = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"
    require(len(seed) == 436 and all(char in alphabet for char in seed), "Invalid finite seed")
    integer = 0
    for char in seed:
        integer = 62 * integer + alphabet.index(char)
    n = integer % (1 << 636)
    targets = (integer >> 636) % (1 << 1675)
    exceptions = integer >> 2311

    def digit(value, base, index):
        return (value // base ** index) % base

    actions, sigma, tau = [], 0, 0
    for q in range(215):
        mark = digit(n, 2, 430 + q)
        flags = 14 + mark * (digit(exceptions, 16, tau) - 14)
        tau += mark
        for b in range(2):
            j = 2 * q + b
            fresh = digit(n, 2, j)
            target = fresh * (1 + sigma) + (1 - fresh) * digit(targets, 216, j - sigma)
            actions.append((target, digit(flags, 2, 2 * b), digit(flags, 2, 2 * b + 1)))
            sigma += fresh
    require(len(actions) == 430 and actions[0] == (1, 1, 1), "Action count or first target mismatch")
    states = [{u for u, v, direction in actions if direction == d} for d in (0, 1)]
    rank = {(d, q): 205 - 199 * d + sum(p < q for p in states[d])
            for d in (0, 1) for q in states[d]}
    tiles = {}

    def insert(index, tile):
        require(index not in tiles, "Duplicate tile index")
        tiles[index] = tile

    insert(0, (2, 435, 3, 1))
    insert(1, (5, 0, 0, 0))
    for j, (u, v, direction) in enumerate(actions):
        insert(j + 2, ((1 - direction) * rank.get((0, u), 0), j + 2,
                       direction * rank.get((1, u), 0), v))
    for a in (0, 1):
        for b in (0, 1):
            insert(434 - 2 * a + b, (0, 432 * a + b, 0, 432 * a + b))
    for direction in (0, 1):
        for q in sorted(states[direction]):
            r = rank[direction, q]
            for b in (0, 1):
                insert(424 + 2 * r + b, (direction * r, b, (1 - direction) * r, 2 * q + b + 2))
    for a in (0, 1):
        for b in (0, 1):
            insert(924 + 2 * a + b, (0, 432 * a + b, 0, 438))
    for index, tile in ((928, (2, 434, 2, 0)), (929, (3, 436, 4, 4)),
                        (930, (4, 436, 4, 0))):
        insert(index, tile)
    for t in (434, 435, 436):
        insert(497 + t, (1, 438, 1, t))
    for a in range(3):
        for b in range(3):
            insert(934 + 3 * a + b, (a * a, 437, b, 437))
    require(set(tiles) == set(range(943)), "Incomplete tile index coverage")
    ordered = [tiles[j] for j in range(943)]
    require(len(set(ordered)) == 943, "Duplicate tile quadruples")
    require(max(max(w, p) for w, n, p, s in ordered) == 249, "Horizontal maximum mismatch")
    require(max(max(n, s) for w, n, p, s in ordered) == 438, "Vertical maximum mismatch")
    require(all(6 <= 255 - h <= 255 for w, n, p, s in ordered for h in (w, p)), "Nonpositive complemented horizontal label")
    require(all(73 <= 511 - v <= 511 for w, n, p, s in ordered for v in (n, s)), "Nonpositive complemented vertical label")
    return seed, actions, ordered


def coefficients(tiles):
    c = [0] * 3297
    for j, (w, n, p, s) in enumerate(tiles):
        c[j] = 1 + (1 << 10) * (1 + w + (n << 8) + (p << 17) + (s << 25))
    for j in range(8):
        c[1023 + j], c[1003 + j] = 1 << (10 + j), 1 << (27 + j)
    for j in range(9):
        c[1013 + j], c[983 + j] = 1 << (18 + j), 1 << (35 + j)
    for e in (1095, 2195, 3296):
        c[e] = 1 << 44
    return c


def h_dense(modulus, c):
    """Route A: dense 3297-term Horner polynomial, then reciprocal identity."""
    r = RHO % modulus
    x = pow(r, -1, modulus)
    phi = 0
    for coefficient in reversed(c):
        phi = (phi * x + coefficient) % modulus
    k = (sum(pow(r, e, modulus) for e in (30, 62, 1100, 2201, 8849))
         + (pow(r, 4393, modulus) + pow(r, 5495, modulus)) * phi) % modulus
    b = pow(r, L, modulus)
    return {"B": b, "K": k, "H": (1 + b * k + b * b) % modulus}


def h_direct(modulus, tiles):
    """Route B: directly expand positive-exponent contributions, without c."""
    def power(e):
        return pow(2, RADIX_BITS * e, modulus)

    k = sum(power(e) for e in (30, 62, 1100, 2201, 8849))
    for center in (4393, 5495):
        for j, (w, n, p, s) in enumerate(tiles):
            weight = 1 + 1024 + 1024 * w + 262144 * n + 134217728 * p + 34359738368 * s
            k += weight * power(center - j)
        for j in range(8):
            k += (2 ** (10 + j)) * power(center - 1023 - j)
            k += (2 ** (27 + j)) * power(center - 1003 - j)
        for j in range(9):
            k += (2 ** (18 + j)) * power(center - 1013 - j)
            k += (2 ** (35 + j)) * power(center - 983 - j)
        k += (2 ** 44) * sum(power(center - e) for e in (1095, 2195, 3296))
    b = power(L)
    k %= modulus
    return {"B": b, "K": k, "H": (1 + b * k + b * b) % modulus}


def modular_record(modulus, c, tiles):
    a, b = h_dense(modulus, c), h_direct(modulus, tiles)
    require(a == b, "Independent modular routes disagree")
    return {"modulus": modulus, "dense_horner": a, "direct_expansion": b, "agree": True}


def exact_constants(c):
    """Build integers independently of modular reductions and check both masks."""
    def power(e):
        return 1 << (RADIX_BITS * e)

    support = {e for e, value in enumerate(c) if value} | {1063, 1064}
    require(len(support) == 982 and sum(value != 0 for value in c) == 980, "Support population mismatch")
    b, mu = power(L), (1 << 46) - 2
    beta = b - 1
    dc = sum(power(e) for e in (30, 62, 1100, 2201))
    dc += sum(value * (power(4393 - e) + power(5495 - e)) for e, value in enumerate(c) if value)
    k = dc + b * power(42)
    mc = beta - sum(power(e) for e in support if e != 1) - 2 * power(1063)
    core = sum(power(e) for e in range(1013, 1022))
    core += sum(power(e) for e in range(1065, 1073)) + power(2195) + power(3296)
    padding = b - power(8792) + (1 << 26) * power(7694) - power(7691)
    positive_padding = (RHO - 1) * sum(power(e) for e in range(8792, 8807))
    positive_padding += (RHO - 1) * sum(power(e) for e in range(7691, 7694)) + ((1 << 26) - 1) * power(7694)
    require(padding == positive_padding, "Positive padding sum differs from telescoped form")
    native = 4 + mu * (power(4393) + power(5495)) + core + padding
    source = 2 * b + 3 + mu * (power(4393) + power(5495)) + core - power(8792) + (1 << 26) * power(7694) - power(7691)
    require(source == native + beta, "Native-to-source shift is not exactly one beta")
    require(0 < dc < b and beta >= 31 and beta % 2 == 1 and k > 0, "Kernel scalar boxes failed")
    require(0 < mc < beta < source < 2 * beta and 0 < native < beta, "Mask scalar boxes failed")
    require(mc % 4 == 2 and native % 8 == 4, "Origin residues failed")
    require(padding.bit_count() == 872 and native.bit_count() == 982, "Padding or native population failed")
    require(mc.bit_count() == D - 982, "MC population failed")
    require(sum(c[943:]) == 4 * (1 << 44) - 1024 and max(c) == 1 << 44, "Coefficient bounds failed")
    data = {}
    for name, value in (("beta", beta), ("K", k), ("MC", mc), ("MF_source", source)):
        raw = value.to_bytes((value.bit_length() + 7) // 8, "big")
        data[name] = {"bits": value.bit_length(), "bytes": len(raw), "sha256_big_endian": sha(raw)}
    checks = {"physical_support": len(support), "nonzero_coefficients": 980,
              "coefficient_sum": sum(c), "coefficient_maximum": max(c),
              "padding_population": padding.bit_count(), "native_mask_population": native.bit_count(),
              "positive_padding_equals_telescope": True, "source_equals_native_plus_beta": True,
              "MC_population": mc.bit_count(), "scalar_boxes": True,
              "MC_mod4": mc % 4, "MF_native_mod8": native % 8,
              "total_constant_bytes": sum(row["bytes"] for row in data.values())}
    return data, checks, b, k


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="write certificate.json; default only checks exact equality")
    args = parser.parse_args()
    seed, actions, tiles = decode_tiles()
    c = coefficients(tiles)
    constants, checks, exact_b, exact_k = exact_constants(c)
    small_primes = [prime_record(n) for n in (7, 17, 23, 37, 47, 8807, 178481)]
    require(all(row["prime"] for row in small_primes), "A stated prime has a proper factor")
    require((1 << 23) - 1 == 47 * 178481 and 4403 == 7 * 17 * 37 and ORDER == 23 * 4403, "Factorization mismatch")
    require(gcd(23, 4403) == gcd(D, 23) == gcd(D, 4403) == 1, "Order gcd failed")
    orders = []
    for p, order, factors in ((47, 23, [23]), (8807, 4403, [7, 17, 37])):
        smaller = {str(factor): pow(2, order // factor, p) for factor in factors}
        require(pow(2, order, p) == 1 and all(value != 1 for value in smaller.values()) and gcd(D, order) == 1, "Exact order test failed")
        orders.append({"prime": p, "order_of_2": order, "order_of_B": order,
                       "order_prime_factors": factors, "proper_divisor_power_residues": smaller,
                       "B_squared_mod_prime": pow(2, 2 * D, p)})
    fixed = [modular_record(p, c, tiles) for p in (47, 8807)]
    require(all(row["dense_horner"]["H"] != 0 for row in fixed), "Fixed-prime H obstruction")
    probes, selected = [], None
    for m in range(5, 206):
        prime = ORDER * m + 1
        probe = {"m": m, **prime_record(prime)}
        if probe["prime"]:
            residue = pow(2, D * (prime - 1), prime * prime)
            require(residue % prime == 1, "Fermat residue failed")
            square = pow(2, 2 * D, prime)
            evaluations = modular_record(prime, c, tiles)
            probe.update({"B_squared_mod_prime": square, "B_kappa_mod_prime_squared": residue,
                          "lift_quotient_mod_prime": (residue - 1) // prime,
                          "evaluations": evaluations})
            probe["Pc3"] = prime > D and square != 1 and residue != 1 and evaluations["dense_horner"]["H"] != 0
            if probe["Pc3"]:
                selected = probe
        probes.append(probe)
        if selected is not None:
            break
    require(selected is not None, "No admissible controller found for 5 <= m <= 205")
    for row in fixed + [selected["evaluations"]]:
        modulus = row["modulus"]
        require(exact_b % modulus == row["dense_horner"]["B"], "Exact B reduction disagrees")
        require(exact_k % modulus == row["dense_horner"]["K"], "Exact K reduction disagrees")
        require((1 + exact_b * exact_k + exact_b * exact_b) % modulus == row["dense_horner"]["H"], "Exact H reduction disagrees")
    report = {"schema": "independent-complemented47-Pc3-v1", "radix_bits": RADIX_BITS,
              "L": L, "d": D, "kappa_divisor": ORDER,
              "inputs": [binding(EQUATION), binding(PROOF), binding(Path(__file__).resolve())],
              "reconstruction": {"seed_characters": len(seed), "seed_sha256": sha(seed.encode("ascii")),
                  "actions": len(actions), "actions_sha256_json": sha(canonical(actions)),
                  "tiles": len(tiles), "tiles_sha256_json": sha(canonical(tiles)),
                  "distinct_tiles": len(set(tiles)), "complemented_labels_positive": True,
                  "coefficients": len(c), "coefficients_sha256_json": sha(canonical(c))},
              "small_prime_certificates": small_primes, "orders": orders,
              "factorizations": {"4403": [7, 17, 37], "101269": [7, 17, 23, 37],
                                 "8388607": [47, 178481]},
              "order_gcds": {"gcd_23_4403": gcd(23, 4403), "gcd_d_23": gcd(D, 23),
                             "gcd_d_4403": gcd(D, 4403), "lcm_23_4403": 23 * 4403 // gcd(23, 4403)},
              "fixed_modular_evaluations": fixed, "controller_probes": probes,
              "selected_lambda": selected["n"], "Pc3": True,
              "constants": constants, "constant_checks": checks,
              "limits": ["Finite controller, coefficient and scalar-mask checks only.",
                  "No native calibration, carry or Pell theorem is formalized here.",
                  "No internal-ZFC formalization, consistency decision or global minimality claim."]}
    output = HERE / "certificate.json"
    encoded = (json.dumps(report, indent=2, sort_keys=True) + "\n").encode("utf-8")
    if args.write:
        output.write_bytes(encoded)
    else:
        require(output.read_bytes() == encoded, "Saved certificate differs; inspect changes before using --write")
    print(json.dumps({"Pc3": True, "lambda": selected["n"],
                      "H_residues": [row["dense_horner"]["H"] for row in fixed + [selected["evaluations"]]],
                      "total_constant_bytes": checks["total_constant_bytes"],
                      "certificate_sha256": sha(output.read_bytes())}, sort_keys=True))


if __name__ == "__main__":
    main()

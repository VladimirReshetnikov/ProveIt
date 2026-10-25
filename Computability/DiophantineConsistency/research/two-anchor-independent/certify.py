#!/usr/bin/env python3
"""Finite coefficient, geometry and controller checks for two anchors, L=7691."""
import argparse
import hashlib
import importlib.util
import json
from math import gcd, lcm
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PARENT = ROOT / "research/complemented47-controller-independent/certify.py"
L, RHO = 7691, 1 << 47
D, M = 47 * L, 1 << 44


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def encoded(data):
    return (json.dumps(data, indent=2, sort_keys=True) + "\n").encode()


def factor(n):
    answer, p = [], 2
    while p * p <= n:
        if n % p == 0:
            answer.append(p)
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        answer.append(n)
    return answer


def model():
    require(sha(PARENT.read_bytes()) == "318665c36d7600a99dbddbacca11ef9a2d30f65e04a761efe25d1f3653e662ed",
            "Reviewed parent decoder changed")
    spec = importlib.util.spec_from_file_location("reviewed_parent47", PARENT)
    parent = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(parent)
    require(sha(parent.EQUATION.read_bytes()) == "440cf0853ec2f992db7aa6146aec42c189368375d8db725d3df085ca27dc4dff",
            "Complete source decoder/table/seed page changed")
    seed, actions, tiles = parent.decode_tiles()
    c = parent.coefficients(tiles)
    c[2195], c[3296] = 2 * M, 0
    support = {e for e, value in enumerate(c) if value} | {1063, 1064}
    require(len(support) == 981 and max(support) == 2195, "Physical support")
    require(sum(bool(v) for v in c) == 979 and max(c) == 2 * M, "Coefficient support/bound")
    require(sum(c[943:]) == 4 * M - 1024, "Whole nonselector sum")
    return parent, seed, actions, tiles, c, support


def constants(c, support):
    power = lambda e: 1 << (47 * e)
    B, beta = power(L), power(L) - 1
    dc = sum(power(e) for e in (30, 62, 1100))
    dc += sum(v * (power(4393 - e) + power(5495 - e)) for e, v in enumerate(c) if v)
    K = dc + B * power(42)
    MC = beta - sum(power(e) for e in support if e != 1) - 2 * power(1063)
    core = sum(power(e) for e in range(1013, 1022))
    core += sum(power(e) for e in range(1065, 1073)) + power(2195)
    padding = (1 << 26) * power(6726) - power(6708)
    positive_padding = (RHO - 1) * sum(power(e) for e in range(6708, 6726))
    positive_padding += ((1 << 26) - 1) * power(6726)
    require(padding == positive_padding and padding.bit_count() == 872, "Padding identity")
    native = 4 + ((1 << 46) - 2) * (power(4393) + power(5495)) + core + padding
    MF = native + beta
    require(0 < dc < B and 0 < MC < beta < MF < 2 * beta, "Scalar boxes")
    require(native.bit_count() == 981 and MC.bit_count() == D - 981, "Complementary populations")
    require(MC % 4 == 2 and native % 8 == 4, "Origin residues")
    return {"beta": beta, "K": K, "MC": MC, "MF_source": MF}, dc


def geometry(c, support):
    coefficients = {}
    for center in (4393, 5495):
        for e, value in enumerate(c):
            if value:
                require(center - e not in coefficients, "Reflected coefficient collision")
                coefficients[center - e] = value
    require(min(coefficients) == 2198, "First reflected position")
    for e in (30, 62, 1100):
        require(e not in coefficients, "Bare/reflected collision")
        coefficients[e] = 1
    pairs = [(a, b) for a in support for b in support if a - b == 1181]
    require(pairs == [(2195, 1014)], "Unique phase-anchor difference")
    require(not any(a + 1102 in support for a in support), "Clause-band intersection")
    hits = lambda e: sorted((s, coefficients[e - s]) for s in support if e - s in coefficients)
    require(hits(1014) == [(984, 1)] and hits(2195) == [(1095, 1)], "Two Start phase targets")
    require(1014 - 42 not in support and 2195 - 42 not in support, "Spatial phase-target collision")
    for j in range(9):
        require(hits(1013 + j) == [(983 + j, 1)] and 971 + j not in support,
                "All nine temporal copy fields")
    for j in range(8):
        require(hits(1065 + j) == [(1003 + j, 1)] and 1023 + j in support
                and 1065 + j not in support, "All eight spatial copy fields")
    clause = sorted((e, c[e]) for e in support if c[e])
    adjacent = sorted((e, c[e + 1]) for e in support if c[e + 1])
    for center in (4393, 5495):
        require(hits(center) == clause and center - 42 not in support, "Entire clause field")
        require(hits(center - 1) == adjacent and center - 43 not in support,
                "Entire clause predecessor")
    require(hits(6707) == [(2195, 1 << 35)], "Padding predecessor")
    require(all(not hits(e) for e in range(6708, 6748)), "Complete zero padding band")
    require(hits(7690) == [(2195, c[0])], "Last-digit reset")
    require(max(coefficients) + max(support) == 7690 < L, "No product crosses a cell")
    require(7 * (M + 30) < RHO, "Last digit plus global carry29 gives F<q/7")
    require(2 * 7 * 3 < RHO and 5495 > 1, "2C+F<q/3 bound")
    require(L - 6559 >= 3 and L - 1106 >= 3 and L - 1064 >= 3 and RHO > 3,
            "Three interior dummy contributions sum below q/rho^2")
    return {"physical_positions": len(support), "nonzero_coefficients": sum(bool(v) for v in c),
            "first_reflected_exponent": 2198, "last_product_exponent": 7690,
            "unique_difference_1181": pairs, "padding_predecessor": hits(6707),
            "padding_zero_band": [6708, 6747], "last_digit": hits(7690),
            "native_population": 981, "MC_population": D - 981,
            "padding_population": 872, "coefficient_sum": sum(c), "coefficient_maximum": max(c)}


def modular(p, c, tiles, whole):
    r, B = RHO % p, pow(2, D, p)
    inverse = pow(r, -1, p)
    phi = 0
    for value in reversed(c):
        phi = (phi * inverse + value) % p
    K = (sum(pow(r, e, p) for e in (30, 62, 1100, L + 42))
         + (pow(r, 4393, p) + pow(r, 5495, p)) * phi) % p
    # Independent expansion of the printed selector and control polynomials.
    direct = sum(pow(2, 47 * e, p) for e in (30, 62, 1100, L + 42))
    for center in (4393, 5495):
        for j, (w, n, east, south) in enumerate(tiles):
            direct += (1 + 1024 * (1 + w + 256 * n + 131072 * east + 33554432 * south)) * pow(2, 47 * (center - j), p)
        for start, bits, count in ((1023, 10, 8), (1003, 27, 8), (1013, 18, 9), (983, 35, 9)):
            direct += sum((1 << (bits + j)) * pow(2, 47 * (center - start - j), p) for j in range(count))
        direct += M * pow(2, 47 * (center - 1095), p) + 2 * M * pow(2, 47 * (center - 2195), p)
    require(K == direct % p == whole["K"] % p, "Three whole-K routes disagree")
    H = (1 + B * K + B * B) % p
    return {"p": p, "B": B, "K": K, "H": H}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    parent, seed, actions, tiles, c, support = model()
    whole, dc = constants(c, support)
    geometric = geometry(c, support)
    fixed = []
    for p, order in ((47, 23), (7691, 7690)):
        require(parent.least_factor(p) is None, "Fixed modulus not prime")
        B = pow(2, D, p)
        proper = {str(f): pow(B, order // f, p) for f in factor(order)}
        require(pow(B, order, p) == 1 and all(v != 1 for v in proper.values()), "Exact B order")
        require(gcd(D, order) == 1 and pow(2, order, p) == 1
                and all(pow(2, order // f, p) != 1 for f in factor(order)), "Exact base2 order")
        row = modular(p, c, tiles, whole)
        require(order > 2 and row["H"] != 0, "Fixed controller unit fails")
        fixed.append({**row, "order": order, "order_factors": factor(order), "proper_order_tests": proper})
    spacing = lcm(*(row["order"] for row in fixed))
    require(spacing == 176870 and gcd(spacing, D) == 1, "Controller spacing")
    trials, selected = [], None
    for j in range((D - 1) // spacing + 1, (D - 1) // spacing + 202):
        p = spacing * j + 1
        divisor = parent.least_factor(p)
        row = {"multiplier": j, "candidate": p, "least_factor": divisor}
        if divisor is None:
            row.update(modular(p, c, tiles, whole))
            row["B_squared"] = pow(2, 2 * D, p)
            row["lift_residue"] = pow(2, D * (p - 1), p * p)
            require(row["lift_residue"] % p == 1, "Fermat residue")
            row["lift_quotient"] = (row["lift_residue"] - 1) // p
            if row["H"] and row["B_squared"] != 1 and row["lift_quotient"]:
                selected = row
        trials.append(row)
        if selected:
            break
    require(selected is not None, "No controller found in the stated bounded interval")
    ports = {}
    for name, value in whole.items():
        raw = value.to_bytes((value.bit_length() + 7) // 8, "big")
        ports[name] = {"bits": value.bit_length(), "bytes": len(raw), "sha256": sha(raw)}
    proof = HERE / "PROOF.md"
    data = {"schema": "two_anchor7691_finite_v1", "L": L, "d": D,
            "parent_verifier_sha256": sha(PARENT.read_bytes()), "script_sha256": sha(Path(__file__).read_bytes()),
            "source_page_sha256": sha(parent.EQUATION.read_bytes()),
            "proof_sha256": sha(proof.read_bytes()), "geometry": geometric, "fixed_controller": fixed,
            "spacing": spacing, "controller_trials": trials, "selected_lambda": selected["p"],
            "constant_ports": ports, "raw_bytes": sum(r["bytes"] for r in ports.values()),
            "scope": "Finite formulas, support geometry and numerical controller. Unbounded carry/native/Pell proofs are in PROOF.md; no new formal-kernel replay."}
    raw = encoded(data)
    if args.write:
        (HERE / "certificate.json").write_bytes(raw)
    else:
        require((HERE / "certificate.json").read_bytes() == raw, "Certificate differs")
    print(json.dumps({"status": "PASS", "lambda": selected["p"], "raw_bytes": data["raw_bytes"],
                      "H": [r["H"] for r in fixed] + [selected["H"]], "certificate_sha256": sha(raw)}))


if __name__ == "__main__":
    main()

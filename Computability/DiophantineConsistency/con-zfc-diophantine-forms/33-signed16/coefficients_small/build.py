#!/usr/bin/env python3
"""Construct the complete Wang943 tuple with B=2^1012625.

Standard library only. Inputs are inert, pinned JSON. This script checks finite
identities; the unbounded semantic and rank-control proofs are in PROOF.md.
"""
from pathlib import Path
from math import gcd
import gzip
import hashlib
import json

ROOT = Path(__file__).resolve().parent
PIN = "8c6eec9d19ef80538c8e61ff6e0180040583446a"
INSTANCE = "wang943-stride2-L8101-b125"


def tiles_from_literal_actions():
    actions = json.loads((ROOT / "source/k215_transitions.json").read_text())["transitions"]
    assert len(actions) == 430
    assert actions[0] == [0, 0, 1, 1, 93]
    right_targets = sorted({n for q, bit, val, move, n in actions if move == 1})
    left_targets = sorted({n for q, bit, val, move, n in actions if move == -1})
    right = {q: j + 6 for j, q in enumerate(right_targets)}
    left = {q: j + 205 for j, q in enumerate(left_targets)}
    head = lambda q, bit: 2 * (q + 1) + bit
    tiles = set()
    for q, bit, val, move, nxt in actions:
        if move == 1:
            tiles.add((0, head(q, bit), right[nxt], val))
        else:
            assert move == -1
            tiles.add((left[nxt], head(q, bit), 0, val))
    for bit in (0, 1):
        tiles.add((0, head(215, bit), 0, head(215, bit)))
        tiles.add((0, bit, 0, bit))
        for q in right_targets:
            tiles.add((right[q], bit, 0, head(q, bit)))
        for q in left_targets:
            tiles.add((0, bit, left[q], head(q, bit)))
    tiles.update((0, color, 0, 438) for color in (0, 1, head(215, 0), head(215, 1)))
    tiles.update([(2, 434, 2, 0), (2, 435, 3, 1), (3, 436, 4, head(93, 0)), (4, 436, 4, 0)])
    tiles.update((1, 438, 1, color) for color in (434, 435, 436))
    tiles.update((a, 437, z, 437) for a in (0, 1, 4) for z in (0, 1, 2))
    start, forbidden = (2, 435, 3, 1), (5, 0, 0, 0)
    tiles.add(forbidden)
    ordered = [start, forbidden] + sorted(tiles - {start, forbidden})
    assert len(ordered) == 943
    assert len(right_targets) == 199 and len(left_targets) == 45
    assert [list(t) for t in ordered] == json.loads((ROOT / "source/wang943_tiles.json").read_text())
    return ordered


def construct():
    tiles = tiles_from_literal_actions()
    b, length, H, T1, T2 = 125, 8101, 21, 3341, 4459
    d = b * length
    anchors = (1110, 1112, 1111, 2225)
    dummies = (1065, 1066)
    copies = {(port, bit): offset + 2 * bit
              for port, offset in enumerate((1024, 1004, 984, 964)) for bit in range(10)}
    E = set(range(943)) | set(copies.values()) | set(anchors) | set(dummies)
    assert len(E) == 989 and max(E) == 2225
    weights = [1 << (10 + 2 * j) for j in range(44)]
    coeff = {}
    for i, tile in enumerate(tiles):
        coeff[i] = 1 + sum(weights[10 * port + bit]
                           for port, label in enumerate(tile) for bit in range(10)
                           if ((label + 512) >> bit) & 1) + sum(weights[40:])
    for (port, bit), exponent in copies.items():
        coeff[exponent] = weights[10 * port + bit]
    for j, exponent in enumerate(anchors):
        coeff[exponent] = weights[40 + j]
    for exponent in dummies:
        coeff[exponent] = 0
    assert set(coeff) == E
    mu = 1022 + sum(weights)
    dc = {shift: 1 for shift in (1, 40, 61, 1113)}
    for exponent, c in coeff.items():
        for target in (T1, T2):
            assert target - exponent > 0
            dc[target - exponent] = dc.get(target - exponent, 0) + c
    dc = {exponent: c for exponent, c in dc.items() if c}
    targets = [(1004 + 2*j, {964 + 2*j}, set(), {1004 + 2*j}) for j in range(10)]
    targets += [(1045 + 2*j, {984 + 2*j}, {1024 + 2*j}, set()) for j in range(10)]
    targets += [(1111, {1110}, set(), {1111}), (2225, {1112}, set(), {2225})]
    basis_checks = 0
    for target, expected_dc, expected_dr, expected_temporal in targets:
        for exponent in E:
            assert dc.get(target - exponent, 0) == int(exponent in expected_dc)
            assert int(exponent + H == target) == int(exponent in expected_dr)
            assert int(exponent == target) == int(exponent in expected_temporal)
            basis_checks += 3
    for target in (T1, T2):
        for exponent in E:
            assert dc.get(target - exponent, 0) == coeff[exponent]
            assert exponent + H != target
            basis_checks += 2
    assert basis_checks == 69230
    assert {(T1-e) % length for e in E}.isdisjoint({(T2-e) % length for e in E})
    assert {(1111-e) % length for e in E} & {(2225-e) % length for e in E} == {0}
    mass = (len(E) + 2) * (2 * sum(coeff.values()) + 6)
    assert mass.bit_length() == 118 and (4*mass+8).bit_length() == 120
    assert 4 * mass + 8 < 1 << b and 2 * mu + 4 < 1 << b
    assert mu.bit_length() == 97 and mu.bit_count() == 53
    max_degree = max(max(dc) + max(E), H + max(E), max(E))
    assert max_degree == 6684
    padding_count = len(E) - (2 * mu.bit_count() + len(targets) + 1)
    padding = list(range(max_degree+1, max_degree+1+padding_count))
    assert padding_count == 860 and padding[-1] == 7544 < length
    residues = {}
    for modulus in (5, 8101):
        r = pow(2, b, modulus)
        dc_r = sum((c % modulus) * pow(r, exponent, modulus)
                   for exponent, c in dc.items()) % modulus
        dr_r = pow(r, H, modulus)
        B_r = pow(2, d, modulus)
        bracket = (1+B_r*(dc_r+B_r*dr_r+B_r)) % modulus
        assert r*r % modulus == modulus - 1
        assert B_r == r and dc_r == (1+3*r) % modulus and dr_r == r
        assert bracket == (-3) % modulus and gcd(bracket, modulus) == 1
        assert gcd(B_r*B_r-1, modulus) == 1
        residues[str(modulus)] = {"rho": r, "B": B_r, "DC": dc_r, "DR": dr_r,
                                  "rank_bracket": bracket, "q2_minus_1": (B_r*B_r-1) % modulus}
    assert gcd(8101, 30) == 1 and length % 4 == 1
    # The exact 5-adic order certificate is small modular arithmetic.
    assert pow(2, 4*d, 5**4) == 1
    assert pow(2, 4*d, 5**5) != 1
    assert pow(2, 4*d, 5*d) == 1
    scalars = {
        "instance": INSTANCE, "pin": PIN, "b": b, "L": length, "d": d,
        "H": H, "clause_targets": [T1, T2], "copy_offsets": [1024,1004,984,964],
        "copy_stride": 2, "anchors": list(anchors), "dummies": list(dummies),
        "bare_shifts": [1,40,61,1113], "support_cardinality": len(E),
        "mu": str(mu), "mu_bit_length": mu.bit_length(), "mu_population": mu.bit_count(),
        "mass": str(mass), "mass_bit_length": mass.bit_length(),
        "carry_threshold_bit_length": (4*mass+8).bit_length(),
        "max_product_exponent": max_degree, "padding_first": padding[0],
        "padding_last": padding[-1], "padding_count": padding_count,
        "native_basis_checks": basis_checks, "residues": residues,
        "Boolean_lemma": {"B4_mod_5d": 1, "v5_B4_minus_1": 4,
                           "physical_indices": "{4j:0<=j<N/5} union {1}",
                           "N_condition": "N is a power of five; N/5>5d"},
    }
    return scalars, E, coeff, dc, mu, targets, padding


def materialize(data):
    scalars, E, coeff, dc, mu, targets, padding = data
    b, d = scalars["b"], scalars["d"]
    B = 1 << d
    DC = sum(c << (b * exponent) for exponent, c in dc.items())
    DR = 1 << (b * scalars["H"])
    MF = 4 + sum(mu << (b*t) for t in scalars["clause_targets"])
    MF += sum(1 << (b*t) for t, *_ in targets)
    MF += sum(1 << (b*t) for t in padding)
    MC = B - 1 - sum(1 << (b*e) for e in E if e != 1) - (2 << (b*1065))
    ports = {"beta": B-1, "K": DC+B*DR, "MC": MC, "MF_source": MF+B-1}
    assert 0 < DC < B and 0 < MC < B-1 and 0 < MF < B-1
    assert MC % 4 == 2 and MF % 8 == 4
    assert MF.bit_count() == 989 and MC.bit_count() == d-989
    out = ROOT / "payloads"
    out.mkdir(exist_ok=True)
    manifest = {"instance": INSTANCE, "encoding": "unsigned minimal-width little-endian; no header",
                "ports": {}, "native_MF_population": MF.bit_count(),
                "MC_population": MC.bit_count(), "population_sum": d}
    for name, value in ports.items():
        raw = value.to_bytes((value.bit_length()+7)//8, "little")
        compressed = gzip.compress(raw, compresslevel=9, mtime=0)
        # Python 3.11/3.12 may inherit zlib's platform OS byte; normalize
        # the informational gzip header for cross-Python reproducibility.
        compressed = compressed[:9] + bytes([255]) + compressed[10:]
        (out / (name+".bin.gz")).write_bytes(compressed)
        assert int.from_bytes(gzip.decompress(compressed), "little") == value
        manifest["ports"][name] = {
            "file": "payloads/"+name+".bin.gz", "raw_bytes": len(raw),
            "gzip_bytes": len(compressed), "bit_length": value.bit_length(),
            "population": value.bit_count(), "sha256_raw": hashlib.sha256(raw).hexdigest(),
            "sha256_gzip": hashlib.sha256(compressed).hexdigest(),
            "mod4": value % 4, "mod8": value % 8,
            "mod5": value % 5, "mod8101": value % 8101,
        }
    manifest["total_raw_bytes"] = sum(p["raw_bytes"] for p in manifest["ports"].values())
    manifest["total_gzip_bytes"] = sum(p["gzip_bytes"] for p in manifest["ports"].values())
    assert manifest["total_raw_bytes"] == 506644
    binding = {
        "instance": INSTANCE, "base": "B=2^1012625", "domain_contract": "complete inputless Wang943 native/Pell interface",
        "port_aliases": {"Bm1": "beta", "beta": "beta", "Kconstant": "K", "K0": "K", "MC": "MC", "MF": "MF_source"},
        "fourth_port": "MF_source=MF_native+B-1; already shifted",
        "all_ports_required": True, "proof": "PROOF.md",
        "upstream_pin": PIN, "payload_manifest": "MANIFEST.json",
    }
    for filename, content in (("SCALARS.json", scalars), ("MANIFEST.json", manifest),
                              ("COEFFICIENT_BINDING.json", binding)):
        (ROOT / filename).write_text(json.dumps(content, indent=2)+"\n")
    sources = {name: hashlib.sha256((ROOT / "source" / name).read_bytes()).hexdigest()
               for name in ("k215_transitions.json", "wang943_tiles.json", "LICENSE.ProveIt")}
    (ROOT / "SOURCE_HASHES.json").write_text(json.dumps({"pin": PIN, "files": sources}, indent=2)+"\n")
    return manifest


if __name__ == "__main__":
    result = materialize(construct())
    print(json.dumps({"instance": INSTANCE, "total_raw_bytes": result["total_raw_bytes"],
                      "total_gzip_bytes": result["total_gzip_bytes"], "basis_checks": 69230}, indent=2))

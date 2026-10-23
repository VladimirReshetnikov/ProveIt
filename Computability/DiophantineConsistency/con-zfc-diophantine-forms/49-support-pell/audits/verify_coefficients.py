#!/usr/bin/env python3
"""Independently reconstruct the four package-31 coefficient integers.

Uses only the literal recipe in COEFFICIENT_PROOF.md section 1 and the
943 supplied tiles.  Does not import or execute upstream builder code.
Finite byte verification does not certify the unbounded compiler theorem.
All checks remain enabled under python -O.
"""

import argparse
import gzip
import hashlib
import json
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def reconstruct(directory):
    tiles_path = directory / "upstream" / "wang943_tiles.json"
    tiles_bytes = tiles_path.read_bytes()
    tiles = json.loads(tiles_bytes)
    require(len(tiles) == 943, "Wrong tile count")
    require(len({tuple(tile) for tile in tiles}) == 943, "Duplicate tile")
    require(tiles[0] == [2, 435, 3, 1], "Start tile changed")
    require(tiles[1] == [5, 0, 0, 0], "Forbidden tile changed")
    require(all(len(tile) == 4 and all(isinstance(x, int) and 0 <= x < 512
                                     for x in tile) for tile in tiles),
            "A tile is not a four-label 9-bit word")
    require(tiles[2:] == sorted(tiles[2:]), "Ordinary tile order changed")

    width, length = 121, 8801
    exponent = width * length
    big_base = 1 << exponent
    weights = [1 << (10 + 2*j) for j in range(44)]
    clauses = {}
    anchors = (1095, 1096, 2195, 3296)
    offsets = (1023, 1013, 1003, 983)
    for selector, tile in enumerate(tiles):
        coefficient = 1 + sum(weights[40:])
        for slot, label in enumerate(tile):
            shifted = label + 512
            for bit in range(10):
                if (shifted >> bit) & 1:
                    coefficient += weights[10*slot + bit]
        clauses[selector] = coefficient
    for slot, offset in enumerate(offsets):
        for bit in range(10):
            require(offset + bit not in clauses, "Overlapping copy position")
            clauses[offset + bit] = weights[10*slot + bit]
    for j, anchor in enumerate(anchors):
        require(anchor not in clauses, "Overlapping anchor")
        clauses[anchor] = weights[40 + j]
    for dummy in (1063, 1064):
        require(dummy not in clauses, "Overlapping dummy")
        clauses[dummy] = 0

    support = (set(range(943)) | set(range(983, 993)) |
               set(range(1003, 1033)) | set((1063, 1064, *anchors)))
    require(set(clauses) == support and len(support) == 989,
            "The literal support is not the claimed 989-element set")
    digit = lambda power: 1 << (width * power)

    dc = sum(digit(power) for power in (30, 62, 1100, 2200))
    for power, coefficient in clauses.items():
        dc += coefficient * (digit(4393-power) + digit(5495-power))
    dr = digit(42)
    beta = big_base - 1
    mc = beta - sum(digit(power) for power in support if power != 1)
    mc -= 2 * digit(1063)
    mu = 1022 + sum(weights)
    padding = ((1 << 119)-1) * sum(digit(power) for power in range(8792, 8799))
    padding += ((1 << 27)-1) * digit(8799)
    mf_native = 4 + mu*(digit(4393) + digit(5495))
    mf_native += sum(digit(1013+j) + digit(1065+j) for j in range(10))
    mf_native += digit(2195) + digit(3296) + padding
    ports = {"beta": beta, "K": dc + big_base*dr, "MC": mc,
             "MF_source": mf_native + beta}

    require(0 < mc < beta and 0 < mf_native < beta, "Mask interval failure")
    require(mc % 4 == 2 and mf_native % 8 == 4, "Low mask residues fail")
    require(mc.bit_count() == exponent-989, "MC population differs")
    require(mf_native.bit_count() == 989, "MF population differs")
    mass = (989+2)*(2*sum(clauses.values())+6)
    threshold = max(4*mass+8, 2*mu+4, 16)
    require(threshold == 789998487493936316431751375694647416,
            "Carry threshold differs from the literal recipe")
    require((1 << 119) < threshold < (1 << 120) < (1 << 121),
            "Carry width bounds fail")

    # Independent finite controller arithmetic; no inferred unbounded claim.
    unit_rows = []
    for prime in (11, 13, 677, 2341):
        row = {"prime": prime, "B": big_base % prime,
               "DC": dc % prime, "DR": dr % prime,
               "q_squared_minus_one": (big_base*big_base-1) % prime,
               "bracket": (1+big_base*dc+big_base*big_base*(dr+1)) % prime}
        require(row["q_squared_minus_one"] != 0 and row["bracket"] != 0,
                "A controller unit is zero")
        unit_rows.append(row)
    require(pow(big_base, 2340, 2341**2) == 2556373,
            "Valuation-one witness differs")
    orders = {}
    for modulus, expected in ((121, 10), (13, 12), (677, 52), (2341, 60)):
        value = 1
        actual = None
        for order in range(1, expected+1):
            value = value*(big_base % modulus) % modulus
            if value == 1:
                actual = order
                break
        require(actual == expected, "Multiplicative order differs")
        orders[str(modulus)] = actual

    binding = json.loads((directory / "COEFFICIENT_BINDING.json").read_text())
    require((binding["b"], binding["L"], binding["d"]) ==
            (width, length, exponent), "Binding dimensions differ")
    require(binding["ports"] == {"Bm1": "beta", "Kconstant": "K",
                                 "MC": "MC", "MF": "MF_source"},
            "Binding aliases differ")
    require(binding["padding"]["orders"] == orders, "Order manifest differs")
    require(binding["padding"]["unit_residues"] == unit_rows,
            "Controller residues differ")
    records = {record["port"]: record for record in binding["files"]}
    require(set(records) == set(ports), "Wrong set of coefficient ports")
    checked = []
    for port, value in ports.items():
        record = records[port]
        raw = value.to_bytes((value.bit_length()+7)//8, "little")
        compressed = (directory / record["file"]).read_bytes()
        require(gzip.decompress(compressed) == raw, port + ": payload differs")
        require(record["raw_bytes"] == len(raw), port + ": raw size differs")
        require(record["gzip_bytes"] == len(compressed), port + ": gzip size differs")
        require(record["bit_length"] == value.bit_length(), port + ": bit length differs")
        require(record["sha256"] == digest(raw), port + ": raw hash differs")
        require(record["gzip_sha256"] == digest(compressed), port + ": gzip hash differs")
        checked.append({"port": port, "raw_bytes": len(raw),
                        "gzip_bytes": len(compressed), "bit_length": value.bit_length(),
                        "sha256": digest(raw), "gzip_sha256": digest(compressed)})
    require(sum(x["raw_bytes"] for x in checked) == 533099,
            "Total raw byte count differs")
    require(sum(x["gzip_bytes"] for x in checked) == 10485,
            "Total gzip byte count differs")
    return {"status": "PASS", "scope": "Independent literal-recipe and byte audit; not a proof of compiler semantics",
            "instance": "wang943-mixed-121x8801", "tiles": len(tiles),
            "tiles_sha256": digest(tiles_bytes), "support_size": len(support),
            "d": exponent, "carry_threshold": str(threshold),
            "MC_population": mc.bit_count(), "MF_native_population": mf_native.bit_count(),
            "orders": orders, "unit_residues": unit_rows,
            "ports": checked, "total_raw_bytes": 533099, "total_gzip_bytes": 10485}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("coefficient_directory", type=Path)
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()
    receipt = reconstruct(args.coefficient_directory)
    text = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    if args.receipt:
        args.receipt.write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()

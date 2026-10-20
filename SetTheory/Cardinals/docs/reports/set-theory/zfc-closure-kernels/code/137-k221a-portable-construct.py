#!/usr/bin/env python3
"""Deterministically construct all three alternatives from the pinned K221 table."""
from pathlib import Path
import argparse
import hashlib
import json

BASE_SHA = "e6dc479f09ded05dd1c0639b60a0c453483f42e6b77c29562d433cac528c1ecc"
EDITS = {
    "row103": {(103, 1): (0, "L", 142)},
    "row157": {(157, 1): (1, "L", 187)},
    "both": {(103, 1): (0, "L", 142), (157, 1): (1, "L", 187)},
}
EXPECTED = {
    "row103": "59cc7866c35cb3b86dbc1fbbebff745c719ef18402bd28cbdfbbf63c9f2f0d8d",
    "row157": "0319319b73af348c9c2af06348afc87e2d3bd81b3ead85af90cfbc7cae8398cc",
    "both": "735a26bef15168bf696103f7f69a55472d98a4a1a4ae8eff653eb42bd7777ded",
}


def need(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    raw = args.baseline.read_bytes()
    need(hashlib.sha256(raw).hexdigest() == BASE_SHA, "Wrong baseline table")
    table = {}
    for line in raw.decode("ascii").splitlines():
        if line and not line.startswith("#"):
            q, b, w, d, z = line.split()
            table[int(q), int(b)] = int(w), d, int(z)
    records = []
    for name, edits in EDITS.items():
        new = {**table, **edits}
        encoded = "#! start 0\n" + "".join(
            f"{q} {b} {w} {d} {z}\n" for (q, b), (w, d, z) in sorted(new.items())
        )
        digest = hashlib.sha256(encoded.encode("ascii")).hexdigest()
        need(digest == EXPECTED[name], "Unexpected constructed bytes")
        directory = args.output / name
        directory.mkdir(parents=True, exist_ok=True)
        (directory / "k221.native.tm").write_bytes(encoded.encode("ascii"))
        records.append({
            "variant": name, "native_sha256": digest,
            "edits": [
                {"state": q, "read": b, "old": table[q, b], "new": action}
                for (q, b), action in sorted(edits.items())
            ],
        })
    receipt = {
        "status": "DETERMINISTIC_THREE_VARIANT_CONSTRUCTION_PASS",
        "baseline_native_sha256": BASE_SHA, "variants": records,
    }
    (args.output / "construction.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()

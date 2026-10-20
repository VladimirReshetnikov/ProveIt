#!/usr/bin/env python3
"""Deterministically construct all three alternatives from the pinned K220 table."""
from pathlib import Path
import argparse
import hashlib
import json

BASE_SHA = "4466ec4f947a9c5112397c30ca25b0e70e3ac39ee54878b3e4493a0297d732e4"
EDITS = {
    "row103": {(103, 1): (0, "L", 142)},
    "row157": {(157, 1): (1, "L", 187)},
    "both": {(103, 1): (0, "L", 142), (157, 1): (1, "L", 187)},
}
EXPECTED = {
    "row103": "d096503d36f677f449367155a3e95cc87865984ad1268801326ea95d5ecb2015",
    "row157": "201977820ab5533ba910a0ed050970091c9e8e32778df76f8341343f664adb48",
    "both": "e946f3e80febc4a993ed2c7352b18e1aec46d21e331f08f067212cc2ca55ac5e",
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
        (directory / "k220.native.tm").write_bytes(encoded.encode("ascii"))
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

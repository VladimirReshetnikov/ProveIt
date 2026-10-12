#!/usr/bin/env python3
"""Replay the seven new whole-cut proofs from their saved exact source inputs."""
import argparse
import hashlib
import json
from pathlib import Path
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fast-dir", type=Path, required=True)
    parser.add_argument("--certificates", type=Path,
                        default=Path(__file__).resolve().parents[1] / "evidence/new_certificates")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    sys.path.insert(0, str(args.fast_dir.resolve(strict=True)))
    from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
    records = []
    paths = sorted(args.certificates.glob("*.json"))
    if not paths:
        raise ValueError("No saved certificate files found")
    for path in paths:
        data = path.read_bytes()
        record = json.loads(data)
        case, proof = record["case"], record["certificate"]
        accepted = verify_normal_cut_handlebodies(
            case["triangulation"], case["coordinates"], proof)
        records.append({"case": case["id"], "file": path.name,
                        "sha256": hashlib.sha256(data).hexdigest(),
                        "accepted": bool(accepted)})
        if not accepted:
            raise RuntimeError(f"Saved whole-cut certificate rejected: {case['id']}")
    report = {"scope": "Independent whole-cut verifier on saved exact source inputs",
              "replayed_certificates": len(records), "accepted": True, "cases": records}
    encoded = json.dumps(report, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(encoded, encoding="utf-8")
    print(encoded, end="")


if __name__ == "__main__":
    main()

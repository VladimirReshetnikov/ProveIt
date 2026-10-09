#!/usr/bin/env python3
"""Replay all saved guarded positives from their original source PD arrays."""
from __future__ import annotations

import argparse
from hashlib import sha256
import json
from pathlib import Path
import sys
import time


def main():
    root = Path(__file__).resolve().parent.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fast", type=Path,
                        default=root / "snapshots/final/Topology/UnknotRecognition/fast")
    parser.add_argument("--audit", type=Path,
                        default=root / "experiments/audit-guarded.json")
    parser.add_argument("--output", type=Path,
                        default=root / "reproduced/saved-certificate-replay.json")
    args = parser.parse_args()
    fast = args.fast.resolve()
    sys.path.insert(0, str(fast))
    import fastunknot
    from fastunknot import Diagram
    from fastunknot.group_certificate import verify_group_certificate
    assert Path(fastunknot.__file__).resolve().is_relative_to(fast)
    data = json.loads(args.audit.read_text())
    source_hashes = {
        str(p.relative_to(fast / "fastunknot")): sha256(p.read_bytes()).hexdigest()
        for p in sorted((fast / "fastunknot").rglob("*.py"))
    }
    assert source_hashes == data["source_sha256"]["current"], "wrong source snapshot"
    start = time.monotonic()
    results = []
    for row in data["cases"]:
        proof = row["singleton"]["proof"]
        if proof is None:
            continue
        key = proof["certificate_sha256"]
        certificate = data["certificates"][key]
        encoded = json.dumps(certificate, sort_keys=True, separators=(",", ":")).encode()
        assert sha256(encoded).hexdigest() == key
        checks = {}
        for compressed in (False, True):
            valid = verify_group_certificate(
                Diagram.from_pd(row["source"]["pd"]), certificate,
                compressed=compressed, max_work=20_000_000, max_nodes=100_000)
            assert valid, (row["source"]["name"], compressed)
            checks["compressed" if compressed else "literal"] = valid
        results.append({"source": row["source"]["name"], "version": certificate["version"],
                        "certificate_sha256": key, **checks})
    assert len(results) == data["singleton_certificates"] == 54
    record = {"completed": True, "positives": len(results), "source_replays": 2 * len(results),
              "all_valid": True, "seconds": time.monotonic() - start,
              "audit_sha256": sha256(args.audit.read_bytes()).hexdigest(),
              "source_hashes_match": True, "results": results}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps({k: record[k] for k in ("completed", "positives", "source_replays", "all_valid")}))


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Rebuild the inherited four-port tuple without modifying pinned sources.

Only the Python standard library is needed. Run from any working directory:
    python3 vendor/rebuild_coefficients.py
An optional positional argument selects the package root.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import tempfile


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("root", nargs="?", type=Path,
                        default=Path(__file__).resolve().parent.parent)
    args = parser.parse_args()
    root = args.root.resolve()
    vendor = root / "vendor"
    source = vendor / "package31/coefficients"
    manifest = json.loads((vendor / "SOURCES.json").read_text())
    checked = []
    for record in manifest["files"]:
        raw = (vendor / record["local"]).read_bytes()
        require(len(raw) == record["bytes"], "Source length changed: " + record["local"])
        require(sha256(raw) == record["sha256"], "Source SHA-256 changed: " + record["local"])
        blob = hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()
        require(blob == record["git_blob_sha1"], "Source Git blob changed: " + record["local"])
        checked.append(record["local"])

    historical = json.loads((source / "SOURCE_PINS.json").read_text())
    for record in historical["files"]:
        raw = (source / record["local"]).read_bytes()
        require(len(raw) == record["bytes"] and sha256(raw) == record["sha256"],
                "Inherited source pin changed: " + record["local"])

    # Bind the literal compiler input table to the independently supplied TM.
    machine = []
    for line in (vendor / "machine/k215.tm").read_text().splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        q, b, value, direction, target = line.split()
        require(direction in ("L", "R"), "Unexpected machine movement")
        machine.append([int(q), int(b), int(value),
                        -1 if direction == "L" else 1, int(target)])
    transitions = json.loads((source / "upstream/k215_transitions.json").read_text())
    require(machine == transitions["transitions"], "Compiler transitions differ from k215.tm")
    require(len(machine) == 430, "Machine must have 430 working actions")

    active = json.loads((root / "data/coefficients_binding.json").read_text())
    expected = {record["name"]: record for record in active["files"]}
    require(set(expected) == {"beta", "K", "MC", "MF_source"}, "Four-port binding required")
    comparisons = []
    with tempfile.TemporaryDirectory(prefix="con_zfc_coefficient_rebuild_") as temporary:
        work = Path(temporary) / "coefficients"
        shutil.copytree(source, work)
        result = subprocess.run([sys.executable, str(work / "build_coefficients.py")],
                                cwd=work, check=True, capture_output=True, text=True)
        rebuilt = json.loads(result.stdout)
        frozen = json.loads((source / "COEFFICIENT_BINDING.json").read_text())
        require(rebuilt["ports"] == frozen["ports"], "Rebuilt port interpretation changed")
        for field in ("instance", "b", "L", "d", "geometry", "padding", "mask_checks"):
            require(rebuilt[field] == frozen[field], "Rebuilt finite check changed: " + field)
        for record in rebuilt["files"]:
            name = record["port"]
            raw = (work / "payloads" / (name + ".bin")).read_bytes()
            active_gzip = (root / "data" / (name + ".bin.gz")).read_bytes()
            active_raw = gzip.decompress(active_gzip)
            target = expected[name]
            actual = sha256(raw)
            require(raw == active_raw, "Rebuilt coefficient differs from active data: " + name)
            require(actual == target["sha256"] == record["sha256"],
                    "Raw coefficient SHA-256 mismatch: " + name)
            require(len(raw) == target["bytes"] == record["raw_bytes"],
                    "Raw coefficient length mismatch: " + name)
            bits = int.from_bytes(raw, "little").bit_length()
            require(bits == target["bit_length"] == record["bit_length"],
                    "Coefficient bit length mismatch: " + name)
            require(sha256(active_gzip) == target["gzip_sha256"],
                    "Active gzip SHA-256 mismatch: " + name)
            comparisons.append({"name": name, "bytes": len(raw), "bit_length": bits,
                                "sha256": actual, "raw_bytes_identical": True,
                                "active_gzip_sha256": sha256(active_gzip),
                                "rebuilt_gzip_sha256": record["gzip_sha256"],
                                "gzip_bytes_identical": record["gzip_sha256"] == target["gzip_sha256"]})

    # Reproduce the literal 31-variable algebraic parent from its preserved
    # 32-variable ancestor. This is a separate finite algebra audit, not an
    # assertion about the original ancestor's default coefficient tuple.
    with tempfile.TemporaryDirectory(prefix="con_zfc_parent_rebuild_") as temporary:
        work = Path(temporary) / "arithmetic"
        shutil.copytree(vendor / "quartic31-source", work)
        result = subprocess.run([sys.executable, str(work / "build_arithmetic.py")],
                                cwd=work, check=True, capture_output=True, text=True)
        raw = (work / "quartic31.json").read_bytes()
        require(raw == (root / "data/parent_quartic31.json").read_bytes(),
                "Rebuilt quadratic parent differs from active parent")
        parent_receipt = {
            "status": "PASS",
            "source_retrieval_commit": "8c6eec9d19ef80538c8e61ff6e0180040583446a",
            "source_ancestry_commit": "ae3007ca4467011e0e051c84acb4a1dd13971b0e",
            "active_parent_bytes": len(raw),
            "active_parent_sha256": sha256(raw),
            "raw_bytes_identical": True,
            "original_sources_modified": False,
            "inherited_audit": json.loads(result.stdout),
            "scope": "Rebuild of literal algebraic parent; no compiler or consistency theorem proved by this program."
        }
        (vendor / "PARENT_REBUILD_RECEIPT.json").write_text(
            json.dumps(parent_receipt, indent=2) + "\n")

    receipt = {
        "status": "PASS",
        "retrieval_commit": manifest["retrieval_commit"],
        "inherited_generator_source_commit": historical["source_commit"],
        "python": platform.python_version(),
        "pinned_files_checked": len(checked),
        "inherited_source_pins_checked": len(historical["files"]),
        "literal_machine_actions_matched": len(machine),
        "coefficient_instance": rebuilt["instance"],
        "geometry": rebuilt["geometry"],
        "padding": rebuilt["padding"],
        "mask_checks": rebuilt["mask_checks"],
        "files": comparisons,
        "total_raw_bytes": sum(record["bytes"] for record in comparisons),
        "parent_rebuild_sha256": parent_receipt["active_parent_sha256"],
        "parent_rebuild_receipt": "PARENT_REBUILD_RECEIPT.json",
        "original_sources_modified": False,
        "scope": "Exact finite reconstruction and byte identity; not a new formal proof of the native compiler or the ZFC endpoint."
    }
    destination = vendor / "REBUILD_RECEIPT.json"
    destination.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({"status": "PASS", "pinned_files_checked": len(checked),
                      "ports": {record["name"]: record["sha256"] for record in comparisons},
                      "receipt": str(destination)}, indent=2))


if __name__ == "__main__":
    main()

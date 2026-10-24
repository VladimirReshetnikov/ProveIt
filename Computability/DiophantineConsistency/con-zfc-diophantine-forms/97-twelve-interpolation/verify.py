#!/usr/bin/env python3
"""Replay finite checks for the three delivered consistency polynomials.

Standard library only. No search for a refutation or a polynomial zero.
The mathematical proofs and their inherited calibration are separate.
"""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def sha(data):
    return hashlib.sha256(data).hexdigest()


def authenticate_inventory():
    path = ROOT / "provenance" / "INHERITED_FILES.json"
    record = json.loads(path.read_text())
    count = 0
    for entry in record["files"]:
        target = ROOT / entry["path"]
        raw = target.read_bytes()
        require(len(raw) == entry["bytes"], "inherited length: " + entry["path"])
        require(sha(raw) == entry["sha256"], "inherited digest: " + entry["path"])
        count += 1
    manifest_path = ROOT / "MANIFEST.json"
    release_count = 0
    if manifest_path.is_file():
        manifest = json.loads(manifest_path.read_text())
        for entry in manifest["files"]:
            raw = (ROOT / entry["path"]).read_bytes()
            require(len(raw) == entry["bytes"], "release length: " + entry["path"])
            require(sha(raw) == entry["sha256"], "release digest: " + entry["path"])
            release_count += 1
    return {"inherited_files": count, "release_files_checked": release_count}


def exact_export(packet, filename):
    delivered = (ROOT / "equations" / filename).read_bytes()
    rebuilt = (json.dumps(packet, indent=2) + "\n").encode()
    require(rebuilt == delivered, "exact graph regeneration: " + filename)
    for field in ["coefficient_binding", "semantic_proof"]:
        require((ROOT / "equations" / packet[field]).resolve().is_file(),
                "resolvable package path: " + field)
    return sha(delivered)


def run():
    inventory = authenticate_inventory()
    base = ROOT / "inherited" / "root_fusion"
    trace = read_module("new_trace_builder", ROOT / "build_trace13.py")
    builder, norm, Ring, audit = trace.load_dependencies(base)
    ports, coefficients = audit.coefficients(base)
    trace_packet = trace.build(builder, norm)
    trace_digest = exact_export(trace_packet, "trace13_degree1072.json")
    trace_receipt = {
        "equation_sha256": trace_digest,
        "structure": trace.check_structure(trace_packet),
        "exact_degree": trace.exact_degree(Ring),
        "transcription": trace.transcription(trace_packet, ports, audit),
    }

    twelve = read_module("new_twelve_builder", ROOT / "build_twelve.py")
    independent = read_module("independent_twelve_checker", ROOT / "check_twelve.py")
    shared = {
        "quintic": independent.check_quintic(),
        "bounds": independent.check_bounds(),
        "interpolation": independent.interpolation_fixtures(),
    }
    twelve_receipts = {}
    for variant, degree in [("product", 4832), ("compact", 16000)]:
        packet = twelve.build(base, variant)
        name = "monotone_intersective12_degree" + str(degree) + ".json"
        digest = exact_export(packet, name)
        twelve_receipts[str(degree)] = {
            "equation_sha256": digest,
            "circuit": independent.circuit_checks(packet, ports),
        }
    return {
        "status": "PASS",
        "scope": "Finite inventories, coefficient reconstruction, algebra, degree and transcription checks.",
        "python_optimized": not __debug__,
        "inventory": inventory,
        "actual_fixed_coefficients": coefficients,
        "twelve_shared_checks": shared,
        "twelve_equations": twelve_receipts,
        "trace_equation": trace_receipt,
        "proof_boundary": (
            "Universal arithmetic proofs are in report/ and proofs/. "
            "Native/compiler and K215 calibration are inherited ordinary proofs. "
            "This receipt is not a proof of consistency or an end-to-end formal theorem certificate."
        ),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()
    receipt = run()
    raw = json.dumps(receipt, indent=2) + "\n"
    if args.receipt:
        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.write_text(raw)
    print(raw)


if __name__ == "__main__":
    main()

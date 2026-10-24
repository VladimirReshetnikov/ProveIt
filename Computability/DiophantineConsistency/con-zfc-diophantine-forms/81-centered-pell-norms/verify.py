#!/usr/bin/env python3
"""Portable release verification. Python standard library only.

This checks literal data, polynomial identities, degree certificates and
reproduction. It is not a consistency test or a proof-assistant kernel.
All validation remains enabled under python -O.
"""
from __future__ import annotations

import gzip
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
PYTHON = [sys.executable] + (["-O"] if sys.flags.optimize else [])
INTEGER_NAMES = ["sextic31", "octic26", "degree10_24", "degree12_25",
                 "degree12_23", "degree14_22"]


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_json(path):
    return json.loads(path.read_text(encoding="utf-8"))


def release_integrity():
    path = ROOT / "MANIFEST.sha256.json"
    if not path.exists():
        return {"status": "development tree; release manifest not yet present"}
    manifest = read_json(path)
    for relative, expected in manifest["files"].items():
        actual = ROOT / relative
        require(actual.is_file(), "missing release file: " + relative)
        require(sha256(actual) == expected, "release hash mismatch: " + relative)
    return {"status": "PASS", "files": len(manifest["files"])}


def pinned_sources():
    pins = read_json(ROOT / "provenance/SOURCE_PINS.json")
    for item in pins["files"]:
        require(sha256(ROOT / item["file"]) == item["sha256"],
                "pinned upstream byte mismatch: " + item["file"])
    return {"status": "PASS", "files": len(pins["files"]),
            "commit": pins["commit"]}


def positive_coefficients():
    binding = read_json(ROOT / "coefficients/ACTIVE_BINDING.json")
    values = {}
    total = 0
    for name, item in binding["ports"].items():
        path = ROOT / "coefficients" / item["gzip_payload"]
        raw = gzip.decompress(path.read_bytes())
        require(hashlib.sha256(raw).hexdigest() == item["sha256"],
                "raw coefficient hash: " + name)
        require(sha256(path) == item["gzip_sha256"],
                "gzip coefficient hash: " + name)
        require(len(raw) == item["raw_bytes"] and raw[-1] != 0,
                "minimal unsigned encoding: " + name)
        value = int.from_bytes(raw, "little")
        require(value.bit_length() == item["bits"],
                "coefficient bit length: " + name)
        values[name] = value
        total += len(raw)
        replay = ROOT / "coefficients/recipe/coefficients" / item["gzip_payload"]
        require(gzip.decompress(replay.read_bytes()) == raw,
                "replayed whole-tuple port: " + name)
    beta = values["beta"]
    require(beta == (1 << 590069) - 1, "literal positive beta")
    require(0 < values["MC"] < beta, "positive native low-mask bounds")
    require(beta < values["MF"] < 2 * beta, "already-shifted high-mask bounds")
    require(values["MC"] % 4 == 2, "low-mask congruence")
    require((values["MF"] - beta) % 8 == 4, "native high-mask congruence")
    return {"status": "PASS", "ports": len(values), "raw_bytes": total,
            "maximum_input_bits": max(v.bit_length() for v in values.values())}


def run(relative, receipts, expected_status="PASS"):
    path = ROOT / relative
    print("Checking " + relative, flush=True)
    env = os.environ.copy()
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    proc = subprocess.run(PYTHON + [str(path)], cwd=path.parent, env=env,
                          capture_output=True, text=True)
    if proc.returncode:
        sys.stderr.write(proc.stdout)
        sys.stderr.write(proc.stderr)
        raise RuntimeError("checker failed: " + relative)
    try:
        result = json.loads(proc.stdout)
    except json.JSONDecodeError as error:
        raise RuntimeError("non-JSON checker output: " + relative) from error
    if isinstance(result, dict) and "status" in result:
        require(result["status"] == expected_status, "unexpected result status: " + relative)
    receipts.append({"script": relative, "status": "PASS"})
    return result


def main():
    integrity = release_integrity()
    provenance = pinned_sources()
    regenerated = ["positive11/p11_positive_degree277.json", "positive12/equation.json"]
    for name in INTEGER_NAMES:
        regenerated += ["integer/" + name + ".json",
                        "integer/" + name + "_circuit.json"]
    before = {name: sha256(ROOT / name) for name in regenerated}
    receipts = []
    run("coefficients/recipe/build_coefficients.py", receipts)
    run("coefficients/recipe/audit_coefficients.py", receipts)
    coefficient_check = positive_coefficients()
    run("positive11/build.py", receipts)
    p11 = run("positive11/audit.py", receipts)
    run("positive12/build.py", receipts)
    p12 = run("positive12/audit.py", receipts)
    run("integer/build.py", receipts)
    run("integer/circuits.py", receipts)
    integer = run("integer/verify.py", receipts)
    closure = run("exploratory/check_homogeneous_closure.py", receipts,
                  "all finite checks passed; universal claims use the written proof")
    for name, expected in before.items():
        require(sha256(ROOT / name) == expected,
                "regeneration changed delivered polynomial/circuit: " + name)
    endpoints = []
    for item in integer["circuit_replays"]:
        if item["name"] != "degree12_25":
            endpoints.append({"name": item["name"], "domain": "unrestricted integers",
                              "variables": item["variables"],
                              "exact_degree": item["exact_degree"],
                              "binary_operations": item["binary_operations"]})
    endpoints += [
        {"name": "p11_positive_degree277", "domain": "strictly positive integers",
         "variables": 11, "exact_degree": 277,
         "binary_operations": p11["literal"]["operations"]},
        {"name": "p12_positive_degree78", "domain": "strictly positive integers",
         "variables": 12, "exact_degree": p12["exact_degree"],
         "binary_operations": p12["live_binary_operations"]},
    ]
    require(len(endpoints) == 7, "seven reported endpoints")
    receipt = {"status": "PASS", "python_optimization": bool(sys.flags.optimize),
               "release_integrity": integrity, "provenance": provenance,
               "positive_coefficient_check": coefficient_check,
               "byte_identical_regenerated_packets_and_circuits": len(before),
               "checks": receipts, "endpoints": endpoints,
               "exploratory_closure_status": closure["status"],
               "proof_boundary": "Exact finite data and algebra checks plus ordinary mathematical proofs; inherited native/compiler calibration, no new end-to-end formal or object-language ZFC derivation."}
    output = ROOT / "validation/VERIFICATION.json"
    output.parent.mkdir(exist_ok=True)
    output.write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()

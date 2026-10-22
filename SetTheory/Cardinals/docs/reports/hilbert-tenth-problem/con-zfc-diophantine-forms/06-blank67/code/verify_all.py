#!/usr/bin/env python3
"""Reproduce the bundle's finite checks without executing historical sources.

Only the five neighboring Python entry points are executed. Copied upstream
files are read as data. A PASS is not a proof-assistant certification of the
mathematical reductions or a decision of Con(ZFC); see the receipt's limits.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
import tempfile


PIN = "cdd582bec13f908df3711fa9e05d1ddac368a5db"
TM_REL = "Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm"
LEAN_REL = "Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KDense215.lean"
ROCQ_REL = "Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/coq/215/Table215.v"
PARENT_REL = "Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete84_scaled_strong_output.json"
SOURCE_PINS = {
    TM_REL: "fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090",
    LEAN_REL: "b1ebe573ced4b336ead43dbe7278ad97c8d28c06412b43c7291d051b98c6395a",
    ROCQ_REL: "7bf3b9a5e37dadcb1091a8af0ccfc512e2704d7bd5f75cfb4563d42842d1d4a8",
    PARENT_REL: "8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf",
}
# name -> (operation count, quantified variables, degree, equation count)
PACKETS = {
    "fixed_blank_67": (67, 15, 155, 1),
    "fixed_blank_68": (68, 15, 123, 1),
    "fixed_blank_system_61": (61, 15, 60, 6),
    "fixed_blank_system_62": (62, 15, 46, 6),
    "fixed_blank_67_over_Z41": (158, 41, 310, 1),
    "fixed_blank_68_over_Z41": (159, 41, 246, 1),
}
PORTS = ["Bm1", "Kconstant", "MC", "MF"]
LIMITS = [
    "Finite executable checks and algebra diagnostics supplement the mathematical proofs; they do not establish the unbounded reductions by exhaustive testing.",
    "Lean and Rocq transition literals are parsed and compared, but neither proof assistant nor the full K215 proof dependency graph is rebuilt.",
    "The giant window alphabet and fixed numerals are specified by closed finite expressions; they are not enumerated or expanded as binary or decimal numerals.",
    "No accepting K215 computation, full Pell witness, or decision of Con(ZFC) is produced.",
]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read_json(path):
    return json.loads(path.read_text(encoding="utf-8"))


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def first_difference(actual, expected, path="$"):
    """Type-sensitive JSON comparison, reporting the first differing field."""
    if type(actual) is not type(expected):
        return f"{path}: types {type(actual).__name__} and {type(expected).__name__}"
    if isinstance(actual, dict):
        if actual.keys() != expected.keys():
            return f"{path}: object keys differ"
        for key in sorted(actual):
            difference = first_difference(actual[key], expected[key], path + "." + key)
            if difference:
                return difference
    elif isinstance(actual, list):
        if len(actual) != len(expected):
            return f"{path}: list lengths {len(actual)} and {len(expected)}"
        for index, (left, right) in enumerate(zip(actual, expected)):
            difference = first_difference(left, right, f"{path}[{index}]")
            if difference:
                return difference
    elif actual != expected:
        return f"{path}: {str(actual)[:120]!r} differs from {str(expected)[:120]!r}"
    return None


def equal_json(actual, expected, label):
    difference = first_difference(actual, expected, "$")
    require(difference is None, f"{label}: {difference}")


def manifest_check(root, supplied):
    path = supplied if supplied is not None else root / "data/upstream_manifest.json"
    if not path.exists():
        require(supplied is None, f"Requested manifest is missing: {path}")
        return {"status": "NOT_PRESENT", "files_checked": 0}
    manifest = read_json(path)
    require(manifest.get("commit") == PIN, "Upstream manifest commit differs from the pinned commit")
    entries = manifest["files"]
    require(isinstance(entries, list) and entries, "Upstream manifest has no file entries")
    seen = set()
    byte_count = 0
    for entry in entries:
        relative = PurePosixPath(entry["path"])
        require(not relative.is_absolute() and relative.parts[0] == "upstream"
                and ".." not in relative.parts, f"Invalid upstream manifest path: {relative}")
        require(str(relative) not in seen, f"Duplicate upstream manifest path: {relative}")
        seen.add(str(relative))
        target = (root / relative).resolve()
        require(target.is_relative_to(root), f"Manifest path leaves the bundle: {relative}")
        raw = target.read_bytes()
        require(type(entry["bytes"]) is int and len(raw) == entry["bytes"],
                f"Upstream file size differs: {relative}")
        require(re.fullmatch(r"[0-9a-f]{64}", entry["sha256"]) is not None,
                f"Malformed SHA-256 in manifest: {relative}")
        require(hashlib.sha256(raw).hexdigest() == entry["sha256"],
                f"Upstream SHA-256 differs: {relative}")
        byte_count += len(raw)
    require({"upstream/" + path for path in SOURCE_PINS} <= seen,
            "The upstream manifest omits a required pinned arithmetic or machine source")
    return {"status": "PASS", "files_checked": len(seen), "bytes_checked": byte_count}


def run(root, script, arguments):
    """Capture child output so the wrapper emits exactly one JSON receipt."""
    environment = dict(os.environ)
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    command = [sys.executable, "-B", str(root / "code" / script)]
    command.extend(str(value) for value in arguments)
    completed = subprocess.run(command, cwd=root, env=environment,
                               text=True, capture_output=True, check=False)
    if completed.returncode:
        details = (completed.stderr or completed.stdout).strip()[-2400:]
        raise ValueError(f"{script} exited {completed.returncode}: {details}")


def without_direct_enumeration(receipt):
    """Project a full count receipt to the portion rebuilt by --quick."""
    result = json.loads(json.dumps(receipt))
    result.pop("independent_direct_predicate_enumeration")
    for category in result["categories"]:
        category.pop("direct_crosses_per_center")
    return result


def verify(root, quick=False, manifest=None):
    root = root.resolve()
    upstream = root / "upstream"
    data = root / "data"
    checks = {"upstream_manifest": manifest_check(root, manifest)}
    for relative, expected in SOURCE_PINS.items():
        require(digest(upstream / relative) == expected, f"Hardcoded source pin differs: {relative}")
    checks["independent_source_pins"] = {"status": "PASS", "files_checked": len(SOURCE_PINS)}

    with tempfile.TemporaryDirectory(prefix="proveit-k215-check-") as temporary:
        fresh = Path(temporary)
        run(root, "build_fixed.py", ["--repo", upstream, "--output", fresh / "fixed_blank_67.json"])
        packet_metrics = []
        for name, expected_metrics in PACKETS.items():
            receipt = read_json(fresh / (name + ".json"))
            equal_json(receipt, read_json(data / (name + ".json")), name)
            packet = receipt.get("packet", receipt)
            if "packet" in receipt:
                require(receipt["status"] == "PASS", f"{name} has no PASS receipt")
            degree = packet.get("exact_degree")
            if degree is None:
                degree = max(packet["residual_exact_degrees"])
            metrics = (packet["ledger"]["operations"], len(packet["witnesses"]),
                       degree, len(packet.get("comparisons", [None])))
            require(metrics == expected_metrics, f"{name}: unexpected metrics {metrics}")
            require(packet["ledger"]["all_gates_live"] and packet["ledger"]["all_ports_live"],
                    f"{name}: unused source gates or ports")
            equal_json(packet["fixed_numerals"], PORTS, name + " fixed numeral ports")
            packet_metrics.append({"name": name, "operations": metrics[0],
                                   "variables": metrics[1], "degree": metrics[2],
                                   "equations": metrics[3]})
        checks["gate_packets"] = {"status": "PASS", "exact_json_matches": len(PACKETS),
                                   "metrics": packet_metrics}

        run(root, "verify_k215.py", ["--repo", upstream, "--output", fresh / "k215_transitions.json"])
        machine = read_json(fresh / "k215_transitions.json")
        equal_json(machine, read_json(data / "k215_transitions.json"), "K215 transition receipt")
        require(machine["repository_commit"] == PIN, "Machine receipt has the wrong commit")
        for name, relative in (("tm", TM_REL), ("lean", LEAN_REL), ("rocq", ROCQ_REL)):
            require(machine["source_sha256"][name] == SOURCE_PINS[relative],
                    f"Machine receipt has the wrong {name} source hash")
        require(machine["transition_count"] == 430 and machine["lean_literal_match"]
                and machine["rocq_literal_match"], "Machine literal comparisons failed")
        checks["k215_machine"] = {"status": "PASS", "transitions": 430,
                                  "lean_and_rocq_literals_match": True,
                                  "bootstrap_steps": machine["bootstrap"]["steps"]}

        run(root, "blank_helical.py", ["--tm", upstream / TM_REL,
                                       "--output", fresh / "blank_helical_checks.json"])
        blank = read_json(fresh / "blank_helical_checks.json")
        equal_json(blank, read_json(data / "blank_helical_checks.json"), "Blank tableau receipt")
        require(blank["S_and_E_center_predicates"] and blank["E_excluded_by_prior_vertical_propagation"],
                "Start/excluded-selector checks failed")
        checks["blank_tableau"] = {"status": "PASS",
                                   "halting_control_presentations": blank["halting_control_presentations"],
                                   "local_windows_and_overlaps": blank["local_windows_and_overlaps_checked"],
                                   "vertical_seam_windows": blank["vertical_seam_windows_checked"]}

        count_args = ["--tm", upstream / TM_REL, "--output", fresh / "blank_alphabet_cardinality.json"]
        if quick:
            count_args.append("--formula-only")
        run(root, "count_blank_alphabet.py", count_args)
        alphabet = read_json(fresh / "blank_alphabet_cardinality.json")
        saved_alphabet = read_json(data / "blank_alphabet_cardinality.json")
        if quick:
            equal_json(without_direct_enumeration(alphabet), without_direct_enumeration(saved_alphabet),
                       "Alphabet count formula receipt")
        else:
            equal_json(alphabet, saved_alphabet, "Alphabet count receipt")
        require(alphabet["independent_direct_predicate_enumeration"] is (not quick),
                "Unexpected direct predicate enumeration mode")
        checks["alphabet_cardinality"] = {"status": "PASS",
                                          "direct_representative_enumeration": not quick,
                                          "representative_categories": len(alphabet["categories"]),
                                          "valid_crosses": alphabet["valid_crosses"],
                                          "windows": alphabet["lifted_alphabet_cardinality"]}

        run(root, "compiler_constants.py", ["--output", fresh / "k215_constants.json"])
        constant_receipt = read_json(fresh / "k215_constants.json")
        equal_json(constant_receipt, read_json(data / "k215_constants.json"), "Fixed coefficient recipe")
        constants = constant_receipt["constants"]
        require(constant_receipt["verification"]["status"] == "PASS", "Compiler checks failed")
        equal_json(constants["free_parameters"], [], "Fixed coefficient recipe free parameters")
        equal_json(constants["polynomial_ports"], PORTS, "Fixed coefficient recipe ports")
        require(constants["machine_sha256"] == machine["source_sha256"]["tm"], "Compiler/TM hash mismatch")
        require(constants["alphabet_size"] == blank["alphabet_size"], "Compiler/tableau alphabet mismatch")
        require(constants["valid_crosses"] == alphabet["valid_crosses"] and
                constants["window_count"] == alphabet["lifted_alphabet_cardinality"],
                "Compiler/alphabet cardinality mismatch")
        equal_json(constants["window_order"]["first"], blank["S"], "Start selector binding")
        equal_json(constants["window_order"]["second"], blank["E"], "Excluded selector binding")
        checks["fixed_constants"] = {"status": "PASS", "free_parameters": 0,
                                     "polynomial_ports": len(PORTS),
                                     "toy_sparse_compilers": len(constant_receipt["verification"]["toy_sparse_compilers"])}
        checks["machine_tableau_constants_packet_bindings"] = {"status": "PASS"}

    limits = list(LIMITS)
    if quick:
        limits.append("Quick mode skips the independent direct local-predicate enumeration for the thirteen center-type representatives; the count formulas are still recomputed.")
    if checks["upstream_manifest"]["status"] == "NOT_PRESENT":
        limits.append("No upstream manifest was present; only the four independently hardcoded essential source hashes were checked.")
    return {"schema": "proveit-zfc-diophantine-verification-v1", "status": "PASS",
            "mode": "quick" if quick else "full", "repository_commit": PIN,
            "checks": checks, "limits": limits}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1],
                        help="bundle directory (default: parent of this code directory)")
    parser.add_argument("--manifest", type=Path, help="override data/upstream_manifest.json")
    parser.add_argument("--quick", action="store_true", help="skip direct representative local-predicate counts")
    parser.add_argument("--output", type=Path, help="also save the JSON receipt to this file")
    args = parser.parse_args()
    try:
        receipt = verify(args.root, args.quick, args.manifest)
    except Exception as error:
        receipt = {"schema": "proveit-zfc-diophantine-verification-v1", "status": "FAIL",
                   "mode": "quick" if args.quick else "full", "error": f"{type(error).__name__}: {error}"}
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(receipt, sort_keys=True))
    return 0 if receipt["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())

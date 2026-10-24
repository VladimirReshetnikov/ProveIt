#!/usr/bin/env python3
"""Replay the exact finite checks of this research packet, entirely offline.

This does not decide existence of zeros or rebuild the inherited Lean/native
calibration. Unbounded equivalence arguments are in the report and proof notes.
Requires Python 3.10 or later and only its standard library.
"""
from collections import Counter
import gzip
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
RECEIPTS = ROOT / "verification"
PIN = "84e16e43092614bae262ca59651cb9d77e31a255"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(path):
    return json.loads(path.read_text())


def run(label, cwd, *arguments):
    command = [sys.executable, "-B", *arguments]
    process = subprocess.run(command, cwd=ROOT / cwd, text=True,
                             stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (RECEIPTS / (label + ".txt")).write_text(process.stdout)
    require(process.returncode == 0,
            label + " failed; see verification/" + label + ".txt")
    print("PASS:", label, flush=True)
    return {"label": label, "directory": cwd, "command": ["python3", "-B", *arguments],
            "exit_code": process.returncode,
            "output_sha256": digest(RECEIPTS / (label + ".txt"))}


def check_bfs():
    reconstructed = load(ROOT / "positive/coefficients_bfs/RECONSTRUCTION.json")
    values = {}
    records = {}
    for number in (96, 98, 102, 104):
        name = "equation" + str(number) + ".json"
        old = load(ROOT / "positive" / name)
        path = ROOT / "positive/bfs" / name
        new = load(path)
        for key in ("domain", "fixed_numerals", "witnesses", "source", "output",
                    "operations", "operation_breakdown", "exact_degree",
                    "syntactic_degree", "register_degrees", "transport_majorant"):
            require(new[key] == old[key], "BFS uniform arithmetic field: " + key)
        require(new["source_pin"] == new["coefficient_source_commit"] == PIN, "BFS source pin")
        require(digest(path.parent / new["parent_local_file"]) == new["parent_sha256"],
                "BFS pinned arithmetic parent")
        require(digest(path.parent / new["coefficient_recipe"]) == new["coefficient_recipe_sha256"],
                "BFS printed coefficient recipe")
        require((path.parent / new["proof"]).is_file(), "BFS proof pointer")
        binding = new["coefficient_binding"]
        require(binding["ports"] == reconstructed["ports"], "whole BFS tuple binding")
        for port, spec in binding["ports"].items():
            payload = path.parent / binding["path"] / spec["file"]
            compressed = payload.read_bytes()
            raw = gzip.decompress(compressed)
            value = int.from_bytes(raw, "little")
            require(hashlib.sha256(compressed).hexdigest() == spec["gzip_sha256"],
                    "BFS gzip " + port)
            require(hashlib.sha256(raw).hexdigest() == spec["raw_sha256"], "BFS raw " + port)
            require(value.bit_length() == spec["bits"], "BFS bit length " + port)
            values[port] = value
        rows = new["source"]
        available = set(new["witnesses"] + new["fixed_numerals"])
        counts = Counter()
        for register, operator, left, right in rows:
            require(register not in available, "unique register")
            require(operator in ("+", "-", "*"), "polynomial operation")
            require(all(isinstance(a, int) or a in available for a in (left, right)), "topological order")
            available.add(register)
            counts[operator] += 1
        require(len(rows) == new["operations"] and dict(counts) == new["operation_breakdown"],
                "BFS circuit census")
        require(new["output"] in available, "defined output")
        records[name] = {"operations": len(rows), "exact_degree": new["exact_degree"],
                         "same_arithmetic_graph_as_checked_original": True,
                         "sha256": digest(path)}
    beta, k0, mc, mf = (values[k] for k in ("beta", "K0", "MC", "MF"))
    require(beta % 2 == 1 and beta >= 31 and k0 > 0 and 0 < mc < beta < mf < 2 * beta,
            "uniform positive arithmetic coefficient conditions")
    return {"whole_printed_recipe_reconstructed": True,
            "all_four_complete_payloads_authenticated": True, "circuits": records}


def check_positive_proof_pins():
    pins = load(ROOT / "POSITIVE_PROOF_PINS.json")
    require(pins["commit"] == PIN, "positive proof source commit")
    for item in pins["files"]:
        raw = (ROOT / item["local"]).read_bytes()
        require(hashlib.sha256(raw).hexdigest() == item["sha256"], "positive proof SHA256")
        blob = hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()
        require(blob == item["git_blob"], "positive proof immutable Git blob")
    return len(pins["files"])


def main():
    if sys.version_info < (3, 10):
        raise RuntimeError("Python 3.10 or later is required")
    RECEIPTS.mkdir(exist_ok=True)
    checks = [
        run("positive_build", "positive", "build.py", "--check"),
        run("positive_algebra", "positive", "verify.py", "--check"),
        run("integer_norms", "integer", "verify_symmetric_norms.py"),
        run("quartic_pairs", "quartic", "check_pair_guards.py"),
        run("quartic_final", "quartic", "check_fused68.py"),
        run("bfs_constants", ".", "reconstruct_constants.py"),
        run("quartic_plaintext", ".", "export_quartic_text.py", "--check"),
    ]
    bfs = check_bfs()
    positive_proof_files = check_positive_proof_pins()
    receipt_names = [
        "positive/CHECKS.json", "integer/VERIFICATION.json",
        "quartic/CHECK_PAIR_GUARDS.json", "quartic/CHECK_FUSED68.json",
        "positive/coefficients_bfs/RECONSTRUCTION.json",
    ]
    receipts = {name: digest(ROOT / name) for name in receipt_names}
    summary = {
        "status": "PASS", "source_commit": PIN, "checks": checks,
        "bfs_variants": bfs, "receipt_sha256": receipts,
        "positive_proof_files_authenticated": positive_proof_files,
        "principal_claims": load(ROOT / "PROVENANCE.json")["claims"],
        "scope": ("Exact identities, source hashes, complete finite specifications, "
                  "degree/count certificates, and integral projection restoration. "
                  "Unbounded equivalence is proved in the supplied ordinary mathematics, "
                  "with the explicitly inherited source/refutation calibration. "
                  "No new Lean/Rocq build or object-ZFC derivation is asserted."),
    }
    (ROOT / "VERIFICATION_SUMMARY.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print("PASS: all exact checks; see VERIFICATION_SUMMARY.json", flush=True)


if __name__ == "__main__":
    main()


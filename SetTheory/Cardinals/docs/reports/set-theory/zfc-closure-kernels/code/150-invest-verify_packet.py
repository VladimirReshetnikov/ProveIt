#!/usr/bin/env python3
"""Quick, offline checks of this research packet; no new <=217 result claimed.

The finite derivations, countermodels, exact core construction, blank-start
obstruction, accepted startup control, and source grammars are replayed.
The large search receipts and full symbolic-runtime census are checked as
recorded evidence, not regenerated. To regenerate the latter, run:
    python3 -B core217/check_core.py --runtime --output /tmp/core217-fresh
"""
from pathlib import Path
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads((ROOT / path).read_text())


def check_manifest(path):
    count = 0
    for line in path.read_text().splitlines():
        if not line.strip():
            continue
        expected, name = line.split(maxsplit=1)
        name = name.lstrip("*")
        relative = Path(name)
        require(not relative.is_absolute() and ".." not in relative.parts,
                "Unsafe manifest entry: " + name)
        require(digest(path.parent / relative) == expected,
                "Manifest mismatch: " + str(path.parent / relative))
        count += 1
    print("MANIFEST_PASS", path.relative_to(ROOT), count, flush=True)


def run(script, *args):
    command = [sys.executable, "-B", str(script), *map(str, args)]
    result = subprocess.run(command, capture_output=True, text=True)
    if result.returncode:
        sys.stdout.write(result.stdout)
        sys.stderr.write(result.stderr)
        raise RuntimeError("Replay failed: " + str(script))
    print(result.stdout.strip(), flush=True)


def main():
    require(__debug__ and not sys.flags.optimize, "Keep assertions enabled.")
    require(sys.version_info >= (3, 11), "Python 3.11 or later is required.")
    manifest = ROOT / "SHA256SUMS"
    require(manifest.is_file(), "The complete delivered manifest is required.")
    check_manifest(manifest)
    for relative in ("source-search/SHA256SUMS", "machine-search/MANIFEST.sha256",
                     "root-search/MANIFEST.sha256"):
        check_manifest(ROOT / relative)
    for name, expected in read("input-pins.json").items():
        require(digest(ROOT / name) == expected, "Input pin mismatch: " + name)

    with tempfile.TemporaryDirectory(prefix="zfc217-verify-") as scratch:
        scratch = Path(scratch)
        theory = scratch / "formalism"
        shutil.copytree(ROOT / "formalism", theory)
        for script, outputs in (
            ("check_self_vacuity.py", ("self_vacuity_proof_dag.json",
                                      "self_vacuity_proof_receipt.json")),
            ("check_fixed_b_countermodels.py", ("fixed_b_countermodels_receipt.json",)),
            ("check_persistent_negation.py", ("persistent_negation_receipt.json",)),
        ):
            run(theory / script)
            for output in outputs:
                require((theory / output).read_bytes() ==
                        (ROOT / "formalism" / output).read_bytes(),
                        "Regenerated certificate differs: " + output)
        run(ROOT / "core217/check_core.py", "--output", scratch / "core")
        for output in ("construction_and_failure.json", "blank_trace.json"):
            require((scratch / "core" / output).read_bytes() ==
                    (ROOT / "core217/evidence" / output).read_bytes(),
                    "Regenerated core evidence differs: " + output)
        run(ROOT / "source-search/src/verify_packet.py")

    receipt = read("formalism/self_vacuity_proof_receipt.json")
    require(receipt["nodes"] == 1110 and len(receipt["outputs"]) == 5,
            "Hilbert endpoint census changed.")
    require(all(item["closed"] for item in receipt["outputs"].values()),
            "An endpoint has open assumptions.")
    require(receipt["proof_sha256"] ==
            digest(ROOT / "formalism/self_vacuity_proof_dag.json"),
            "Hilbert proof hash mismatch.")

    runtime = read("core217/evidence/runtime.json")
    cases = read("core217/evidence/cases.json")
    sites = read("baseline218/sites218.json")
    require(runtime["status"] == "ALL_PRIMITIVE_INTERFACES_PROVED",
            "Incomplete recorded runtime.")
    require((runtime["states"], runtime["rows"], runtime["direct_rows"],
             runtime["cases"], runtime["symbolic_steps"]) ==
            (217, 434, 434, 6167, 1515310), "Runtime census changed.")
    expected = {(i, positive) for i, site in enumerate(sites)
                for positive in ((False, True) if site[1] == "CD" else (False,))}
    actual = {(case["index"], case["positive"]) for case in cases}
    require(actual == expected and len(cases) == len(expected),
            "Guarded primitive cases are missing or repeated.")
    require(sum(case["symbolic_steps"] for case in cases) == 1515310,
            "Symbolic rule sum mismatch.")
    require(min(case["duration"][0] for case in cases) == 12,
            "Minimum finite duration mismatch.")
    require(all(len(case["duration"]) == 13 and
                all(v >= 0 for v in case["duration"][1:]) for case in cases),
            "Invalid recorded affine duration.")
    require(runtime["negative_control"]["status"] == "REJECTED",
            "Runtime negative control did not reject.")
    require(runtime["driver_sha256"] == digest(ROOT / "core217/check_core.py"),
            "Runtime driver differs from the recorded replay.")
    for name, expected_hash in runtime["pins"].items():
        require(digest(ROOT / name) == expected_hash, "Runtime pin drift: " + name)
    print("RECORDED_RUNTIME_CENSUS_PASS (full proof is a separate replay)", flush=True)

    searches = read("machine-search/SUMMARY.json")["all_pair_synthesis"]
    for name in ("twoaction_allpairs_allinitial", "twoaction_allpairs_masked"):
        item = searches[name]
        require(item["pairs_complete"] == 23653 and
                item["complete_assignments_rejected"] == 17985362752 and
                item["survivors"] == 0, "Changed two-action receipt: " + name)
    item = searches["flipped_fast"]
    require(item["pairs_complete"] == 4886 and
            item["complete_assignments_rejected"] == 3715236224 and
            item["survivors"] == 0, "Changed complemented-marker receipt.")
    allocation = read("source-search/results/allocation_final.json")
    require(allocation["distinct"] == 1190 and allocation["best"] == 218 and
            allocation["counts"]["allocation_error"] == 837 and
            allocation["counts"]["states_218"] == 36,
            "Changed source allocation receipt.")
    root = read("root-search/SUMMARY.json")
    require(root["preliminary_correction"]["completed_symbolic_rejections"] == 40,
            "Incomplete corrected-fold census.")
    single = root["initializers"]["one_edit_every_start"]
    require(single["cases"] == single["edits"] * single["initial_states"] == 106764
            and single["rays"] == 106764 and single["frames"] == 0
            and single["limits"] == 0 and single["halts"] == 0,
            "Changed single-edit initializer census.")
    paired = root["initializers"]["two_edits_start_zero"]
    require(paired["distinct_row_pairs"] == 118928 and paired["rays"] == 118838
            and paired["limits"] == 90 and paired["frames"] == 0
            and paired["halts"] == 0, "Changed paired-initializer census.")
    print("RECORDED_SEARCH_CENSUS_PASS (large searches not rerun)", flush=True)
    print("QUICK_PACKET_CHECKS_PASS; no <=217 blank-tape consistency machine claimed.")


if __name__ == "__main__":
    main()

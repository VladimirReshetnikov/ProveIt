#!/usr/bin/env python3
"""Offline replay of the 243-state construction and its finite proof premises.

The default replay rebuilds both tables and the exact blank startup, checks
the independent local simulation, replays the complete source rotation and
frame closure, and checks all universal affine instruction cases.  --expanded
also reruns the complete expanded whole-tape symbolic proof on the actual
243-state table.  No network or proof-assistant installation is used.

Results go to a fresh directory, never into the delivered evidence files.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import zipfile

ROOT = Path(__file__).resolve().parents[1]
REFERENCE_NAME = "zfc244-loop-rotation-20261018"
REFERENCE_SHA = "2609ff9ff0c6c0a2ba7619bcfad7e7480f3d9052dd32c161149e6a721c25a54a"
REFERENCE_BLOB = "663925a900262cb01eaf112b824dd957b4d497ba"
OLD_SHA = "4207fc3d1bb16f3c64c3cff0980eaa1486160c3f467aee7685740a39e3df7300"
CANONICAL_SHA = "a3860fb49d6b96e58ead6293134f246d59b3958231cb56850273c4b8a8138791"
SOURCE_SHA = "3ee984818f0bdfd2c4daae72aeb14340572e34d73f5cdb5616b6d29d78fcd7f4"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_json(path):
    return json.loads(path.read_text())


def manifest(root):
    path = root / "SHA256SUMS"
    require(path.is_file(), "The complete package manifest is required.")
    checked = 0
    names = set()
    for line in path.read_text().splitlines():
        expected, name = line.split("  ", 1)
        require(name not in names, "Duplicate manifest entry.")
        names.add(name)
        target = (root / name).resolve()
        require(target.is_relative_to(root.resolve()), "Manifest path escapes package.")
        require(target.is_file() and digest(target) == expected, f"Hash mismatch: {name}")
        checked += 1
    return checked


def inspect_expanded(record, machine):
    require(record["status"] == "PASS_UNIVERSAL_EXPANDED_RUNTIME", "Expanded proof failed.")
    require(record["complete"] is True, "Expanded proof is incomplete.")
    require(record["table_sha256"] == OLD_SHA, "Expanded proof has the wrong table.")
    require(record["sites_logical_sha256"] == SOURCE_SHA, "Wrong expanded source identity.")
    require(record["counts"] == {"cases": 8390, "symbolic_rules": 2314868},
            "Wrong expanded proof census.")
    require(record["rules"] == {"literal": 1987184, "unary-induction": 322484,
                                "finite-list-induction": 5200}, "Wrong proof-rule census.")
    require(record["literal_rows_covered"] == 485 and record["unused_rows"] == [[27, 1]],
            "Wrong transition coverage.")
    for key in ("arbitrary_primary_registers", "arbitrary_nonempty_finite_spare_suffix",
                "positive_progress_checked"):
        require(record[key] is True, f"Missing quantified proof property: {key}")
    require(record["frame_padding"] == 64, "Wrong frame padding.")
    sites = read_json(machine / "sites_logical.json")
    expected = [(i, p, op, r, zero) for i, (p, op, r) in enumerate(sites)
                for zero in ((True, False) if op == "CD" else (None,))]
    observed = [(c["index"], c["pc"], c["op"], c["r"], c["zero"])
                for c in record["cases"]]
    require(observed == expected, "Expanded case inventory differs from the complete source.")
    require(min(c["time_lower_bound"] for c in record["cases"]) == 13,
            "Wrong positive-progress lower bound.")


def main():
    if not __debug__:
        raise RuntimeError("The inherited proof engine uses assertions; do not run with -O.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--expanded", action="store_true",
                        help="Freshly replay all expanded whole-frame cases (several minutes).")
    parser.add_argument("--output", type=Path, help="New or empty result directory.")
    args = parser.parse_args()
    out = args.output.resolve() if args.output else Path(tempfile.mkdtemp(prefix="zfc243-replay-"))
    require(not out.exists() or (out.is_dir() and not any(out.iterdir())),
            "Output must be a new or empty directory.")
    out.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    packet_files = manifest(ROOT)
    archive_path = ROOT / "reference" / (REFERENCE_NAME + ".zip")
    raw = archive_path.read_bytes()
    require(hashlib.sha256(raw).hexdigest() == REFERENCE_SHA, "Wrong inherited archive.")
    header = b"blob " + str(len(raw)).encode("ascii") + b"\0"
    require(hashlib.sha1(header + raw).hexdigest() == REFERENCE_BLOB,
            "Inherited archive does not match the pinned Git blob.")
    unpacked = out / "inherited"
    unpacked.mkdir()
    with zipfile.ZipFile(archive_path) as archive:
        for member in archive.infolist():
            target = (unpacked / member.filename).resolve()
            require(target.is_relative_to(unpacked.resolve()), "Archive path escapes extraction.")
            require((member.external_attr >> 16) & 0o170000 != 0o120000,
                    "Reference archive must not contain symbolic links.")
        archive.extractall(unpacked)
    rotation = unpacked / REFERENCE_NAME
    reference = rotation / "reference/baseline245"
    inherited_files = manifest(rotation)
    baseline_files = manifest(reference)
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
    env.pop("PYTHONOPTIMIZE", None)
    py = [sys.executable, "-B"]
    completed = []

    def run(name, command):
        print(f"Checking {name} ...", flush=True)
        with (out / (name + ".log")).open("w") as stream:
            result = subprocess.run([str(x) for x in command], cwd=ROOT, env=env,
                                    stdout=stream, stderr=subprocess.STDOUT)
        if result.returncode:
            log = (out / (name + ".log")).read_text()
            raise RuntimeError(f"{name} failed:\n{log[-10000:]}")
        completed.append(name)
        print(f"PASS {name}", flush=True)

    machine = out / "machine"
    run("exact-construction-and-blank", py + [ROOT / "code/build_composed243.py",
        "--rotation", rotation, "--output", machine, "--boot"])
    for name in ("machine.tm", "machine_old.tm", "renumbering.json", "sites_logical.json",
                 "sites_physical.json", "boot.json", "construction.json"):
        require((machine / name).read_bytes() == (ROOT / "machine" / name).read_bytes(),
                f"Reconstruction changed {name}")
    require(digest(machine / "machine.tm") == CANONICAL_SHA, "Wrong canonical table.")

    run("independent-local-composition", py + [ROOT / "code/audit_composition.py",
        reference / "certificate/machine_old.tm", rotation / "machine/machine_old.tm",
        machine / "machine_old.tm", "--output", out / "composition-audit.json"])
    local = read_json(out / "composition-audit.json")
    require(local["status"] == "PASS_INDEPENDENT_243_COMPOSITION_AUDIT", "Local audit failed.")
    require(local["reduction"]["ordinary_equal_rows"] == 480, "Wrong ordinary row count.")

    run("universal-source-rotation", py + [rotation / "code/check_qt_rotation.py",
        "--reference", reference, "--output", out / "source-rotation"])
    source = read_json(out / "source-rotation/right/source_verification.json")
    require(source["status"] == "PASS_UNIVERSAL_SOURCE_EQUIVALENCE", "Source proof failed.")
    require(source["context_edges_checked"] == 8385 and source["new_guarded_cases"] == 8390,
            "Wrong source proof inventory.")
    for name in ("sites_logical.json", "sites_physical.json"):
        require((out / "source-rotation/right" / name).read_bytes() == (machine / name).read_bytes(),
                "Source proof does not match the compiled source.")

    run("independent-frame-closure", py + [ROOT / "code/check_composed_frames.py",
        "--machine", machine, "--output", out / "frame-composition.json"])
    frame = read_json(out / "frame-composition.json")
    require(frame["status"] == "PASS" and frame["nonhalting_successors_normalized"] == 8389,
            "Incomplete frame closure.")

    run("all-universal-affine-cases", py + [ROOT / "code/check_composed_runtime.py",
        "--reference", reference, "--candidate", machine])
    affine = read_json(machine / "affine-runtime.json")
    require(affine["status"] == "PASS_UNIVERSAL_AFFINE_RUNTIME" and affine["complete"],
            "Affine replay failed.")
    require(affine["counts"]["cases"] == 8390, "Incomplete affine replay.")

    if args.expanded:
        run("all-expanded-whole-frame-cases", py + [ROOT / "code/check_composed_runtime.py",
            "--reference", reference, "--candidate", machine, "--expanded"])
        expanded = read_json(machine / "expanded-runtime.json")
    else:
        expanded = read_json(ROOT / "certificate/expanded-runtime.json")
    inspect_expanded(expanded, machine)

    run("finite-algebra-semantic-controls", py + [ROOT / "research/finite-algebra/finite_algebra.py",
        "--output", out / "finite-algebra-results.json"])
    finite = read_json(out / "finite-algebra-results.json")
    require(finite == read_json(ROOT / "research/finite-algebra/finite_algebra_results.json"),
            "Finite-algebra reference evidence changed.")

    result = {
        "status": "PASS_243_FULL_REPLAY" if args.expanded else "PASS_243_FAST_REPLAY",
        "working_states": 243, "binary_rows": 486, "canonical_sha256": CANONICAL_SHA,
        "old_label_sha256": OLD_SHA, "source_sha256": SOURCE_SHA,
        "exact_blank_steps": 407967, "ordinary_equal_rows": 480, "local_cases": 7,
        "source_context_edges": 8385, "universal_guarded_cases": 8390,
        "nonhalting_successors_normalized": 8389,
        "expanded_freshly_replayed": args.expanded, "expanded_symbolic_rules": 2314868,
        "expanded_runtime_rows_used": 485, "retained_unused_runtime_row": [27, 1],
        "minimum_expanded_progress": 13, "packet_manifest_files": packet_files,
        "inherited_manifest_files": inherited_files, "baseline_manifest_files": baseline_files,
        "reference_archive_sha256": REFERENCE_SHA, "steps_completed": completed,
        "seconds": round(time.monotonic() - started, 3),
        "scope": "Ordinary mathematical proof-premise replay; no new proof-assistant endpoint.",
        "output": str(out),
    }
    (out / "verification-summary.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2), flush=True)


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Verify deliverable hashes and every frozen experiment/source binding."""
from __future__ import annotations

import argparse
from hashlib import sha256
import json
from pathlib import Path


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def package_hashes(path):
    return {str(p.relative_to(path)): digest(p) for p in sorted(path.rglob("*.py"))}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    args = parser.parse_args()
    root = args.root.resolve()
    manifest = json.loads((root / "MANIFEST.json").read_text())
    for item in manifest["files"]:
        relative = Path(item["path"])
        assert not relative.is_absolute() and ".." not in relative.parts
        path = root / relative
        assert path.is_file(), relative
        assert path.stat().st_size == item["bytes"], (relative, "size differs")
        assert digest(path) == item["sha256"], (relative, "hash differs")
    baseline = root / "snapshots/baseline/fastunknot"
    final_fast = root / "snapshots/final/Topology/UnknotRecognition/fast"
    final = final_fast / "fastunknot"
    eager = root / "snapshots/eager/fastunknot"
    current_hashes = package_hashes(final)
    bindings = [
        ("audit-guarded.json", final),
        ("stages-guarded.json", final),
        ("benchmark-guarded.json", final),
        ("audit-eager.json", eager),
    ]
    for record_name, source in bindings:
        data = json.loads((root / "experiments" / record_name).read_text())
        assert data["baseline_commit"] == manifest["baseline_commit"]
        assert data["source_sha256"]["baseline"] == package_hashes(baseline), record_name
        assert data["source_sha256"]["current"] == package_hashes(source), record_name
        assert data["script_sha256"] == digest(root / "experiments/singleton_dag_research.py")
        assert data["corpus_sha256"] == digest(root / "experiments/corpus.json")
        assert data["source_hashes_unchanged"] is True
    ledger = json.loads((root / "experiments/test-suite-ledger.json").read_text())
    assert ledger["source_hashes"] == {"fastunknot/" + k: v for k, v in current_hashes.items()}
    assert ledger["completed"] and ledger["successful"]
    assert ledger["discovered_tests"] == ledger["tests_run"] == 1008
    assert not ledger["failures"] and not ledger["errors"] and not ledger["skipped"]
    overlay = root / "repo_overlay/Topology/UnknotRecognition/fast"
    for path in sorted(overlay.rglob("*")):
        if path.is_file():
            assert path.read_bytes() == (final_fast / path.relative_to(overlay)).read_bytes()
    for line in (root / "CHECKSUMS.sha256").read_text().splitlines():
        expected, relative = line.split("  ", 1)
        assert digest(root / relative) == expected, relative
    print(json.dumps({"valid": True, "manifest_files": len(manifest["files"]),
                      "experiment_source_bindings": len(bindings),
                      "final_python_files": len(current_hashes),
                      "test_suite": "1008 completed; no failures, errors, or skips"}))


if __name__ == "__main__":
    main()

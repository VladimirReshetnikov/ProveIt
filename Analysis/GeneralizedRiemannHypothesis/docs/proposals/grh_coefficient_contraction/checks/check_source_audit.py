#!/usr/bin/env python3
"""Check the source snapshot used by the accompanying mathematical proposal.

Usage:
    python3 check_source_audit.py /path/to/ProveIt --output source_audit_result.json

The manifest defaults to ../audit/source_audit.json relative to this script. The script reads
files and Git metadata only. It checks the pinned commit, SHA-256 digests,
physical line counts, declaration locations, inspected-cluster count, and the
textual interface perimeter in the tracked New sources.
It does not run Lean, validate any proof, or estimate net source-code savings.
Only the Python standard library and a Git executable are required.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys


def declaration_lines(lines: list[str], declaration: str) -> list[int]:
    """Locate a declaration prefix, allowing Lean attributes on the same line."""
    found = []
    for number, line in enumerate(lines, 1):
        stripped = line.lstrip()
        while stripped.startswith("@[") and "]" in stripped:
            stripped = stripped.split("]", 1)[1].lstrip()
        if stripped.startswith("noncomputable "):
            stripped = stripped[len("noncomputable "):]
        if stripped == declaration or (
            stripped.startswith(declaration)
            and stripped[len(declaration):len(declaration) + 1] in " ({[:\t"
        ):
            found.append(number)
    return found


def check(repo: Path, manifest: dict) -> dict:
    failures = []
    result = {
        "audit_kind": "source_snapshot_integrity",
        "proof_validation": False,
        "expected_commit": manifest["commit"],
        "actual_commit": None,
        "checked_files": 0,
        "checked_declaration_anchors": 0,
        "inspected_core_cluster_physical_lines": 0,
        "cluster_count_meaning": manifest["inspected_core_cluster"]["meaning"],
        "files": [],
        "not_checked": [
            "Lean parsing, elaboration, type checking, or kernel checking",
            "Validity of the claimed RH or Dirichlet GRH proof",
            "Compilation of a replacement implementation",
            "Net code deletion or savings after refactoring",
        ],
    }
    try:
        git = subprocess.run(
            ["git", "-C", str(repo), "rev-parse", "HEAD"],
            check=True, capture_output=True, text=True,
        )
        result["actual_commit"] = git.stdout.strip()
        if result["actual_commit"] != manifest["commit"]:
            failures.append("Checkout HEAD does not match the pinned commit.")
    except (OSError, subprocess.CalledProcessError) as exc:
        failures.append(f"Cannot read checkout commit: {exc}")

    actual_counts = {}
    for entry in manifest["files"]:
        path = repo / entry["path"]
        file_result = {"path": entry["path"], "ok": False, "anchors_checked": 0}
        file_failures = []
        try:
            data = path.read_bytes()
            lines = data.decode("utf-8").splitlines()
        except (OSError, UnicodeDecodeError) as exc:
            file_failures.append(f"Cannot read UTF-8 source: {exc}")
        else:
            result["checked_files"] += 1
            digest = hashlib.sha256(data).hexdigest()
            actual_counts[entry["path"]] = len(lines)
            file_result["physical_lines"] = len(lines)
            file_result["sha256"] = digest
            if digest != entry["sha256"]:
                file_failures.append("SHA-256 digest differs.")
            if len(lines) != entry["physical_lines"]:
                file_failures.append("Physical line count differs.")
            for anchor in entry["declaration_anchors"]:
                positions = declaration_lines(lines, anchor["declaration"])
                file_result["anchors_checked"] += 1
                result["checked_declaration_anchors"] += 1
                if positions != [anchor["line"]]:
                    file_failures.append(
                        f"Anchor {anchor['declaration']!r}: "
                        f"expected line {anchor['line']}, found {positions}."
                    )
        file_result["ok"] = not file_failures
        if file_failures:
            file_result["failures"] = file_failures
            failures.extend(f"{entry['path']}: {f}" for f in file_failures)
        result["files"].append(file_result)

    cluster = manifest["inspected_core_cluster"]
    cluster_count = sum(actual_counts.get(path, 0) for path in cluster["paths"])
    result["inspected_core_cluster_physical_lines"] = cluster_count
    if cluster_count != cluster["physical_lines"]:
        failures.append("Inspected core cluster physical-line total differs.")

    scan = manifest["interface_occurrence_scan"]
    pattern = re.compile(r"\b(?:" + "|".join(map(re.escape, scan["identifiers"])) + r")\b")
    scan_result = {
        "directory": scan["directory"],
        "identifiers": scan["identifiers"],
        "meaning": scan["meaning"],
        "tracked_lean_files_scanned": 0,
        "matching_paths": [],
        "matching_files_physical_lines": 0,
    }
    try:
        tracked = subprocess.run(
            ["git", "-C", str(repo), "ls-tree", "-r", "--name-only", "HEAD", "--", scan["directory"]],
            check=True, capture_output=True, text=True,
        )
        paths = sorted(p for p in tracked.stdout.splitlines() if p.endswith(".lean"))
        for relative in paths:
            content = (repo / relative).read_text(encoding="utf-8")
            scan_result["tracked_lean_files_scanned"] += 1
            if pattern.search(content):
                scan_result["matching_paths"].append(relative)
                scan_result["matching_files_physical_lines"] += len(content.splitlines())
    except (OSError, UnicodeDecodeError, subprocess.CalledProcessError) as exc:
        failures.append(f"Cannot complete interface occurrence scan: {exc}")
    for key in ("tracked_lean_files_scanned", "matching_paths", "matching_files_physical_lines"):
        if scan_result[key] != scan[key]:
            failures.append(f"Interface occurrence scan differs for {key}.")
    result["interface_occurrence_scan"] = scan_result
    result["ok"] = not failures
    result["failures"] = failures
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("repo", type=Path, help="Local ProveIt checkout root")
    parser.add_argument(
        "--manifest", type=Path,
        default=Path(__file__).resolve().parent.parent / "audit" / "source_audit.json",
    )
    parser.add_argument("--output", type=Path, help="Optional output JSON path")
    args = parser.parse_args()
    manifest = json.loads(args.manifest.read_text(encoding="utf-8"))
    result = check(args.repo.resolve(), manifest)
    rendered = json.dumps(result, ensure_ascii=False, indent=2) + "\n"
    if args.output:
        args.output.write_text(rendered, encoding="utf-8")
    print(rendered, end="")
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    sys.exit(main())

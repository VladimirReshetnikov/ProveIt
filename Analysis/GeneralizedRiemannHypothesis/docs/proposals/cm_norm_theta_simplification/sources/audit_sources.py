#!/usr/bin/env python3
"""Verify pinned source bytes and declaration locations without network access.

Usage:
    python3 audit_sources.py /path/to/ProveIt --output audit_result.json

The neighboring revision.json and TSV inventories supply all expected values.
Only Python's standard library is required. If Git and a .git entry are present,
the commit and recorded tree metadata are additionally checked. Git subprocesses
disable lazy fetching and all transport protocols; this program never fetches.
This verifies source identity and anchors, not Lean elaboration or mathematics.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import shutil
import stat
import subprocess
import sys


def git_object_sha1(kind: bytes, data: bytes) -> str:
    return hashlib.sha1(kind + b" " + str(len(data)).encode("ascii") + b"\0" + data).hexdigest()


def blob_sha1(data: bytes) -> str:
    return git_object_sha1(b"blob", data)


def read_tsv(path: Path) -> list[dict[str, str]]:
    with path.open(encoding="utf-8", newline="") as stream:
        return list(csv.DictReader(stream, delimiter="\t"))


def safe_source(root: Path, relative: str) -> Path:
    path = PurePosixPath(relative)
    if path.is_absolute() or ".." in path.parts:
        raise ValueError(f"Unsafe relative source path: {relative}")
    result = root.joinpath(*path.parts)
    if not result.resolve().is_relative_to(root):
        raise ValueError(f"Source path escapes supplied checkout: {relative}")
    return result


def tree_sha1(directory: Path) -> str:
    """Recompute a Git tree from local bytes, names, and regular-file modes.

    Symlink targets are hashed as strings, never followed. For a checkout with
    changed file modes or extra files the resulting tree intentionally differs.
    Git's ordering treats a directory name as if followed by a slash.
    """
    entries = []
    for path in directory.iterdir():
        name = os.fsencode(path.name)
        if path.is_symlink():
            mode = b"120000"
            digest = blob_sha1(os.fsencode(os.readlink(path)))
            key = name
        elif path.is_dir():
            mode = b"40000"
            digest = tree_sha1(path)
            key = name + b"/"
        elif path.is_file():
            mode = b"100755" if path.stat().st_mode & stat.S_IXUSR else b"100644"
            digest = blob_sha1(path.read_bytes())
            key = name
        else:
            raise ValueError(f"Unexpected non-regular filesystem entry: {path.name}")
        entries.append((key, mode + b" " + name + b"\0" + bytes.fromhex(digest)))
    return git_object_sha1(b"tree", b"".join(entry for _, entry in sorted(entries)))


def offline_git(root: Path, *arguments: str) -> str:
    environment = os.environ.copy()
    environment["GIT_NO_LAZY_FETCH"] = "1"
    environment["GIT_TERMINAL_PROMPT"] = "0"
    environment["GIT_ALLOW_PROTOCOL"] = ""
    completed = subprocess.run(
        ["git", "-c", "protocol.allow=never", "-C", str(root), *arguments],
        env=environment, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        text=True, timeout=30,
    )
    return completed.stdout.strip()


def audit(root: Path, support: Path) -> dict:
    revision = json.loads((support / "revision.json").read_text(encoding="utf-8"))
    inventory = read_tsv(support / "proposal_inventory.tsv")
    anchors = read_tsv(support / "source_anchors.tsv")
    root = root.resolve()
    errors: list[str] = []
    warnings: list[str] = []
    verified_blobs: dict[str, str] = {}
    text_cache: dict[str, list[str]] = {}

    def check(condition: bool, message: str) -> None:
        if not condition:
            errors.append(message)

    def inspect(path: str, expected_sha: str) -> list[str] | None:
        if path in verified_blobs:
            check(verified_blobs[path] == expected_sha, f"Inconsistent expected hash for {path}")
            return text_cache.get(path)
        try:
            raw = safe_source(root, path).read_bytes()
            actual_sha = blob_sha1(raw)
            verified_blobs[path] = actual_sha
            check(actual_sha == expected_sha, f"Blob mismatch for {path}: {actual_sha}")
            lines = raw.decode("utf-8").splitlines()
            text_cache[path] = lines
            return lines
        except (OSError, UnicodeError, ValueError) as exc:
            errors.append(f"Cannot inspect {path}: {exc}")
            return None

    expected_commit = revision["commit"]
    base_url = revision["repository_url"] + "/blob/" + expected_commit + "/"
    for row in inventory:
        inspect(row["path"], row["git_blob_sha1"])
        check(row["pinned_url"] == base_url + row["path"], f"Unexpected inventory URL: {row['path']}")
    for row in anchors:
        lines = inspect(row["path"], row["git_blob_sha1"])
        line = int(row["line"])
        if lines is not None:
            if not 1 <= line <= len(lines):
                errors.append(f"Anchor line outside file: {row['path']}:{line}")
            else:
                check(lines[line - 1].startswith(row["declaration_prefix"]),
                      f"Declaration prefix mismatch: {row['path']}:{line}")
                check(lines[line - 1] == row["line_text"],
                      f"Exact declaration line mismatch: {row['path']}:{line}")
        check(row["pinned_url"] == base_url + row["path"] + "#L" + str(line),
              f"Unexpected anchor URL: {row['path']}:{line}")

    try:
        proposals_root = safe_source(root, revision["trees"]["proposals"]["path"])
        expected_documents = {
            path.relative_to(root).as_posix() for path in proposals_root.rglob("*")
            if path.is_file() and (path.suffix == ".tex" or path.name in
                                   {"README.md", "FORMALIZATION.md", "LEAN_PLAN.md"})
        }
        recorded_documents = {row["path"] for row in inventory}
        check(recorded_documents == expected_documents, "Proposal inventory does not cover the complete requested text set.")
        check(len(recorded_documents) == len(inventory), "Duplicate proposal inventory paths.")
        counts = {category: sum(row["category"] == category for row in inventory)
                  for category in ("tex", "readme", "integration_plan")}
        check(counts == revision["audited_proposal_documents"], "Proposal category counts differ from revision.json.")
    except (OSError, ValueError) as exc:
        errors.append(f"Cannot enumerate proposal documents: {exc}")
        counts = {}

    tree_results = {}
    for label in ("lean_src", "proposals"):
        item = revision["trees"][label]
        try:
            actual = tree_sha1(safe_source(root, item["path"]))
            tree_results[label] = actual
            check(actual == item["git_tree_sha1"], f"Local content tree differs for {label}: {actual}")
        except (OSError, ValueError) as exc:
            errors.append(f"Cannot compute {label} content tree: {exc}")

    stats = {}
    try:
        lean_root = safe_source(root, revision["trees"]["lean_src"]["path"])
        lean_files = sorted(lean_root.rglob("*.lean"))
        raw_files = [path.read_bytes() for path in lean_files]
        stats = {"files": len(lean_files), "lf_lines": sum(raw.count(b"\n") for raw in raw_files),
                 "logical_lines": sum(len(raw.splitlines()) for raw in raw_files),
                 "files_without_final_lf": sum(not raw.endswith(b"\n") for raw in raw_files)}
        check(stats == revision["lean_source_statistics"], "Lean source file/line statistics differ.")
    except OSError as exc:
        errors.append(f"Cannot count Lean sources: {exc}")

    for item in revision["version_files"]:
        inspect(item["path"], item["git_blob_sha1"])
    try:
        toolchain = safe_source(root, revision["lean_toolchain_file"]).read_text(encoding="utf-8").strip()
        check(toolchain == revision["lean_toolchain"], "Lean toolchain does not match.")
        manifest = json.loads(safe_source(root, revision["lake_manifest_file"]).read_text(encoding="utf-8"))
        mathlib = [package for package in manifest["packages"] if package["name"] == "mathlib"]
        check(len(mathlib) == 1 and mathlib[0]["rev"] == revision["mathlib_revision"],
              "Mathlib revision does not match.")
    except (OSError, KeyError, ValueError) as exc:
        errors.append(f"Cannot verify dependency versions: {exc}")

    git_metadata = {"checked": False}
    if (root / ".git").exists() and shutil.which("git"):
        try:
            head = offline_git(root, "rev-parse", "HEAD")
            root_tree = offline_git(root, "rev-parse", "HEAD^{tree}")
            git_metadata = {"checked": True, "head": head, "root_tree": root_tree, "trees": {}}
            check(head == expected_commit, f"Checkout HEAD is {head}, expected {expected_commit}.")
            check(root_tree == revision["root_tree"], "Recorded root tree differs.")
            for label, item in revision["trees"].items():
                actual = offline_git(root, "rev-parse", "HEAD:" + item["path"])
                git_metadata["trees"][label] = actual
                check(actual == item["git_tree_sha1"], f"Git tree metadata differs for {label}.")
        except (OSError, subprocess.SubprocessError) as exc:
            errors.append(f"Offline Git metadata check failed: {exc}")
    else:
        warnings.append("Git metadata not checked: .git or Git executable unavailable; local content checks still ran.")

    check(len(anchors) == revision["source_anchor_statistics"]["declarations"], "Anchor count differs.")
    unique_anchors = len({row["path"] for row in anchors})
    check(unique_anchors == revision["source_anchor_statistics"]["files"], "Anchor file count differs.")
    return {"status": "PASS" if not errors else "FAIL", "pinned_commit": expected_commit,
            "proposal_documents": counts, "proposal_files_checked": len(inventory),
            "source_declarations_checked": len(anchors), "source_anchor_files_checked": unique_anchors,
            "total_unique_text_blobs_checked": len(verified_blobs), "content_tree_checks": tree_results,
            "lean_source_statistics": stats, "git_metadata": git_metadata,
            "scope": "Source bytes, versions, inventory coverage, and declaration locations only; no Lean build or kernel replay.",
            "warnings": warnings, "errors": errors}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout", type=Path, help="Root of the supplied ProveIt checkout or source export.")
    parser.add_argument("--output", type=Path, help="Optional JSON output path; no source files are modified.")
    arguments = parser.parse_args()
    result = audit(arguments.checkout, Path(__file__).resolve().parent)
    if arguments.output:
        arguments.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(f"{result['status']}: pinned source identity audit")
    print(f"Commit: {result['pinned_commit']}")
    print(f"Proposal text files: {result['proposal_files_checked']} (12 TeX, 5 READMEs, 2 integration plans)")
    print(f"Source anchors: {result['source_declarations_checked']} declarations in {result['source_anchor_files_checked']} files")
    stats = result["lean_source_statistics"]
    print(f"Lean src: {stats.get('files', '?')} files, {stats.get('lf_lines', '?')} LF lines")
    print("Scope: source identity and locations; no Lean elaboration or kernel replay.")
    for warning in result["warnings"]:
        print("WARNING:", warning)
    for error in result["errors"]:
        print("ERROR:", error)
    return 0 if result["status"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())

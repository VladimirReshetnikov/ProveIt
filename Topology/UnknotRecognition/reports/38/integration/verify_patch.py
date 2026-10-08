"""Verify provenance, apply the patch to a temporary copy, and compare bytes.

The supplied repository is read only. Only the selected source subset is
copied; missing reference modules are read from their pinned snapshot copies.
Requires Python 3.10+ and git. Does not run tests or contact a remote service.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tempfile


PACKAGE = Path(__file__).resolve().parents[1]


def blob_sha(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def file_map(root: Path) -> dict[str, Path]:
    return {p.relative_to(root).as_posix(): p for p in root.rglob("*")
            if p.is_file() and "__pycache__" not in p.parts
            and p.suffix not in {".pyc", ".pyo"}}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, required=True,
                        help="checkout containing the pinned baseline fast source")
    parser.add_argument("--output", type=Path, help="optional JSON verification record")
    args = parser.parse_args()
    repo = args.repo_root.resolve()
    pinned = json.loads((PACKAGE / "provenance/selected-pinned-source-validation.json").read_text())
    changes = json.loads((PACKAGE / "integration/changed-files.json").read_text())
    patch = PACKAGE / "integration/unknot_research.patch"
    patch_digest = hashlib.sha256(patch.read_bytes()).hexdigest()
    assert patch_digest == changes["patch_sha256"], "Patch digest mismatch"
    fast_verified = reference_verified = fallback_references = 0
    bytes_verified = 0
    with tempfile.TemporaryDirectory(prefix="unknot-patch-verify-") as temporary:
        checkout = Path(temporary)
        for row in pinned["files"]:
            source = repo / row["path"]
            reference = row["source"] == "unchanged-test-reference"
            if reference and not source.is_file():
                source = PACKAGE / "snapshot" / row["path"]
                fallback_references += 1
            data = source.read_bytes()
            assert len(data) == row["bytes"], f"Pinned byte length mismatch: {row['path']}"
            assert blob_sha(data) == row["expected_git_blob_sha1"], f"Pinned Git blob mismatch: {row['path']}"
            assert hashlib.sha256(data).hexdigest() == row["sha256"], f"Pinned SHA-256 mismatch: {row['path']}"
            destination = checkout / row["path"]
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source, destination)
            if reference:
                reference_verified += 1
            else:
                fast_verified += 1
        git = ["git", "-c", "core.autocrlf=false", "-c", "core.safecrlf=false",
               "-c", "core.attributesFile=/dev/null"]
        checked = subprocess.run(git + ["apply", "--check", "--whitespace=nowarn", str(patch)],
                                 cwd=checkout, check=True, capture_output=True, text=True)
        applied = subprocess.run(git + ["apply", "--whitespace=nowarn", str(patch)],
                                 cwd=checkout, check=True, capture_output=True, text=True)
        actual = file_map(checkout)
        expected = file_map(PACKAGE / "snapshot")
        assert set(actual) == set(expected), "Patched snapshot path set differs"
        for name, source in expected.items():
            data = source.read_bytes()
            assert actual[name].read_bytes() == data, f"Patched bytes differ: {name}"
            bytes_verified += len(data)
        tree = file_map(PACKAGE / "integration/tree")
        assert set(tree) == set(changes["new_files"] + changes["modified_files"]), "Integration tree path set differs"
        for row in changes["files"]:
            data = tree[row["path"]].read_bytes()
            assert data == expected[row["path"]].read_bytes(), f"Integration tree bytes differ: {row['path']}"
            assert len(data) == row["bytes"]
            assert hashlib.sha256(data).hexdigest() == row["sha256"]
        report = dict(
            result="PASS", base_commit=pinned["base_commit"], baseline_input=str(repo),
            verification="temporary clean baseline copy; input repository unchanged",
            selected_pinned_files=fast_verified + reference_verified,
            pinned_fast_files=fast_verified, pinned_reference_files=reference_verified,
            references_from_packaged_snapshot=fallback_references,
            patch_check_returncode=checked.returncode, patch_apply_returncode=applied.returncode,
            whitespace_policy="nowarn; preserve exact authored bytes", patch_sha256=patch_digest,
            target_files_compared=len(expected), target_bytes_compared=bytes_verified,
            target_path_sets_identical=True, target_bytes_identical=True,
            integration_tree_files_compared=len(tree), new_files=len(changes["new_files"]),
            modified_files=len(changes["modified_files"]), deleted_files=len(changes["deleted_files"]),
            tests_rerun=False)
    output = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(output)
    print(output, end="")


if __name__ == "__main__":
    main()

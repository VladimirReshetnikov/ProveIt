#!/usr/bin/env python3
"""Check the delivered source patch and hashes without changing a checkout."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tempfile


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, help="Optional baseline checkout to verify read-only")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    manifest = json.loads((root / "provenance.json").read_text())
    count = 0
    for line in (root / "SHA256SUMS").read_text().splitlines():
        expected, relative = line.split("  ", 1)
        path = root / relative
        assert path.is_file(), f"Missing artifact: {relative}"
        assert sha256(path) == expected, f"Artifact checksum mismatch: {relative}"
        count += 1

    before = after = 0
    for entry in manifest["files"]:
        relative = Path(entry["repository_path"])
        old = root / "baseline" / relative
        new = root / "replacements" / relative
        assert sha256(old) == entry["baseline_sha256"], relative
        assert sha256(new) == entry["candidate_sha256"], relative
        old_lines = len(old.read_text().splitlines())
        new_lines = len(new.read_text().splitlines())
        assert old_lines == entry["baseline_lines"]
        assert new_lines == entry["candidate_lines"]
        before += old_lines
        after += new_lines
        if args.repo is not None:
            checkout_file = args.repo.resolve() / relative
            assert checkout_file.is_file(), f"Missing checkout file: {relative}"
            assert sha256(checkout_file) == entry["baseline_sha256"], (
                f"Checkout differs from the pinned baseline: {relative}"
            )

    assert (before, after, before - after) == (1401, 1307, 94)
    with tempfile.TemporaryDirectory(prefix="proveit-proof-proposal-") as work:
        work_path = Path(work)
        shutil.copytree(root / "baseline", work_path, dirs_exist_ok=True)
        patch = str(root / "patches" / "proposed.patch")
        subprocess.run(["git", "apply", "--check", patch], cwd=work_path, check=True)
        subprocess.run(["git", "apply", patch], cwd=work_path, check=True)
        for entry in manifest["files"]:
            relative = Path(entry["repository_path"])
            assert (work_path / relative).read_bytes() == (
                root / "replacements" / relative
            ).read_bytes(), f"Patch differs from replacement: {relative}"
    print(json.dumps({
        "artifact_checksums_verified": count,
        "source_files_verified": len(manifest["files"]),
        "combined_patch_applies_and_matches_replacements": True,
        "baseline_lines": before,
        "candidate_lines": after,
        "net_physical_lines_removed": before - after,
        "lean_recompiled_by_this_script": False,
    }, indent=2))


if __name__ == "__main__":
    main()

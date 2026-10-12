#!/usr/bin/env python3
"""Rebuild the pinned patch, full-file overlay, and per-source manifest."""
import argparse
import difflib
import hashlib
import json
from pathlib import Path
import subprocess

BASE = "8cb7d9d25ac8cb64a9d147304e3441e98e94c7a4"
PREFIX = "Topology/UnknotRecognition/fast/"
FILES = (
    "fastunknot/normal_cut_handlebodies.py",
    "fastunknot/normal_cut_handlebodies_verify.py",
    "fastunknot/core_top_reduction.py",
    "fastunknot/core_top_reduction_verify.py",
    "fastunknot/core_top_template.py",
    "fastunknot/core_forest_exchange.py",
    "fastunknot/core_forest_exchange_verify.py",
    "tests/test_core_top_reduction.py",
    "tests/test_core_top_template.py",
    "tests/test_core_forest_exchange.py",
    "core_top_research/audit.py",
    "core_top_research/benchmark.py",
    "core_top_research/template_audit.py",
    "core_top_research/forest_audit.py",
    "core_top_research/chain_audit.py",
    "core_top_research/residual_kernel.py",
    "core_top_research/residual_kernel_audit.py",
)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--package", type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    repo = args.repo.resolve(strict=True)
    head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=repo, text=True).strip()
    if head != BASE:
        raise RuntimeError(f"Expected pinned HEAD {BASE}, got {head}")
    destination = args.package.resolve() / "integration"
    destination.mkdir(parents=True, exist_ok=True)
    chunks, records = [], []
    for relative in FILES:
        path = PREFIX + relative
        current = (repo / path).read_bytes()
        original = subprocess.run(["git", "show", BASE + ":" + path], cwd=repo,
                                  capture_output=True, check=False)
        old = original.stdout if original.returncode == 0 else b""
        is_new = original.returncode != 0
        if old == current:
            raise RuntimeError(f"Unexpected unchanged release file: {path}")
        target = destination / "overlay" / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(current)
        header = f"diff --git a/{path} b/{path}\n"
        if is_new:
            header += "new file mode 100644\n"
        delta = "".join(difflib.unified_diff(
            old.decode("utf-8").splitlines(keepends=True),
            current.decode("utf-8").splitlines(keepends=True),
            fromfile="/dev/null" if is_new else "a/" + path,
            tofile="b/" + path,
        ))
        chunks.append(header + delta)
        records.append({"path": path, "status": "new" if is_new else "modified",
                        "bytes": len(current), "sha256": sha(current),
                        "baseline_sha256": None if is_new else sha(old)})
    patch = "".join(chunks).encode("utf-8")
    (destination / "proveit-relative-top-handles.patch").write_bytes(patch)
    manifest = {"base_commit": BASE, "repository": "https://github.com/VladimirReshetnikov/ProveIt",
                "patch_sha256": sha(patch), "files": records}
    (destination / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(json.dumps({"base_commit": BASE, "files": len(records),
                      "modified": sum(r["status"] == "modified" for r in records),
                      "patch_bytes": len(patch), "patch_sha256": sha(patch)}, indent=2))


if __name__ == "__main__":
    main()

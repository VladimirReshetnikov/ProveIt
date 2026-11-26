#!/usr/bin/env python3
"""Compare a checkout and downloaded evidence with published MIT SHA-256 lists.

This checks content identity, not theorem correctness. No network is used.
Usage: python3 verify_published_hashes.py REPOSITORY LOG_DIRECTORY --out REPORT.json
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

ARCHIVE_SHA256 = "9138cf2f5862e64f823ed676e8d37333c0717e1a13cd8f74f6b735ab2d1ba57c"


def compare_manifest(base, manifest, ignore_missing=False):
    checks = []
    for line in manifest.read_text().splitlines():
        expected, name = line.split(None, 1)
        name = name.strip().lstrip("*")
        path = base / name
        if not path.is_file() and ignore_missing:
            continue
        actual = hashlib.sha256(path.read_bytes()).hexdigest() if path.is_file() else None
        checks.append({"path": name, "expected": expected, "actual": actual, "match": expected == actual})
    return checks


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("repository", type=Path)
    parser.add_argument("logs", type=Path)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    sources = compare_manifest(args.repository, args.logs / "source-files.sha256")
    logs = compare_manifest(args.logs, args.logs / "SHA256SUMS", ignore_missing=True)
    tracked = set(subprocess.check_output(["git", "-C", str(args.repository), "ls-files"], text=True).splitlines())
    listed = {s["path"] for s in sources}
    proc = subprocess.Popen(["git", "-C", str(args.repository), "archive", "--format=tar", "HEAD"], stdout=subprocess.PIPE)
    archive_hash = hashlib.sha256()
    while block := proc.stdout.read(1 << 20):
        archive_hash.update(block)
    if proc.wait() != 0:
        raise RuntimeError("git archive failed")
    report = {
        "source_manifest_url": "https://math.mit.edu/~drew/shortgrh/source-files.sha256",
        "listed_source_files": len(sources),
        "source_hash_matches": sum(x["match"] for x in sources),
        "source_mismatches": [x for x in sources if not x["match"]],
        "tracked_files_missing_from_external_manifest": sorted(tracked - listed),
        "listed_files_not_tracked": sorted(listed - tracked),
        "downloaded_logs_checked_against_publisher_sha256s": len(logs),
        "downloaded_logs_hash_matches": sum(x["match"] for x in logs),
        "downloaded_logs_hash_mismatches": [x for x in logs if not x["match"]],
        "git_archive_sha256": archive_hash.hexdigest(),
        "published_archive_sha256": ARCHIVE_SHA256,
        "archive_matches": archive_hash.hexdigest() == ARCHIVE_SHA256,
        "scope_note": "Content matching against third-party published manifests, not independent proof replay. Publisher hashes and logs share one provenance.",
    }
    args.out.write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()

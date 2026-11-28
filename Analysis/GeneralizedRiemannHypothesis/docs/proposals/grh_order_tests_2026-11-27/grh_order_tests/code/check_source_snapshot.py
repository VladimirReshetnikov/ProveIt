#!/usr/bin/env python3
"""Verify the pinned inputs to the report; never modifies the source checkout."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess


def blob_id(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    source = json.loads((root / "audit/source_manifest.json").read_text())
    proposals = json.loads((root / "audit/existing_proposals_manifest.json").read_text())
    checkout = args.checkout.resolve()
    head = subprocess.check_output(["git", "-C", str(checkout), "rev-parse", "HEAD"], text=True).strip()
    assert head == source["commit"] == proposals["commit"], ("Unexpected revision", head)

    anchors = 0
    for record in source["files"]:
        path = checkout / record["path"]
        data = path.read_bytes()
        assert len(data) == record["size_bytes"], ("Size mismatch", path)
        assert blob_id(data) == record["git_blob_sha1"], ("Git blob mismatch", path)
        assert hashlib.sha256(data).hexdigest() == record["sha256"], ("SHA-256 mismatch", path)
        lines = data.decode().splitlines()
        for anchor in record["anchors"]:
            assert lines[anchor["line"] - 1] == anchor["source_line"], ("Anchor mismatch", path, anchor)
            anchors += 1

    for record in proposals["files"]:
        path = checkout / record["path"]
        data = path.read_bytes()
        assert len(data) == record["size_bytes"], ("Proposal size mismatch", path)
        assert blob_id(data) == record["git_blob_sha1"], ("Proposal Git blob mismatch", path)

    result = {
        "status": "PASS",
        "commit": head,
        "source_files": len(source["files"]),
        "declaration_anchors": anchors,
        "proposal_files": len(proposals["files"]),
        "proposal_text_files": proposals["text_file_count"],
        "scope": "Source identity and anchor verification only; no Lean compilation or kernel replay.",
    }
    rendered = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(rendered)
    print(rendered, end="")


if __name__ == "__main__":
    main()

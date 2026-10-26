#!/usr/bin/env python3
"""Authenticate selected inherited evidence, without invoking a proof assistant."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    directory = ROOT / "calibration/evidence"
    pins = json.loads((directory / "SOURCE_PINS.json").read_text())
    commit = "cdfea7d90176775d74c1c30afbe49fa78ade9897"
    require(pins["commit"] == commit, "Calibration snapshot differs")
    for item in pins["files"]:
        payload = (directory / item["local"]).read_bytes()
        blob = b"blob " + str(len(payload)).encode("ascii") + b"\0" + payload
        require(hashlib.sha1(blob).hexdigest() == item["git_blob_sha"],
                "Retained calibration file differs: " + item["local"])
        require("/blob/" + commit + "/" in item["source_url"],
                "Calibration URL is not pinned")
    ledger = json.loads((ROOT / "calibration/DIRECT_SOURCE_LEDGER.json").read_text())
    require(ledger["commit"] == commit, "Direct source ledger snapshot differs")
    print(json.dumps({
        "status": "PASS",
        "retained_git_blobs_authenticated": len(pins["files"]),
        "direct_source_audit_module_records": len(ledger["modules"]),
        "scope": "Authenticates retained proof text and archived logs. "
                 "Does not rebuild kernels or repeat the remote transitive source audit.",
    }, indent=2))


if __name__ == "__main__":
    main()

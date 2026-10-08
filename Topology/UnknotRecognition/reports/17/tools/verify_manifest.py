"""Check archive content hashes and the pinned source provenance."""
import hashlib
import json
from pathlib import Path


def main():
    root = Path(__file__).resolve().parents[1]
    count = 0
    for line in (root / "SHA256SUMS").read_text().splitlines():
        digest, name = line.split("  ", 1)
        path = (root / name).resolve()
        if not path.is_relative_to(root) or not path.is_file():
            raise SystemExit("Missing or unsafe manifest path: " + name)
        if hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            raise SystemExit("SHA-256 mismatch: " + name)
        count += 1
    provenance = json.loads((root / "integration/source_provenance.json").read_text())
    for item in provenance["files"]:
        data = (root / "reference" / item["path"]).read_bytes()
        blob = b"blob " + str(len(data)).encode("ascii") + b"\0" + data
        if hashlib.sha1(blob).hexdigest() != item["git_blob_sha1"]:
            raise SystemExit("Git object mismatch: " + item["path"])
    print(json.dumps({"status": "PASS", "sha256_files": count,
                      "git_blobs": len(provenance["files"]),
                      "baseline_commit": provenance["commit"]}, indent=2))


if __name__ == "__main__":
    main()

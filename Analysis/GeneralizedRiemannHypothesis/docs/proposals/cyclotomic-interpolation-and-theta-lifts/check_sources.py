"""Check pinned Git blobs against a checkout of the upstream grh-lean repository."""
import argparse
from hashlib import sha1
from pathlib import Path
import json

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout", type=Path, help="directory containing grh and grh-compact")
    args = parser.parse_args()
    manifest = json.loads(Path(__file__).with_name("sources.json").read_text())
    for entry in manifest["files"]:
        path = args.checkout / entry["path"]
        data = path.read_bytes()
        digest = sha1(b"blob " + str(len(data)).encode("ascii") + b"\0" + data).hexdigest()
        if digest != entry["git_blob"]:
            raise SystemExit(f"Blob mismatch in {entry['path']}: read {digest}")
    print(f"Matched {len(manifest['files'])} Git blobs at {manifest['upstream_revision']}.")

if __name__ == "__main__":
    main()

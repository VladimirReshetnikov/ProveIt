"""Match the inspected GitHub blob identities to a local upstream checkout."""
import argparse
import hashlib
import json
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout", type=Path)
    args = parser.parse_args()
    record = json.loads(Path(__file__).with_name("upstream_blobs.json").read_text())
    for path, expected in record["files"].items():
        data = (args.checkout / path).read_bytes()
        actual = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        if actual != expected:
            raise ValueError(f"Git blob mismatch for {path}")
    print(f"All {len(record['files'])} inspected sources match revision {record['commit']}.")


if __name__ == "__main__":
    main()

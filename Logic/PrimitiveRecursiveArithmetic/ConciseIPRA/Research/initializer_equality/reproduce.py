"""Offline reproduction of the delivered checks and measurements."""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def run(relative):
    proc = subprocess.run([sys.executable, str(ROOT / relative)],
                          cwd=ROOT, text=True, capture_output=True)
    if proc.returncode:
        print(proc.stdout)
        print(proc.stderr, file=sys.stderr)
        raise SystemExit(proc.returncode)
    print("Verified", relative)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--skip-manifest", action="store_true")
    args = parser.parse_args()
    manifest = ROOT / "SHA256SUMS"
    if manifest.exists() and not args.skip_manifest:
        for line in manifest.read_text().splitlines():
            digest, name = line.split("  ", 1)
            if hashlib.sha256((ROOT / name).read_bytes()).hexdigest() != digest:
                raise SystemExit("Checksum mismatch: " + name)
        print("Verified delivered checksum manifest")
    run("shared_traversal/build_shared.py")
    run("shared_traversal/verify_shared.py")
    run("code/build.py")
    run("code/test_seed.py")
    proc = subprocess.run([sys.executable, str(ROOT / "build.py"), "--tex-only"],
                          cwd=ROOT, text=True, capture_output=True)
    if proc.returncode:
        raise SystemExit(proc.stdout + proc.stderr)
    summary = json.loads((ROOT / "evidence/summary.json").read_text())
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()

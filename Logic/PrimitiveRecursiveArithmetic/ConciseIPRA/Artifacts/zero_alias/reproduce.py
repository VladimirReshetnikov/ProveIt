"""Verify delivered files, regenerate certificates, and replay the evidence."""
from pathlib import Path
import argparse
import hashlib
import subprocess
import sys

ROOT = Path(__file__).resolve().parent

def verify_manifest():
    manifest = ROOT / "MANIFEST.sha256"
    if not manifest.exists():
        raise RuntimeError("Delivery manifest is missing")
    count = 0
    for line in manifest.read_text().splitlines():
        expected, relative = line.split("  ", 1)
        path = ROOT / relative
        if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            raise RuntimeError("Manifest mismatch: " + relative)
        count += 1
    print(f"Verified {count} delivered file hashes", flush=True)

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--pdf", action="store_true",
                        help="also rebuild both PDF documents")
    args = parser.parse_args()
    verify_manifest()
    subprocess.run([sys.executable, str(ROOT / "verify_incoming.py")], cwd=ROOT, check=True)
    subprocess.run([sys.executable, str(ROOT / "implementation/compile_alias.py")],
                   cwd=ROOT, check=True)
    subprocess.run([sys.executable, str(ROOT / "implementation/verify_alias.py")],
                   cwd=ROOT, check=True)
    if args.pdf:
        subprocess.run([sys.executable, str(ROOT / "build.py")],
                       cwd=ROOT, check=True)

if __name__ == "__main__":
    main()


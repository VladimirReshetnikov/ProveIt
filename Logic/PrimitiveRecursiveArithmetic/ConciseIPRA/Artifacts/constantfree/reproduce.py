"""Reproduce the mathematical certificates and complete-module measurements."""

from pathlib import Path
import argparse
import hashlib
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
REFERENCES = {
    "reference/checker_register_graph.py": "453f591238a5281cb213930581735b2b2afaa443",
    "reference/register_graph.tex": "e5e2dcc949cacb8ddcbdea2ad35726049b4b38e0",
}


def verify_references():
    for filename, expected in REFERENCES.items():
        data = (ROOT / filename).read_bytes()
        observed = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        if observed != expected:
            raise RuntimeError("Pinned Git blob mismatch: " + filename)
    print("Pinned reference blobs verified.", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pdf", action="store_true", help="also rebuild the PDF")
    args = parser.parse_args()
    verify_references()
    for script in ("code/make_certificates.py", "code/verify_certificates.py", "compact/verify.py"):
        subprocess.run([sys.executable, str(ROOT / script)], cwd=ROOT, check=True)
    if args.pdf:
        subprocess.run([sys.executable, str(ROOT / "build_pdf.py")], cwd=ROOT, check=True)
    print("Reproduction completed successfully.")


if __name__ == "__main__":
    main()

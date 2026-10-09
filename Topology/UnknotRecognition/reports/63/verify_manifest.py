"""Verify delivered SHA-256 checksums. Run before changing generated artifacts."""
from pathlib import Path
import hashlib
import sys


def main() -> int:
    root = Path(__file__).resolve().parent
    manifest = root / "MANIFEST.sha256"
    if not manifest.is_file():
        print("Missing MANIFEST.sha256", file=sys.stderr)
        return 2
    failures = []
    count = 0
    for line in manifest.read_text(encoding="utf-8").splitlines():
        digest, sep, name = line.partition("  ")
        candidate = (root / name).resolve()
        if not sep or len(digest) != 64 or root not in candidate.parents:
            failures.append(f"Invalid manifest entry: {line!r}")
            continue
        count += 1
        if not candidate.is_file():
            failures.append(f"Missing: {name}")
        elif hashlib.sha256(candidate.read_bytes()).hexdigest() != digest:
            failures.append(f"Changed: {name}")
    for failure in failures:
        print(failure, file=sys.stderr)
    print(f"Checked {count} files; {len(failures)} mismatches.")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())

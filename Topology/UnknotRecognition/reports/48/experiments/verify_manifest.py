"""Verify the delivered package against SHA256SUMS; no network access."""
from hashlib import sha256
from pathlib import Path
import sys


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    manifest = root / "SHA256SUMS"
    failures, checked = [], 0
    for line in manifest.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        digest, relative = line.split("  ", 1)
        path = (root / relative).resolve()
        if not path.is_relative_to(root) or not path.is_file():
            failures.append(relative + ": missing or outside package")
            continue
        if sha256(path.read_bytes()).hexdigest() != digest:
            failures.append(relative + ": checksum mismatch")
        checked += 1
    for failure in failures:
        print(failure, file=sys.stderr)
    print(f"Checked {checked} files; {len(failures)} failures.")
    return int(bool(failures))


if __name__ == "__main__":
    raise SystemExit(main())

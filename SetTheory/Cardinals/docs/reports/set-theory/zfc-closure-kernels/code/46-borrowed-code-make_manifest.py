#!/usr/bin/env python3
"""Regenerate hashes after intentional changes to this research package."""
import hashlib
from pathlib import Path

root = Path(__file__).resolve().parents[1]
excluded = {".aux", ".log", ".out", ".toc", ".fls", ".fdb_latexmk", ".synctex.gz", ".pyc"}
lines = []
for path in sorted(root.rglob("*")):
    if not path.is_file() or path.name == "SHA256SUMS":
        continue
    if "__pycache__" in path.parts or path.suffix in excluded or path.name.endswith(".synctex.gz"):
        continue
    relative = path.relative_to(root).as_posix()
    lines.append(hashlib.sha256(path.read_bytes()).hexdigest() + "  " + relative)
(root / "SHA256SUMS").write_text("\n".join(lines) + "\n", encoding="utf-8")
print(f"Wrote SHA256SUMS for {len(lines)} files")

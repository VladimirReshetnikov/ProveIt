"""Regenerate SHA256SUMS after an intentional package modification."""
import hashlib
from pathlib import Path

root = Path(__file__).resolve().parents[1]
excluded_suffixes = {".aux", ".log", ".toc", ".out", ".bbl", ".blg", ".fls", ".fdb_latexmk"}
rows = []
for path in sorted(root.rglob("*")):
    if not path.is_file() or path.name == "SHA256SUMS":
        continue
    relative = path.relative_to(root)
    if "__pycache__" in relative.parts or "reproduction_runs" in relative.parts:
        continue
    if path.suffix == ".pyc":
        continue
    # Preserve research and benchmark logs; exclude only LaTeX build debris.
    if relative.parts[0] == "paper" and path.suffix in excluded_suffixes:
        continue
    rows.append(hashlib.sha256(path.read_bytes()).hexdigest() + "  " + relative.as_posix())
(root / "SHA256SUMS").write_text("\n".join(rows) + "\n")
print("Recorded", len(rows), "files")

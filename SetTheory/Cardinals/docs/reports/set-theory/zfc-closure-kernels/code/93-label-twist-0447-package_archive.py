#!/usr/bin/env python3
"""Build the portable research ZIP, excluding only generated work directories."""
from pathlib import Path
import json
import zipfile

ROOT = Path(__file__).resolve().parents[1]
DEST = ROOT.parent / (ROOT.name + ".zip")
root_build_files = {
    "zfc_sub245_research.aux", "zfc_sub245_research.log",
    "zfc_sub245_research.out", "zfc_sub245_research.toc",
}
entries = []
for path in sorted(ROOT.rglob("*")):
    rel = path.relative_to(ROOT)
    if not path.is_file() or path.is_symlink():
        continue
    if "__pycache__" in rel.parts or path.suffix == ".pyc":
        continue
    if rel.parts[0] in {"verification", "replay245"}:
        continue
    if len(rel.parts) > 1 and rel.parts[:2] == ("grammar", "reproduced"):
        continue
    if len(rel.parts) == 1 and rel.name in root_build_files:
        continue
    entries.append((path, ROOT.name + "/" + rel.as_posix()))
with zipfile.ZipFile(DEST, "w", compression=zipfile.ZIP_DEFLATED,
                     compresslevel=9) as archive:
    for path, name in entries:
        archive.write(path, name)
with zipfile.ZipFile(DEST) as archive:
    assert archive.testzip() is None
    for name in archive.namelist():
        assert not name.startswith("/") and ".." not in Path(name).parts
print(json.dumps({"status": "PASS_ARCHIVE_CREATED", "path": str(DEST),
                  "files": len(entries), "bytes": DEST.stat().st_size,
                  "uncompressed_bytes": sum(p.stat().st_size for p, _ in entries)},
                 indent=2))

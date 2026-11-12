"""Package the complete source, PDF, proof certificates, and evidence."""
from pathlib import Path
import hashlib
import json
import zipfile

root = Path(__file__).resolve().parent
excluded = {"report.aux", "report.log", "report.out", "report.toc", "MANIFEST.sha256.json"}
files = sorted(p for p in root.rglob("*") if p.is_file()
               and "__pycache__" not in p.parts
               and p.relative_to(root).as_posix() not in excluded)
manifest = [{"path":p.relative_to(root).as_posix(), "bytes":p.stat().st_size,
             "sha256":hashlib.sha256(p.read_bytes()).hexdigest()} for p in files]
(root / "MANIFEST.sha256.json").write_text(json.dumps(manifest, indent=2) + "\n")
files.append(root / "MANIFEST.sha256.json")
archive = root.parent / (root.name + ".zip")
with zipfile.ZipFile(archive, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as z:
    for p in sorted(files):
        z.write(p, root.name + "/" + p.relative_to(root).as_posix())
with zipfile.ZipFile(archive) as z:
    assert z.testzip() is None
    members = len(z.infolist())
print(json.dumps({"archive":str(archive), "files":members, "bytes":archive.stat().st_size,
                  "sha256":hashlib.sha256(archive.read_bytes()).hexdigest()}, indent=2))

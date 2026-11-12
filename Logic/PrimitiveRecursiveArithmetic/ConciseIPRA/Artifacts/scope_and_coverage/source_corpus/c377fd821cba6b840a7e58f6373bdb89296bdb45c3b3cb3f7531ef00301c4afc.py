"""Create a distributable archive, excluding build caches and bytecode."""
from pathlib import Path
import hashlib
import zipfile

ROOT = Path(__file__).resolve().parent
members = sorted(p for p in ROOT.rglob("*") if p.is_file()
                 and not any(part in ("build", "__pycache__")
                             for part in p.relative_to(ROOT).parts)
                 and p.suffix != ".pyc" and p.name != "MANIFEST.sha256")
manifest = ROOT / "MANIFEST.sha256"
manifest.write_text("".join(hashlib.sha256(p.read_bytes()).hexdigest() + "  " +
                            p.relative_to(ROOT).as_posix() + "\n" for p in members))
target = ROOT.parent / (ROOT.name + ".zip")
with zipfile.ZipFile(target, "w", compression=zipfile.ZIP_DEFLATED,
                     compresslevel=9) as archive:
    for path in members + [manifest]:
        archive.write(path, ROOT.name + "/" + path.relative_to(ROOT).as_posix())
with zipfile.ZipFile(target) as archive:
    bad = archive.testzip()
    if bad is not None:
        raise SystemExit("Archive integrity failure: " + bad)
    if not any(name.endswith(".pdf") for name in archive.namelist()):
        raise SystemExit("The compiled PDF is missing")
    if not any(name.endswith(".tex") for name in archive.namelist()):
        raise SystemExit("The LaTeX source is missing")
print(target)
print("Files:", len(members) + 1)
print("Bytes:", target.stat().st_size)
print("SHA-256:", hashlib.sha256(target.read_bytes()).hexdigest())

"""Create a deterministic ZIP with an integrity manifest; omit build debris."""
import hashlib
import json
from pathlib import Path
import zipfile

ROOT = Path(__file__).resolve().parent


def payload():
    return sorted(p for p in ROOT.rglob("*") if p.is_file()
                  and "build" not in p.relative_to(ROOT).parts
                  and "__pycache__" not in p.relative_to(ROOT).parts
                  and p.suffix != ".pyc" and p.name != "MANIFEST.sha256.json")


def main():
    entries = [{"file": p.relative_to(ROOT).as_posix(),
                "bytes": p.stat().st_size,
                "sha256": hashlib.sha256(p.read_bytes()).hexdigest()} for p in payload()]
    manifest = ROOT / "MANIFEST.sha256.json"
    manifest.write_text(json.dumps(entries, indent=2) + "\n")
    destination = ROOT.parent / (ROOT.name + ".zip")
    with zipfile.ZipFile(destination, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for path in sorted(payload() + [manifest]):
            info = zipfile.ZipInfo(ROOT.name + "/" + path.relative_to(ROOT).as_posix(),
                                   date_time=(2026, 11, 10, 12, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            archive.writestr(info, path.read_bytes(), compresslevel=9)
    with zipfile.ZipFile(destination) as archive:
        if archive.testzip() is not None:
            raise ValueError("ZIP CRC validation failed")
    print(json.dumps({"zip": str(destination), "bytes": destination.stat().st_size,
                      "sha256": hashlib.sha256(destination.read_bytes()).hexdigest(),
                      "payload_files": len(entries)}, indent=2))


if __name__ == "__main__":
    main()

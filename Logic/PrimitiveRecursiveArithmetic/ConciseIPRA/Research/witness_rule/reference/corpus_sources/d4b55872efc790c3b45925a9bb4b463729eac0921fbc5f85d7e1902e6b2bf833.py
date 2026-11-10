"""Build and verify the final ZIP and payload hashes."""
import hashlib
import json
from pathlib import Path
import zipfile

ROOT = Path(__file__).resolve().parent
NAME = "ipra_three_schema_2026-11-09"


def payload():
    return sorted(path for path in ROOT.rglob("*") if path.is_file()
                  and not any(part in ("__pycache__", "tmp", ".git") for part in path.parts)
                  and path.name != "MANIFEST.json"
                  and path.suffix not in (".pyc", ".aux", ".out", ".toc"))


def main():
    manifest = [{"path": str(p.relative_to(ROOT)), "bytes": p.stat().st_size,
                 "sha256": hashlib.sha256(p.read_bytes()).hexdigest()} for p in payload()]
    (ROOT / "MANIFEST.json").write_text(json.dumps({"files": manifest}, indent=2) + "\n")
    destination = ROOT.parent / (NAME + ".zip")
    with zipfile.ZipFile(destination, "w", zipfile.ZIP_DEFLATED, compresslevel=9) as z:
        for p in payload() + [ROOT / "MANIFEST.json"]:
            info = zipfile.ZipInfo(NAME + "/" + str(p.relative_to(ROOT)))
            info.date_time = (2026, 11, 9, 12, 0, 0)
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o644 << 16
            z.writestr(info, p.read_bytes())
    with zipfile.ZipFile(destination) as z:
        if z.testzip() is not None:
            raise ValueError("ZIP CRC verification failed")
        for item in manifest:
            b = z.read(NAME + "/" + item["path"])
            if len(b) != item["bytes"] or hashlib.sha256(b).hexdigest() != item["sha256"]:
                raise ValueError("Manifest mismatch: " + item["path"])
    print(json.dumps({"file": str(destination), "bytes": destination.stat().st_size,
                      "members": len(manifest) + 1,
                      "sha256": hashlib.sha256(destination.read_bytes()).hexdigest(),
                      "verified": True}, indent=2))


if __name__ == "__main__":
    main()

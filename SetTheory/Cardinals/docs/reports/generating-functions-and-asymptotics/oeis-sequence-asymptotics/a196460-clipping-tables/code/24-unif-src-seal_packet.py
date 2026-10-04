#!/usr/bin/env python3
"""Fresh local manifest/archive utility; does not execute source inputs."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import stat
import zipfile

HERE = Path(__file__).resolve().parent


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    manifest = HERE / "MANIFEST.sha256"
    archive = HERE.with_suffix(".zip")
    receipt = HERE.parent / (HERE.name + "-receipt.json")
    assert not manifest.exists() and not archive.exists() and not receipt.exists()
    before = json.loads((HERE / "evidence/input-before.json").read_text())
    after = json.loads((HERE / "evidence/input-after.json").read_text())
    assert before["objects"] == after["objects"]
    assert after["unchanged_from_before"] is True
    payloads = sorted(p for p in HERE.rglob("*") if p.is_file())
    assert all(not p.is_symlink() for p in HERE.rglob("*"))
    assert not any("__pycache__" in p.parts for p in payloads)
    with manifest.open("x") as f:
        for p in payloads:
            f.write(digest(p.read_bytes()) + "  " + str(p.relative_to(HERE)) + "\n")
    all_files = sorted([*payloads, manifest])
    for p in all_files:
        p.chmod(0o444)
    with zipfile.ZipFile(archive, "x", compression=zipfile.ZIP_DEFLATED) as z:
        for p in all_files:
            z.write(p, str(Path(HERE.name) / p.relative_to(HERE)))
    with zipfile.ZipFile(archive) as z:
        expected = [str(Path(HERE.name) / p.relative_to(HERE)) for p in all_files]
        assert z.namelist() == expected
        assert len(set(z.namelist())) == len(expected)
        for p, name in zip(all_files, expected):
            assert z.read(name) == p.read_bytes()
            assert stat.S_IMODE(z.getinfo(name).external_attr >> 16) == 0o444
    for p in sorted((p for p in HERE.rglob("*") if p.is_dir()), reverse=True):
        p.chmod(0o555)
    HERE.chmod(0o555)
    archive.chmod(0o444)
    result = {
        "sealed_utc": datetime.now(timezone.utc).isoformat(),
        "packet": str(HERE), "payload_count": len(payloads),
        "archive_members": len(all_files),
        "proof_sha256": digest((HERE / "PROOF.md").read_bytes()),
        "manifest_sha256": digest(manifest.read_bytes()),
        "archive_sha256": digest(archive.read_bytes()),
        "archive_member_bytes_and_modes_verified": True,
        "input_objects_preserved": len(before["objects"]),
        "input_preservation": "bytes, object set, size, mode and mtime_ns; atime excluded",
        "limits": "Local read-only delivery convention; not WORM or external timestamp."
    }
    with receipt.open("x") as f:
        json.dump(result, f, indent=2)
        f.write("\n")
    receipt.chmod(0o444)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()

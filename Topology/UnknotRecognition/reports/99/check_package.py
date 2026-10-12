"""Check recorded artifact hashes and replay the standalone finite examples.

The code_manifest.json scope is code, native overlay, and recorded evidence.
The article and final archive manifest are maintained separately.
"""

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import subprocess
import sys


def require(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--hashes-only", action="store_true")
    parser.add_argument("--native-repo", type=Path,
                        help="also replay the ten native packets against this patched checkout")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    manifest = json.loads((root / "code_manifest.json").read_text())
    require(manifest["schema"] == "proveit-dual-forest-code-manifest-v1", "unknown manifest")
    seen, total = set(), 0
    for item in manifest["files"]:
        relative = PurePosixPath(item["path"])
        require(not relative.is_absolute() and relative.parts
                and all(p not in (".", "..") for p in relative.parts), "unsafe manifest path")
        require(item["path"] not in seen, "duplicate manifest path")
        seen.add(item["path"])
        path = root.joinpath(*relative.parts)
        require(path.is_file() and not path.is_symlink(), "missing or linked file: " + item["path"])
        require(path.resolve().is_relative_to(root), "manifest path escapes package")
        data = path.read_bytes()
        require(len(data) == item["bytes"], "size mismatch: " + item["path"])
        require(hashlib.sha256(data).hexdigest() == item["sha256"], "hash mismatch: " + item["path"])
        total += len(data)
    report = {"all_passed": True, "verified_files": len(seen), "verified_bytes": total,
              "source_revision": manifest["source_revision"]}
    if not args.hashes_only:
        replay = subprocess.run([sys.executable, "-B", str(root / "code/forest_search/replay_demo.py")],
                                check=True, capture_output=True, text=True)
        report["finite_replay"] = json.loads(replay.stdout)
    if args.native_repo is not None:
        replay = subprocess.run([sys.executable, "-B", str(root / "code/replay_native_packets.py"),
                                 str(args.native_repo.resolve())],
                                check=True, capture_output=True, text=True)
        report["native_replay"] = json.loads(replay.stdout)
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()

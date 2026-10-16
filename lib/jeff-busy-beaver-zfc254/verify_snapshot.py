"""Check imported Git blobs, the exact Coq closure, and the literal machine.

This does not compile Coq. Use the unchanged ZF/m254/check.py on a scratch copy
for the upstream end-to-end check. No network or upstream checkout is required.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", type=Path,
                        help="also check the manifest against this upstream Git checkout")
    args = parser.parse_args()
    manifest = json.loads((ROOT / "upstream-manifest.json").read_text())
    expected = {item["path"]: item for item in manifest["files"]}
    for path, item in expected.items():
        data = (ROOT / path).read_bytes()
        blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        if blob != item["git_blob"] or len(data) != item["bytes"]:
            raise SystemExit(f"Imported file differs from pinned Git blob: {path}")
    if args.upstream:
        rows = subprocess.check_output(
            ["git", "ls-tree", "-r", manifest["upstream_commit"]],
            cwd=args.upstream, text=True,
        ).splitlines()
        tree = {}
        for row in rows:
            info, path = row.split("\t", 1)
            mode, kind, blob = info.split()
            tree[path] = (mode, kind, blob)
        for path, item in expected.items():
            if tree.get(path) != (item["git_mode"], "blob", item["git_blob"]):
                raise SystemExit(f"Manifest entry differs from upstream commit: {path}")
        package = {path for path in tree if path.startswith("ZF/m254/")}
        if not package <= expected.keys():
            raise SystemExit("The import omits an upstream ZF/m254 file")
    sys.dont_write_bytecode = True
    spec = importlib.util.spec_from_file_location("m254_check", ROOT / "ZF/m254/check.py")
    if spec is None or spec.loader is None:
        raise SystemExit("Cannot load upstream checker")
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    error = checker.check_table()
    if error:
        raise SystemExit(error)
    closure = [str(path.relative_to(ROOT))
               for path in checker.closure(checker.ROOTS, checker.TOP)]
    if closure != manifest["coq_dependency_order"]:
        raise SystemExit("Coq dependency closure differs from the pinned manifest")
    print(f"Verified {len(expected)} unchanged upstream blobs at "
          f"{manifest['upstream_commit']}; {len(closure)} Coq dependencies.")
    print("Literal 254-state table and published machine SHA-256 match. "
          "Coq compilation was not run by this helper.")


if __name__ == "__main__":
    main()

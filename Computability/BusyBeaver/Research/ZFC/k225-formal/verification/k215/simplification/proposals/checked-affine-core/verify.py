#!/usr/bin/env python3
"""Check archived file identities and replay independent finite witnesses.

This is not a replacement for the Coq/Lean compiler checks. See each component's
README for those commands. Witnesses are rerun in a temporary copy so archived
receipts and their hashes remain unchanged.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile


def main():
    if sys.flags.optimize:
        raise SystemExit("Run without -O or PYTHONOPTIMIZE: witness checks use assertions.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--hashes-only", action="store_true")
    parser.add_argument("--universal", action="store_true",
                        help="Also rerun the symbolic arbitrary-value increment checks.")
    args = parser.parse_args()
    if args.hashes_only and args.universal:
        parser.error("--hashes-only and --universal cannot be combined")
    root = Path(__file__).resolve().parent
    manifest = json.loads((root / "MANIFEST.sha256.json").read_text())
    failures = []
    for name, record in manifest["files"].items():
        path = root / name
        if Path(name).is_absolute() or ".." in Path(name).parts:
            failures.append(f"Unsafe manifest path: {name}")
            continue
        if not path.is_file() or path.is_symlink():
            failures.append(f"Missing file or unexpected symbolic link: {name}")
            continue
        data = path.read_bytes()
        if len(data) != record["bytes"] or hashlib.sha256(data).hexdigest() != record["sha256"]:
            failures.append(f"File identity mismatch: {name}")
    if failures:
        print("\n".join(failures), file=sys.stderr)
        raise SystemExit(1)
    print(f"PASS: {len(manifest['files'])} archived file identities.", flush=True)
    if args.hashes_only:
        return
    env = os.environ.copy()
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    with tempfile.TemporaryDirectory(prefix="k215-independent-audit-") as tmp:
        work = Path(tmp) / "state_search"
        shutil.copytree(root / "state_search", work)
        command = [sys.executable, "verify.py"]
        if args.universal:
            command.append("--universal")
        subprocess.run(command, cwd=work, env=env, check=True)
        extension = work / "forced_provider189"
        for script in ("audit_forced_provider.py", "check_near_survivors.py", "inspect_layouts.py"):
            subprocess.run([sys.executable, script], cwd=extension, env=env, check=True)
        reachability = work / "source_reachability"
        graph = root / "affine_core" / "input_graph.json"
        source_commands = [
            ["crosscheck_direct.py", "--graph", str(graph),
             "--receipt", "reachability_probe.json", "--out", str(Path(tmp) / "direct.json")],
            ["check_semantic_binding.py", "--graph", str(graph),
             "--leaves", str(root / "affine_core" / "leaves.json"),
             "--dag", str(root / "affine_core" / "source_deps" / "K215F" / "DagPerm.v"),
             "--out", str(Path(tmp) / "binding.json")],
        ]
        for command in source_commands:
            subprocess.run([sys.executable, *command], cwd=reachability, env=env, check=True)
    print("PASS: independent finite audits. Formal build commands are separate.")


if __name__ == "__main__":
    main()

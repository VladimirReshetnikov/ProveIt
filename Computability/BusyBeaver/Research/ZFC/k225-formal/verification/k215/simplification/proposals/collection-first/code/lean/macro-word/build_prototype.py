#!/usr/bin/env python3
"""Compile the macro-word prototype against pinned repository sources.

Usage: python3 build_prototype.py --repo PATH --lean PATH --out NEW_DIRECTORY
No network requests and no edits to repository sources.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import time

BASE_COMMIT = "6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95"


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", type=Path, required=True)
    ap.add_argument("--lean", type=Path, required=True)
    ap.add_argument("--out", type=Path, required=True)
    args = ap.parse_args()
    repo, lean, out = args.repo.resolve(), args.lean.resolve(), args.out.resolve()
    here = Path(__file__).resolve().parent
    actual = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=repo, text=True).strip()
    if actual != BASE_COMMIT:
        raise SystemExit(f"Expected {BASE_COMMIT}, got {actual}")
    out.mkdir(parents=True, exist_ok=False)
    roots = [repo / "Computability/BusyBeaver/Lean", repo / "Logic/FirstOrder/Lean"]
    own = {"BusyBeaver.ZFC.GenericMacroWord", "BusyBeaver.ZFC.AXReadCons", "BusyBeaver.ZFC.AXWordsEqual"}
    seen, order, paths = set(), [], {}

    def visit(module):
        if module in seen or module == "Init":
            return
        seen.add(module)
        rel = Path(module.replace(".", "/") + ".lean")
        options = [here / rel] if module in own else [r / rel for r in roots]
        source = next((p for p in options if p.is_file()), None)
        if source is None:
            raise SystemExit(f"Missing project source {module}")
        paths[module] = source
        for line in source.read_text().splitlines():
            if line.startswith("import "):
                for dep in line[len("import "):].split():
                    visit(dep)
        order.append(module)

    visit("BusyBeaver.ZFC.AXWordsEqual")
    pins = {item["module"]: item["source_sha256"]
            for item in json.loads((here / "receipt.json").read_text())["modules"]}
    for module in order:
        if sha(paths[module].read_bytes()) != pins[module]:
            raise SystemExit(f"Source differs from the checked snapshot: {module}")
        dest = out / (module.replace(".", "/") + ".lean")
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(paths[module], dest)
    env = dict(os.environ, LEAN_PATH=str(out))
    receipt = {"base_commit": actual, "lean": subprocess.check_output([str(lean), "--version"], text=True).strip(),
               "scope": "30 repository dependencies and 3 new prototype modules; no endpoint rebuild", "modules": []}
    (out / "logs").mkdir()
    for module in order:
        rel = module.replace(".", "/")
        cmd = [str(lean), "--threads=1", "-o", rel + ".olean", rel + ".lean"]
        start = time.monotonic()
        result = subprocess.run(cmd, cwd=out, env=env, capture_output=True, text=True)
        log = result.stdout + result.stderr
        (out / "logs" / (module + ".log")).write_text(log)
        item = {"module": module, "source_sha256": sha(paths[module].read_bytes()),
                "returncode": result.returncode, "seconds": round(time.monotonic() - start, 3),
                "log_sha256": sha(log.encode())}
        receipt["modules"].append(item)
        print(module, result.returncode, item["seconds"], flush=True)
        (out / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
        if result.returncode:
            print(log, flush=True)
            raise SystemExit(result.returncode)
        if module in own:
            print(log, flush=True)
    receipt["passed"] = True
    (out / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")


if __name__ == "__main__":
    main()

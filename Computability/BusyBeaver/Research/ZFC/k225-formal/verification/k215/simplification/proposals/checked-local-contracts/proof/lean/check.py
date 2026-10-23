#!/usr/bin/env python3
"""Rebuild the standalone checked K215 contract library from pinned source bytes.

Only Python's standard library and Lean 4.32.0 are needed. No network or mathlib.
The output directory must be absent or empty; no previously built object is used.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--lean", required=True, type=Path)
    ap.add_argument("--out", required=True, type=Path)
    args = ap.parse_args()
    root = Path(__file__).resolve().parent
    out = args.out.resolve()
    lean = args.lean.resolve()
    if out.exists() and any(out.iterdir()):
        raise SystemExit("Use a new or empty output directory.")
    out.mkdir(parents=True, exist_ok=True)
    sources = json.loads((root / "sources.json").read_text())
    receipt = {
        "scope": "Standalone exact K215 control contracts; not the ZFC endpoint",
        "status": "STARTED",
        "modules": [],
        "source_manifest_sha256": digest(root / "sources.json"),
        "compiler_sha256": digest(lean),
    }
    env = dict(os.environ, LEAN_PATH=str(out))
    try:
        version = subprocess.run([str(lean), "--version"], check=True, text=True,
                                 stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        receipt["version"] = version.stdout.strip()
        if "version 4.32.0," not in version.stdout:
            raise RuntimeError("The reviewed version is Lean 4.32.0.")
        for row in sources:
            source = root / row["path"]
            if digest(source) != row["sha256"]:
                raise RuntimeError("Input hash mismatch: " + row["path"])
            if re.search(r"\b(sorry|admit|axiom)\b", source.read_text()):
                # Inspect commands after discarding comments, rather than reject prose.
                text = source.read_text()
                depth = 0
                clean = []
                i = 0
                while i < len(text):
                    if text.startswith("/-", i):
                        depth += 1; i += 2
                    elif depth and text.startswith("-/", i):
                        depth -= 1; i += 2
                    elif depth:
                        i += 1
                    elif text.startswith("--", i):
                        end = text.find("\n", i)
                        i = len(text) if end < 0 else end
                    else:
                        clean.append(text[i]); i += 1
                if re.search(r"\b(sorry|admit|axiom)\b", "".join(clean)):
                    raise RuntimeError("Unexpected admission or axiom in " + row["path"])
            obj = out / Path(*row["module"].split(".")).with_suffix(".olean")
            obj.parent.mkdir(parents=True, exist_ok=True)
            command = [str(lean), "-o", str(obj), str(source)]
            start = time.monotonic()
            result = subprocess.run(command, cwd=root / row["root"], env=env,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                    text=True)
            elapsed = time.monotonic() - start
            log = out / (row["module"] + ".log")
            log.write_text(result.stdout)
            record = {
                "module": row["module"], "source_sha256": row["sha256"],
                "command": command, "cwd": str(root / row["root"]),
                "exit_code": result.returncode, "seconds": round(elapsed, 6),
                "log": log.name, "log_sha256": digest(log),
            }
            receipt["modules"].append(record)
            print(row["module"], "exit", result.returncode, flush=True)
            if result.returncode:
                raise RuntimeError("Compiler failure; inspect " + str(log))
            record["warning_count"] = result.stdout.count("warning:")
            if "sorryAx" in result.stdout:
                raise RuntimeError("Unexpected admission; inspect " + str(log))
            if record["warning_count"] != row.get("expected_warnings", 0):
                raise RuntimeError("Unexpected warning count; inspect " + str(log))
            record["object_sha256"] = digest(obj)
        final = (out / "ClosedControl215.log").read_text()
        expected = ("SetTheory.BusyBeaver.ZFC.KLeftFrame215."
                    "every_template_control_closed")
        if expected not in final:
            raise RuntimeError("Missing final named theorem report.")
        if "[propext, Classical.choice, Quot.sound]" not in final:
            raise RuntimeError("Missing expected final axiom profile.")
        receipt["status"] = "PASS_FOCUSED_KERNEL"
    except Exception as exc:
        receipt["status"] = "FAIL"
        receipt["error"] = str(exc)
        raise
    finally:
        (out / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({"status": receipt["status"], "modules": len(receipt["modules"]),
                      "version": receipt["version"]}))


if __name__ == "__main__":
    main()

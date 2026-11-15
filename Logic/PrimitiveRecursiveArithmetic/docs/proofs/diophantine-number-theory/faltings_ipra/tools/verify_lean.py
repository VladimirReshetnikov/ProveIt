#!/usr/bin/env python3
"""Compile every standalone module and preserve its kernel dependency audit."""
from pathlib import Path
import argparse
import json
import shutil
import subprocess


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--lean", default=shutil.which("lean") or "lean")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    out = root/"verification"
    out.mkdir(exist_ok=True)
    version = subprocess.check_output([args.lean, "--version"], text=True).strip()
    modules = []
    for name in ["FiniteSearch", "Logic", "Curves"]:
        proc = subprocess.run([args.lean, name+".lean"], cwd=root/"lean",
                              capture_output=True, text=True)
        text = proc.stdout + proc.stderr
        (out/(name+".log")).write_text(text)
        if proc.returncode:
            raise SystemExit(text)
        if "sorryAx" in text or "Classical.choice" in text:
            raise SystemExit("Unexpected kernel dependency: " + text)
        modules.append({"module": name+".lean", "exit_code": proc.returncode,
                        "audit_log": name+".log"})
    result = {"result": "PASS", "version": version, "modules": modules,
              "scope": "native Lean checks; not an embedded iPRA derivation"}
    (out/"lean.json").write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()

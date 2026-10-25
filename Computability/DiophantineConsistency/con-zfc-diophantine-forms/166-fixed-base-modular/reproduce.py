#!/usr/bin/env python3
"""Rebuild the selected new sources and equations; compare every emitted JSON.

The default uses a temporary directory and changes no deliverable. --output
keeps a reconstruction in a new or empty directory. No search or network is used.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def run(arguments):
    command = [sys.executable, "-B"]
    if sys.flags.optimize:
        command.append("-O")
    environment = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
    process = subprocess.run(command + list(map(str, arguments)),
                             check=True, capture_output=True, text=True,
                             env=environment, cwd=ROOT)
    return json.loads(process.stdout)


def build(destination):
    parent = ROOT / "upstream/factorial_free/direct"
    stages = destination / "stages"
    equations = destination / "equations"
    steps = [
        ("stages/fixed_base", [
            ROOT / "code/build_fixed_base.py", "--parent", parent,
            "--output", stages / "fixed_base"]),
        ("stages/modular", [
            ROOT / "code/build_modular.py", "--parent", parent,
            "--source", stages / "fixed_base/raw_source.json",
            "--output", stages / "modular"]),
        ("stages/compressed", [
            ROOT / "code/build_frame_compressed.py", "--parent", parent,
            "--source", stages / "modular", "--output", stages / "compressed"]),
        ("equations/balanced", [
            ROOT / "code/refine_fixed_source.py", stages / "compressed",
            equations / "balanced", "--parent", parent,
            "--ashift", "6", "--zshift", "0"]),
        ("equations/compact", [
            ROOT / "code/refine_fixed_source.py", stages / "compressed",
            equations / "compact", "--parent", parent,
            "--dense", "--ashift", "6", "--zshift", "0"]),
    ]
    matched = []
    stages_checked = {}
    for label, arguments in steps:
        stages_checked[label] = run(arguments)
        generated = sorted((destination / label).glob("*.json"))
        if len(generated) != (4 if label.startswith("equations/") else 11):
            raise ValueError("Unexpected emitted file count for " + label)
        for path in generated:
            relative = path.relative_to(destination)
            expected = ROOT / relative
            if expected.read_bytes() != path.read_bytes():
                raise ValueError("Byte reproduction differs: " + str(relative))
            matched.append({
                "path": relative.as_posix(),
                "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            })
    if len(matched) != 41:
        raise ValueError("Unexpected total reconstruction census")
    return {
        "status": "PASS", "byte_identical_json_files": len(matched),
        "files": matched, "stages": stages_checked,
        "scope": "Deterministic finite reproduction; semantic proofs are separate.",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()
    if args.output:
        destination = args.output.resolve()
        if destination.exists() and any(destination.iterdir()):
            raise ValueError("--output must be a new or empty directory")
        destination.mkdir(parents=True, exist_ok=True)
        result = build(destination)
    else:
        with tempfile.TemporaryDirectory(prefix="conzfc-fixed-modular-") as tmp:
            result = build(Path(tmp))
    output = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.receipt:
        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.write_text(output)
    print(output, end="")


if __name__ == "__main__":
    main()

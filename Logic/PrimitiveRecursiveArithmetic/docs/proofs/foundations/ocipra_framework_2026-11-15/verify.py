#!/usr/bin/env python3
from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def run(cmd: list[str], cwd: Path) -> None:
    print("+", " ".join(cmd), flush=True)
    subprocess.run(cmd, cwd=cwd, check=True)


def check_json() -> None:
    paths = sorted(ROOT.rglob("*.json"))
    for path in paths:
        with path.open("r", encoding="utf-8") as stream:
            json.load(stream)
    print(f"+ parsed {len(paths)} JSON files", flush=True)


def strip_lean_comments(text: str) -> str:
    # Sufficient for these small outline files; comments are not used as syntax.
    previous = None
    while previous != text:
        previous = text
        text = re.sub(r"/-.*?-/", "", text, flags=re.DOTALL)
    return re.sub(r"--.*$", "", text, flags=re.MULTILINE)


def check_lean_outline() -> None:
    forbidden = {
        r"\baxiom\b": "declared axiom",
        r"\bsorry\b": "sorry placeholder",
        r":=\s*True\b": "trivial proposition placeholder",
    }
    files = sorted((ROOT / "lean").rglob("*.lean"))
    for path in files:
        body = strip_lean_comments(path.read_text(encoding="utf-8"))
        for pattern, label in forbidden.items():
            if re.search(pattern, body):
                raise RuntimeError(f"{label} found in {path.relative_to(ROOT)}")
    print(f"+ inspected {len(files)} Lean outline files for admitted placeholders", flush=True)


def check_schema_example() -> None:
    example = json.loads((ROOT / "schema" / "example_contract.json").read_text())
    required = {"name", "statement_kind", "programs", "resources", "verifier", "proof_backend"}
    missing = required - set(example)
    if missing:
        raise RuntimeError(f"schema example misses required fields: {sorted(missing)}")
    if not example["programs"].get("fixed_or_clocked"):
        raise RuntimeError("schema example is not fixed or clocked")
    if not example["resources"].get("primitive_recursive_bound"):
        raise RuntimeError("schema example lacks a primitive-recursive resource bound")
    if not example["verifier"].get("bounded_decidable"):
        raise RuntimeError("schema example lacks a bounded verifier")
    print("+ checked schema example", flush=True)


def main() -> None:
    code = ROOT / "code"
    check_json()
    check_schema_example()
    check_lean_outline()
    run([sys.executable, "-m", "unittest", "-v", "test_ocipra.py"], code)
    run([sys.executable, "demo.py"], code)


if __name__ == "__main__":
    main()

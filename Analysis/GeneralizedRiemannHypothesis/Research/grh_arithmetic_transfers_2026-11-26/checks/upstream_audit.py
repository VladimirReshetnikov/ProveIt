#!/usr/bin/env python3
"""Static, reproducible source audit of the pinned grh-lean checkout.

This is not a Lean build, kernel replay, or proof of mathematical correctness.
No third-party Python modules are required. Nested Lean comments and string
literals are removed before scanning the listed trust-sensitive tokens.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

PIN = "72fead102f663d5c7a407964a13dc0cf9d977207"
SENSITIVE = {"sorry", "admit", "axiom", "unsafe", "native_decide",
             "implemented_by", "ofReduceBool", "sorryAx"}
KEY_FILES = [
    "README.md", "grh/README.md", "grh/GUIDE.md", "grh/lean-toolchain",
    "grh/lake-manifest.json", "grh/lakefile.toml", "grh/src/Statements.lean",
    "grh/src/Main.lean", "grh/scripts/PrintAxioms.lean", "grh/Challenge.lean",
    "grh/src/New/Reduction/MainInequality.lean",
    "grh/src/New/Reduction/OneSidedBound.lean",
    "grh/src/New/Reduction/Zeros/Criterion.lean",
    "grh/src/New/Reduction/Lattices/Heights.lean",
    "grh/src/New/Reduction/Lattices/TwistedLattice.lean",
    "grh/src/New/Reduction/ShortAndEnough.lean",
    "grh/src/New/Determinant/Twist/LongForms.lean",
    "grh/src/Lib/GaloisRep/Main/Defs.lean",
    "grh/src/Lib/GaloisRep/Main/AttachedRepresentations.lean",
]


def executable_text(text: str) -> str:
    """Conservative token scan helper, preserving positions and newlines."""
    out = list(text)
    i, depth = 0, 0
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                out[i:i+2] = "  "
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                out[i:i+2] = "  "
                i += 2
            else:
                if text[i] != "\n":
                    out[i] = " "
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            out[i:i+2] = "  "
            i += 2
        elif text.startswith("--", i):
            while i < len(text) and text[i] != "\n":
                out[i] = " "
                i += 1
        elif text[i] == '"':
            out[i] = " "
            i += 1
            while i < len(text):
                c = text[i]
                if c != "\n":
                    out[i] = " "
                i += 1
                if c == "\\" and i < len(text):
                    if text[i] != "\n":
                        out[i] = " "
                    i += 1
                elif c == '"':
                    break
        else:
            i += 1
    if depth:
        raise ValueError("unclosed nested comment")
    return "".join(out)


def audit(root: Path) -> dict:
    sha = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root,
                                  text=True).strip()
    if sha != PIN:
        raise ValueError(f"Expected {PIN}, found {sha}")
    results = {}
    for edition in ("grh", "grh-compact"):
        files = sorted((root / edition / "src").rglob("*.lean"))
        hits, imports, line_count = [], [], 0
        for path in files:
            text = path.read_text(encoding="utf-8")
            line_count += len(text.splitlines())
            code = executable_text(text)
            for match in re.finditer(r"\b(?:" + "|".join(sorted(SENSITIVE)) + r")\b", code):
                hits.append({"path":str(path.relative_to(root)),
                             "line":code.count("\n", 0, match.start()) + 1,
                             "token":match.group()})
            for module in re.findall(r"(?m)^\s*import\s+([^\n]+)", code):
                if "Challenge" in module.split():
                    imports.append(str(path.relative_to(root)))
        results[edition] = {"source_files":len(files), "source_lines":line_count,
                            "sensitive_token_hits":hits,
                            "imports_of_Challenge":imports}
    digests = {p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in KEY_FILES}
    return {
        "repository":"https://github.com/lsernau/grh-lean",
        "commit":sha,
        "method":"Static lexical scan of src trees; nested comments and strings removed.",
        "limitations":["No compilation or kernel replay in this run.",
                       "No audit of Mathlib or external dependencies by this script.",
                       "No semantic theorem-statement check by this script.",
                       "Absence of these lexical tokens alone does not certify a proof."],
        "editions":results,
        "key_file_sha256":digests,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = json.dumps(audit(args.checkout.resolve()), indent=2) + "\n"
    if args.output:
        args.output.write_text(result, encoding="utf-8")
    else:
        print(result, end="")


if __name__ == "__main__":
    main()

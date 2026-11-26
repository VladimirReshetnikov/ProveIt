#!/usr/bin/env python3
"""Reproduce the *static* source inventory; this does not run Lean's kernel.

Usage: python3 code/source_audit.py /path/to/grh-lean > data/source_audit.json
The repository must be the pinned upstream revision. No files are modified.
"""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

PIN = "72fead102f663d5c7a407964a13dc0cf9d977207"
KEY_FILES = [
    "grh/src/Main.lean", "grh/src/Statements.lean",
    "grh/src/New/Reduction/MainInequality.lean",
    "grh/src/New/Reduction/OneSidedBound.lean",
    "grh/src/New/Congruences/Selmer/RootsOfUnity.lean",
    "grh/src/New/Congruences/Selmer/SelmerData.lean",
    "grh/src/New/Congruences/Selmer/TwistingTheorem.lean",
    "grh/src/New/Congruences/FirstOrder/DenominatorBound.lean",
    "grh/lean-toolchain", "grh/lake-manifest.json", "grh/scripts/PrintAxioms.lean",
]


def erase_comments_and_strings(s: str) -> str:
    """Limited lexical scan: nested block comments, line comments, quoted strings.

    Not a Lean parser. The resulting token counts are diagnostic, not proof
    certification; no conclusion about transitive axioms follows from this scan.
    """
    out = list(s)
    i = 0
    depth = 0
    string = False
    line = False
    while i < len(s):
        if depth:
            if s.startswith("/-", i):
                out[i:i+2] = "  "; depth += 1; i += 2; continue
            if s.startswith("-/", i):
                out[i:i+2] = "  "; depth -= 1; i += 2; continue
            if s[i] != "\n": out[i] = " "
        elif line:
            if s[i] == "\n": line = False
            else: out[i] = " "
        elif string:
            if s[i] == "\\" and i + 1 < len(s):
                out[i:i+2] = "  "; i += 2; continue
            if s[i] == '"': string = False
            if s[i] != "\n": out[i] = " "
        elif s.startswith("/-", i):
            out[i:i+2] = "  "; depth = 1; i += 2; continue
        elif s.startswith("--", i):
            out[i:i+2] = "  "; line = True; i += 2; continue
        elif s[i] == '"':
            out[i] = " "; string = True
        i += 1
    return "".join(out)


def run(root: Path) -> dict:
    head = subprocess.check_output(["git", "-C", str(root), "rev-parse", "HEAD"], text=True).strip()
    assert head == PIN, (head, PIN)
    result = {"commit": head, "lean_build_run": False,
              "method": "static source inventory, not a kernel or axiom audit",
              "editions": {}, "key_files": {}}
    for edition in ["grh", "grh-compact"]:
        files = sorted((root/edition/"src").rglob("*.lean"))
        flags = []
        lines = 0
        for p in files:
            s = p.read_text()
            lines += len(s.splitlines())
            clean = erase_comments_and_strings(s)
            for m in re.finditer(r"\b(sorry|admit|axiom|unsafe)\b", clean):
                flags.append({"file": str(p.relative_to(root)), "token": m.group(),
                              "line": clean.count("\n", 0, m.start())+1})
        result["editions"][edition] = {"files": len(files), "lines_including_comments": lines,
                                            "flagged_tokens": flags}
    for name in KEY_FILES:
        p = root/name
        data = p.read_bytes()
        s = data.decode()
        result["key_files"][name] = {
            "sha256": hashlib.sha256(data).hexdigest(), "bytes": len(data),
            "declarations": [dict(name=m.group(2), kind=m.group(1),
                                  line=s.count("\n", 0, m.start())+1)
                             for m in re.finditer(r"(?m)^(?:noncomputable )?(theorem|lemma|def|structure)\s+([^\s({:]+)", s)]}
    base = root/"grh/src"
    modules = {".".join(p.relative_to(base).with_suffix("").parts): p for p in base.rglob("*.lean")}
    visited, external = set(), set()
    todo = ["New.Congruences.Selmer.RootsOfUnity"]
    while todo:
        m = todo.pop()
        if m in visited: continue
        if m not in modules: external.add(m); continue
        visited.add(m)
        for line in modules[m].read_text().splitlines():
            if line.startswith("import "): todo.extend(line[7:].split())
    result["torsion_module_import_closure"] = {
        "internal_count": len(visited), "external_imports": sorted(external),
        "internal_lines": sum(len(modules[m].read_text().splitlines()) for m in visited),
        "modules": sorted(visited),
        "caveat": "Import reachability, not elaborated declaration dependency or mathematical necessity."}
    result["toolchain"] = (root/"grh/lean-toolchain").read_text().strip()
    manifest = json.loads((root/"grh/lake-manifest.json").read_text())
    result["mathlib_revision"] = next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib")
    return result


if __name__ == "__main__":
    if len(sys.argv) != 2: raise SystemExit(__doc__)
    print(json.dumps(run(Path(sys.argv[1]).resolve()), indent=2))

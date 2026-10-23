#!/usr/bin/env python3
"""Read-only inventory of the pinned K215 source snapshot.

This records source bytes, literal input identities and ordinary import edges.
It does not compile proofs or certify declaration-level theorem dependencies.
Only Python's standard library is required.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import tomllib
from pathlib import Path

PIN = "cbf94cb552a3b49509e0eee80e7455d4eb5974c6"
ZFC = "Computability/BusyBeaver/Research/ZFC/"
LEAN = "Computability/BusyBeaver/Lean/BusyBeaver/ZFC/"


def digest(path: Path) -> dict:
    raw = path.read_bytes()
    return {"bytes": len(raw), "lines": len(raw.splitlines()),
            "sha256": hashlib.sha256(raw).hexdigest()}


def no_comments(source: str) -> str:
    """Remove nested block and line comments, preserving line boundaries.

    Quoted strings are preserved. This is sufficient for the conventional
    top-level import declarations in this snapshot, not a full Lean parser.
    """
    out, i, depth, quoted = [], 0, 0, False
    while i < len(source):
        c, two = source[i], source[i:i + 2]
        if depth:
            if two == "/-":
                depth += 1
                i += 2
            elif two == "-/":
                depth -= 1
                i += 2
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
        elif quoted:
            out.append(c)
            i += 1
            if c == "\\" and i < len(source):
                out.append(source[i])
                i += 1
            elif c == '"':
                quoted = False
        elif two == "/-":
            depth = 1
            out.append(" ")
            i += 2
        elif two == "--":
            j = source.find("\n", i)
            i = len(source) if j < 0 else j
        else:
            out.append(c)
            quoted = c == '"'
            i += 1
    if depth:
        raise ValueError("Unterminated comment")
    return "".join(out)


def inventory(repo: Path) -> dict:
    commit = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=repo, text=True).strip()
    if commit != PIN:
        raise ValueError(f"Expected {PIN}; found {commit}")
    lake = tomllib.loads((repo / "lakefile.toml").read_text())
    libraries = {x["name"]: x.get("srcDir", ".")
                 for x in lake["lean_lib"]}
    modules, boundary, missing = {}, set(), set()

    def visit(module: str) -> None:
        if module in modules or module in boundary:
            return
        top = module.split(".")[0]
        if top in {"Init", "Std", "Lean"}:
            boundary.add(module)
            return
        if top not in libraries:
            missing.add(module)
            return
        rel = Path(libraries[top]) / (module.replace(".", "/") + ".lean")
        path = repo / rel
        if not path.is_file():
            missing.add(module)
            return
        text = no_comments(path.read_text())
        imports = [word for line in text.splitlines()
                   if re.match(r"^\s*import\s+", line)
                   for word in line.split()[1:]]
        modules[module] = {"path": str(rel), **digest(path), "imports": imports}
        for name in imports:
            visit(name)

    visit("BusyBeaver.ZFC.KEndpoint215")
    if missing:
        raise ValueError(f"Missing source modules: {sorted(missing)}")
    literals = ["candidate-k215/k215.tm", "candidate-k215/k215.native.tm",
                "candidate-k215/sites215.json"]
    inputs = {p: digest(repo / ZFC / p) for p in literals}
    source = json.loads((repo / ZFC / literals[2]).read_text())
    if not isinstance(source, list):
        raise ValueError("Unexpected source site JSON shape")
    kinds = {}
    for row in source:
        kind = row[1]
        kinds[kind] = kinds.get(kind, 0) + 1
    chosen = [
        LEAN + "KSource215Program.lean", LEAN + "KSource215Data.lean",
        LEAN + "KSim.lean", LEAN + "KRuntimeCore.lean", LEAN + "EnumPerm.lean",
        ZFC + "k225-formal/rocq/rocq-extension/coq/215/Source215.v",
        ZFC + "k225-formal/rocq/rocq-extension/coq/215/NormalizedCert215.v",
        ZFC + "k225-formal/rocqdom/DomRho8.v",
        ZFC + "k225-formal/rocq224/src/DominatedCore.v",
    ]
    measured = {p: digest(repo / p) for p in chosen if (repo / p).is_file()}
    return {
        "scope": "Static import/source inventory only; not a kernel build or axiom audit",
        "repository": "https://github.com/VladimirReshetnikov/ProveIt",
        "commit": commit,
        "lean_endpoint": "BusyBeaver.ZFC.KEndpoint215",
        "project_module_count": len(modules),
        "project_source_bytes": sum(x["bytes"] for x in modules.values()),
        "project_source_lines": sum(x["lines"] for x in modules.values()),
        "explicit_toolchain_imports": sorted(boundary),
        "machine_inputs": inputs,
        "source_sites": {"leaves": len(source), "kinds": kinds,
                         "max_path_length": max(len(x[0]) for x in source)},
        "selected_current_sources": measured,
        "modules": dict(sorted(modules.items())),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    result = inventory(args.repo.resolve())
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({k: result[k] for k in (
        "commit", "project_module_count", "project_source_bytes",
        "project_source_lines", "source_sites")}, indent=2))


if __name__ == "__main__":
    main()

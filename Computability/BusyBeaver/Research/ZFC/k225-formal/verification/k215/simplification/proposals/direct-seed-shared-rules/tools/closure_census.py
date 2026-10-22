#!/usr/bin/env python3
"""Read-only, reproducible Lean import/source census for a ProveIt overlay.

This is a source measurement, not a proof checker or a build-time estimate.
An overlay uses repository-relative paths and takes precedence over the checkout.
Missing or multiply resolved project imports cause failure.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOTS = (
    "Computability/BusyBeaver/Lean",
    "Logic/FirstOrder/Lean",
    "SetTheory/ZF/Lean",
    "SetTheory/BoundedConsistency/Lean",
)

def strip_comments_and_strings(text: str) -> str:
    out, i, depth = [], 0, 0
    while i < len(text):
        pair = text[i:i+2]
        if pair == "/-":
            depth += 1
            out.append(" ")
            i += 2
        elif depth and pair == "-/":
            depth -= 1
            out.append(" ")
            i += 2
        elif depth:
            if text[i] == "\n":
                out.append("\n")
            i += 1
        elif pair == "--":
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            out.append(" ")
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    if text[i] == "\n":
                        out.append("\n")
                    i += 1
        else:
            out.append(text[i])
            i += 1
    if depth:
        raise ValueError("Unclosed Lean block comment")
    return "".join(out)

def census(repo: Path, overlays: list[Path], target: str,
           module_overlays: list[Path] | None = None) -> dict:
    rows, seen, active, external = [], set(), set(), set()
    def resolve(module: str):
        module_path = Path(module.replace(".", "/") + ".lean")
        package_roots = dict(zip(
            ("BusyBeaver", "FirstOrder", "ZF", "BoundedZFCConsistency"), ROOTS))
        for directory in reversed(module_overlays or []):
            path = directory / module_path
            if path.is_file():
                prefix = module.split(".")[0]
                if prefix not in package_roots:
                    raise ValueError(f"Unknown overlay package: {module}")
                return path, Path(package_roots[prefix]) / module_path
        matches = []
        for root in ROOTS:
            relative = Path(root) / (module.replace(".", "/") + ".lean")
            for directory in [*reversed(overlays), repo]:
                path = directory / relative
                if path.is_file():
                    matches.append((path, relative))
                    break
        if len(matches) > 1:
            raise ValueError(f"Ambiguous project import: {module}")
        if matches:
            return matches[0]
        if module.split(".")[0] in {"Init", "Lean", "Std"}:
            return None
        raise FileNotFoundError(f"Unresolved project import: {module}")
    def visit(module: str):
        if module in seen:
            return
        if module in active:
            raise ValueError(f"Import cycle: {module}")
        source = resolve(module)
        if source is None:
            external.add(module)
            return
        path, relative = source
        raw = path.read_bytes()
        text = raw.decode("utf-8")
        clean = strip_comments_and_strings(text)
        imports = [name for line in re.findall(
            r"(?m)^\s*(?:public\s+)?import\s+([^\n]+)", clean)
            for name in line.split()]
        active.add(module)
        for imported in imports:
            visit(imported)
        active.remove(module)
        seen.add(module)
        rows.append({"module": module, "path": relative.as_posix(),
                     "bytes": len(raw), "lines": len(text.splitlines()),
                     "sha256": hashlib.sha256(raw).hexdigest(), "imports": imports})
    visit(target)
    pin = subprocess.check_output(["git", "-C", str(repo), "rev-parse", "HEAD"],
                                  text=True).strip()
    return {"kind": "source-import-census-not-compilation", "repository_commit": pin,
            "target": target, "project_modules": len(rows),
            "source_bytes": sum(row["bytes"] for row in rows),
            "source_lines": sum(row["lines"] for row in rows),
            "external_imports": sorted(external), "modules": rows}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("repository", type=Path)
    parser.add_argument("--overlay", type=Path, action="append", default=[])
    parser.add_argument("--module-overlay", type=Path, action="append", default=[],
                        help="Overlay rooted at Lean package names such as BusyBeaver/")
    parser.add_argument("--target", default="BusyBeaver.ZFC.KEndpoint215")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = census(args.repository.resolve(),
                    [path.resolve() for path in args.overlay], args.target,
                    [path.resolve() for path in args.module_overlay])
    serialized = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(serialized)
        print(json.dumps({key: value for key, value in result.items()
                          if key not in {"modules", "external_imports"}}))
    else:
        print(serialized, end="")

if __name__ == "__main__":
    main()

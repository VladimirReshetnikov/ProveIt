#!/usr/bin/env python3
"""Reproduce the source-level inventory of lsernau/grh-lean.

Usage:
    python3 static_audit.py /path/to/grh-lean --output static_audit_results.json

Requires Python 3.11 or later; uses only its standard library and git.
It reads files and never runs Lean,
Lake, downloaded code, or proof checkers. A clean result is NOT compilation or
kernel-verification evidence. Imports are followed only inside each src tree;
pinned Mathlib and other external dependencies are not audited by this script.

The lexical pass blanks nested block comments, line comments, ordinary strings,
character literals, and quoted identifiers while preserving source line breaks.
Unusual raw/interpolated string syntax is reported for manual inspection. This
is an inventory tool, not a complete Lean parser or an axiom-dependency checker.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import tomllib
from pathlib import Path


REFERENCE_COMMIT = "72fead102f663d5c7a407964a13dc0cf9d977207"
HAZARDS = (
    "sorry", "admit", "axiom", "unsafe", "opaque", "native_decide",
    "implemented_by", "run_elab", "run_cmd", "elab", "macro", "initialize",
    "ofReduceBool", "ofReduceNat",
)
HAZARD_RE = re.compile(r"(?<![\w'])" + "(" + "|".join(HAZARDS) + r")(?![\w'])")
IMPORT_RE = re.compile(r"^\s*(?:public\s+)?import\s+([^\n]+)", re.MULTILINE)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git(repo: Path, *args: str) -> str | None:
    try:
        return subprocess.run(
            ["git", "-C", str(repo), *args], check=True, text=True,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        ).stdout.strip()
    except (FileNotFoundError, subprocess.CalledProcessError):
        return None


def strip_lean_noncode(source: str) -> tuple[str, list[dict]]:
    """Blank comments/literal bodies, preserving newlines and character offsets."""
    out = list(source)
    warnings: list[dict] = []
    n, i = len(source), 0

    def blank(a: int, b: int) -> None:
        for j in range(a, b):
            if source[j] not in "\r\n":
                out[j] = " "

    def warn(pos: int, message: str) -> None:
        warnings.append({"line": source.count("\n", 0, pos) + 1, "message": message})

    while i < n:
        if source.startswith("--", i):
            end = source.find("\n", i)
            end = n if end < 0 else end
            blank(i, end)
            i = end
        elif source.startswith("/-", i):
            start, depth = i, 1
            i += 2
            while i < n and depth:
                if source.startswith("/-", i):
                    depth += 1
                    i += 2
                elif source.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            blank(start, i)
            if depth:
                warn(start, "Unclosed block comment")
        elif source[i] == '"':
            start = i
            if i and (source[i - 1] in "!#" or source[max(0, i - 1):i] == "r"):
                warn(i, "Raw/interpolated string prefix: manually inspect this literal")
            i += 1
            closed = False
            while i < n:
                if source[i] == "\\":
                    i = min(n, i + 2)
                elif source[i] == '"':
                    i += 1
                    closed = True
                    break
                else:
                    i += 1
            blank(start, i)
            if not closed:
                warn(start, "Unclosed ordinary string")
        elif source[i] == "«":
            end = source.find("»", i + 1)
            if end < 0:
                warn(i, "Unclosed quoted identifier")
                end = n - 1
            blank(i, end + 1)
            i = end + 1
        elif source[i] == "'" and (i == 0 or not (source[i - 1].isalnum() or source[i - 1] in "_'")):
            # Apostrophes attached to identifiers are not character delimiters.
            end = None
            if i + 2 < n and source[i + 2] == "'":
                end = i + 3
            elif i + 3 < n and source[i + 1] == "\\" and source[i + 3] == "'":
                end = i + 4
            if end is None:
                i += 1
            else:
                blank(i, end)
                i = end
        else:
            i += 1
    return "".join(out), warnings


def hazard_matches(code: str) -> list[dict]:
    return [
        {"token": m.group(1), "line": code.count("\n", 0, m.start()) + 1}
        for m in HAZARD_RE.finditer(code)
    ]


def reachable(graph: dict[str, list[str]], start: str) -> set[str]:
    seen: set[str] = set()
    todo = [start]
    while todo:
        node = todo.pop()
        if node in seen or node not in graph:
            continue
        seen.add(node)
        todo.extend(graph[node])
    return seen


def import_cycles(graph: dict[str, list[str]]) -> list[list[str]]:
    color: dict[str, int] = {}
    path: list[str] = []
    cycles: list[list[str]] = []

    def visit(node: str) -> None:
        color[node] = 1
        path.append(node)
        for nxt in graph[node]:
            if nxt not in graph:
                continue
            if color.get(nxt, 0) == 0:
                visit(nxt)
            elif color[nxt] == 1:
                cycles.append(path[path.index(nxt):] + [nxt])
        path.pop()
        color[node] = 2

    for node in sorted(graph):
        if not color.get(node):
            visit(node)
    return cycles


def audit_edition(repo: Path, edition: str) -> dict:
    base = repo / edition
    src = base / "src"
    if not src.is_dir():
        raise ValueError(f"Missing source tree: {src}")
    files: dict[str, dict] = {}
    modules: dict[str, list[str]] = {}
    totals = {key: 0 for key in HAZARDS}
    warnings: list[dict] = []
    for file in sorted(src.rglob("*.lean")):
        relative = file.relative_to(src).as_posix()
        module = relative[:-5].replace("/", ".")
        data = file.read_bytes()
        text = data.decode("utf-8")
        code, file_warnings = strip_lean_noncode(text)
        imports = [name for m in IMPORT_RE.finditer(code) for name in m.group(1).split()]
        matches = hazard_matches(code)
        for match in matches:
            totals[match["token"]] += 1
        warnings.extend({"file": relative, **w} for w in file_warnings)
        files[relative] = {
            "sha256": sha256(data), "bytes": len(data),
            "total_lines": len(text.splitlines()),
            "nonblank_code_lines": sum(bool(line.strip()) for line in code.splitlines()),
            "module": module, "imports": imports, "hazard_matches": matches,
        }
        modules[module] = imports

    closure = reachable(modules, "Main")
    external = sorted({i for imports in modules.values() for i in imports if i not in modules})
    main_external = sorted({i for m in closure for i in modules[m] if i not in modules})
    manifest = json.loads((base / "lake-manifest.json").read_text())
    lake_config = tomllib.loads((base / "lakefile.toml").read_text())
    mathlib = next((p for p in manifest["packages"] if p["name"] == "mathlib"), None)
    challenge_path = base / "Challenge.lean"
    challenge_text = challenge_path.read_text()
    challenge_code, challenge_warnings = strip_lean_noncode(challenge_text)
    config_names = (
        "lean-toolchain", "lakefile.toml", "lake-manifest.json", "comparator.json",
        "Challenge.lean", "scripts/PrintAxioms.lean", "README.md", "GUIDE.md",
    )
    config_hashes = {
        name: sha256((base / name).read_bytes())
        for name in config_names if (base / name).is_file()
    }
    manifest_text = "".join(f"{files[p]['sha256']}  {p}\n" for p in sorted(files))
    return {
        "edition": edition,
        "lean_toolchain": (base / "lean-toolchain").read_text().strip(),
        "mathlib_pin": mathlib,
        "lake_configuration": lake_config,
        "source_files": len(files),
        "total_source_lines": sum(f["total_lines"] for f in files.values()),
        "nonblank_code_lines": sum(f["nonblank_code_lines"] for f in files.values()),
        "source_bytes": sum(f["bytes"] for f in files.values()),
        "source_hash_manifest_sha256": sha256(manifest_text.encode()),
        "hazard_token_counts": totals,
        "scanner_warnings": warnings,
        "main_reachable_local_modules_count": len(closure),
        "main_reachable_local_modules": sorted(closure),
        "main_unreachable_local_modules": sorted(set(modules) - closure),
        "external_imports_all": external,
        "external_imports_from_main_closure": main_external,
        "local_import_cycles": import_cycles(modules),
        "source_imports_challenge": any("Challenge" in imp for imp in modules.values()),
        "challenge_outside_src": {
            "hazard_matches": hazard_matches(challenge_code),
            "scanner_warnings": challenge_warnings,
            "note": "Intentional admitted comparison target, not part of src or the Main import closure.",
        },
        "comparator_configuration": json.loads((base / "comparator.json").read_text()),
        "configuration_sha256": config_hashes,
        "source_inventory": files,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("repository", type=Path, help="Local checkout of lsernau/grh-lean")
    parser.add_argument("--output", type=Path, help="Write full JSON here; stdout then receives a compact summary")
    args = parser.parse_args()
    repo = args.repository.resolve()
    head = git(repo, "rev-parse", "HEAD")
    status = git(repo, "status", "--porcelain")
    result = {
        "audit_kind": "static source inventory; NOT compilation or formal proof verification",
        "reference_commit": REFERENCE_COMMIT,
        "checkout_commit": head,
        "matches_reference_commit": head == REFERENCE_COMMIT,
        "working_tree_status_porcelain": status,
        "working_tree_clean": status == "" if status is not None else None,
        "external_dependencies_scanned": False,
        "lean_executed": False,
        "kernel_or_independent_checkers_executed": False,
        "limitations": [
            "A lexical absence scan cannot replace elaboration, type checking, or axiom dependency analysis.",
            "Import reachability is local file reachability, not declaration-level dependency reachability.",
            "Quoted identifiers are blanked; unusual string syntax is reported for manual inspection.",
            "The Mathlib pin is read from the manifest; its transitive sources are not scanned.",
            "Hashes describe the current working files; a dirty checkout may differ from its commit.",
        ],
        "editions": [audit_edition(repo, e) for e in ("grh", "grh-compact")],
    }
    rendered = json.dumps(result, indent=2, ensure_ascii=False) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered)
        summary = {
            "output": str(args.output.resolve()), "commit": head,
            "working_tree_clean": result["working_tree_clean"],
            "editions": [{k: e[k] for k in (
                "edition", "source_files", "total_source_lines", "nonblank_code_lines",
                "main_reachable_local_modules_count", "hazard_token_counts", "scanner_warnings",
            )} for e in result["editions"]],
        }
        print(json.dumps(summary, indent=2, ensure_ascii=False))
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()

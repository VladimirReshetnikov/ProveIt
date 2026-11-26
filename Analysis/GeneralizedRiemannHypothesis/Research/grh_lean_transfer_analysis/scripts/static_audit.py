#!/usr/bin/env python3
"""Reproducible *static* inventory for lsernau/grh-lean.

This is not a Lean parser, compiler, theorem-dependency tracer, or kernel checker.
It masks nested comments and string literals, inventories source tokens and
module imports, and records file hashes. Use Lean's #print axioms and independent
proof checkers for the proof-level trust claim.

Usage: python3 static_audit.py /path/to/grh-lean --out /path/to/audit-output
"""
from __future__ import annotations

import argparse
import collections
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess

WATCH_TOKENS = (
    "sorry", "sorryAx", "admit", "axiom", "unsafe", "native_decide",
    "implemented_by", "extern", "elab", "macro", "syntax", "initialize",
    "builtin_initialize", "run_tac", "run_elab", "ofReduceBool", "ofReduceNat",
    "opaque", "partial",
)
WATCH_RE = re.compile(r"(?<![\w'])\b(" + "|".join(WATCH_TOKENS) + r")\b(?![\w'])")
DECL_RE = re.compile(
    r"(?m)^\s*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|class|inductive|instance|axiom|opaque)\b"
)
IMPORT_RE = re.compile(r"(?m)^\s*(?:public\s+)?import\s+([^\n]+)")
OPTION_RE = re.compile(r"\bset_option\s+([\w.]+)")


def mask_noncode(text: str) -> str:
    """Mask nested block comments, line comments, ordinary strings; keep offsets.

    This snapshot uses no custom source-transforming macros. Lean quoted names,
    character literals, syntax quotations, and exotic literal forms are not a
    complete lexical grammar here; all token results remain source-level leads.
    """
    out = list(text)
    i, n, depth = 0, len(text), 0
    while i < n:
        if depth:
            if text.startswith("/-", i):
                out[i:i+2] = "  "
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                out[i:i+2] = "  "
                depth -= 1
                i += 2
            else:
                if text[i] != "\n":
                    out[i] = " "
                i += 1
        elif text.startswith("/-", i):
            out[i:i+2] = "  "
            depth = 1
            i += 2
        elif text.startswith("--", i):
            j = text.find("\n", i)
            if j < 0:
                j = n
            out[i:j] = " " * (j-i)
            i = j
        elif text[i] == '"':
            out[i] = " "
            i += 1
            while i < n:
                c = text[i]
                if c != "\n":
                    out[i] = " "
                i += 1
                if c == "\\" and i < n:
                    if text[i] != "\n":
                        out[i] = " "
                    i += 1
                elif c == '"':
                    break
        else:
            i += 1
    return "".join(out)


def git(repo: Path, *args: str) -> str | None:
    try:
        return subprocess.check_output(["git", "-C", str(repo), *args], text=True).strip()
    except (OSError, subprocess.CalledProcessError):
        return None


def inspect_file(path: Path, repo: Path) -> dict:
    data = path.read_bytes()
    raw = data.decode("utf-8")
    code = mask_noncode(raw)
    return {
        "path": path.relative_to(repo).as_posix(),
        "sha256": hashlib.sha256(data).hexdigest(),
        "bytes": len(data),
        "lines": len(raw.splitlines()),
        "nonblank_lines": sum(bool(s.strip()) for s in raw.splitlines()),
        "nonblank_code_lines": sum(bool(s.strip()) for s in code.splitlines()),
        "declarations_approx": dict(collections.Counter(DECL_RE.findall(code))),
        "imports": [m for group in IMPORT_RE.findall(code) for m in group.split()],
        "set_options": sorted(set(OPTION_RE.findall(code))),
        "eval_directives": [code.count("\n", 0, m.start())+1 for m in re.finditer(r"#eval\b", code)],
        "watch_hits": [
            {"token": m.group(), "line": code.count("\n", 0, m.start()) + 1}
            for m in WATCH_RE.finditer(code)
        ],
    }


def audit_project(repo: Path, edition: str) -> tuple[dict, dict, list]:
    src = repo / edition / "src"
    files = [inspect_file(p, repo) for p in sorted(src.rglob("*.lean"))]
    modules = {}
    for f in files:
        mod = Path(f["path"]).relative_to(f"{edition}/src").with_suffix("").as_posix().replace("/", ".")
        f["module"] = mod
        modules[mod] = f
    edges = {m: list(f["imports"]) for m, f in modules.items()}
    closure, pending = set(), ["Main"]
    while pending:
        m = pending.pop()
        if m in closure or m not in modules:
            continue
        closure.add(m)
        pending.extend(edges[m])
    visiting, visited, cycles = set(), set(), []

    def visit(m: str, stack: list[str]):
        if m in visiting:
            cycles.append(stack[stack.index(m):] + [m])
            return
        if m in visited:
            return
        visiting.add(m)
        for dep in edges[m]:
            if dep in modules:
                visit(dep, stack+[m])
        visiting.remove(m)
        visited.add(m)

    for module in modules:
        visit(module, [])
    by_folder = collections.Counter()
    for f in files:
        first = f["module"].split(".")[0]
        by_folder[first] += 1
    hits = [{"path": f["path"], **hit} for f in files for hit in f["watch_hits"]]
    challenges = inspect_file(repo / edition / "Challenge.lean", repo)
    manifest = json.loads((repo / edition / "lake-manifest.json").read_text())
    return {
        "edition": edition,
        "source_files": len(files),
        "source_files_by_top_module": dict(by_folder),
        "source_lines": sum(f["lines"] for f in files),
        "source_nonblank_lines": sum(f["nonblank_lines"] for f in files),
        "source_nonblank_code_lines_approx": sum(f["nonblank_code_lines"] for f in files),
        "source_declarations_approx": dict(sum((collections.Counter(f["declarations_approx"]) for f in files), collections.Counter())),
        "watch_tokens": list(WATCH_TOKENS),
        "source_watch_hits": hits,
        "source_watch_token_counts": dict(collections.Counter(x["token"] for x in hits)),
        "source_set_options": sorted({x for f in files for x in f["set_options"]}),
        "source_eval_directives": [{"path": f["path"], "line": line} for f in files for line in f["eval_directives"]],
        "main_local_module_import_closure_count": len(closure),
        "main_local_module_import_closure": sorted(closure),
        "source_modules_outside_main_import_closure": sorted(set(modules)-closure),
        "external_imports": sorted({x for deps in edges.values() for x in deps if x not in modules}),
        "challenge_imported_from_source": any("Challenge" in ds for ds in edges.values()),
        "challenge_watch_hits": challenges["watch_hits"],
        "lib_imports_new": [{"module": m, "import": dep} for m, ds in edges.items() if m.startswith("Lib.") for dep in ds if dep.startswith("New.")],
        "module_import_cycles": cycles,
        "lean_toolchain": (repo/edition/"lean-toolchain").read_text().strip(),
        "dependencies": [{k: p.get(k) for k in ("name", "url", "rev")} for p in manifest["packages"]],
        "comparison_config": json.loads((repo/edition/"comparator.json").read_text()),
    }, edges, files


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("repository", type=Path)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    repo = args.repository.resolve()
    args.out.mkdir(parents=True, exist_ok=True)
    summary = {
        "audit_kind": "Static source inventory; NOT Lean compilation or proof verification",
        "repository": "https://github.com/lsernau/grh-lean",
        "commit": git(repo, "rev-parse", "HEAD"),
        "working_tree_status": git(repo, "status", "--porcelain"),
        "validation_performed": ["SHA-256 file inventory", "comment/string-aware token scan", "local module import closure", "main theorem source inspection"],
        "validation_not_performed": ["Lean build", "kernel replay", "#print axioms", "independent checker replay", "declaration-level proof dependency closure"],
        "available_executables": {x: shutil.which(x) for x in ["lean", "lake", "elan", "leanchecker", "leanexport", "nanoda", "con-leche", "con-ron"]},
        "editions": [],
    }
    for edition in ["grh", "grh-compact"]:
        s, graph, inventory = audit_project(repo, edition)
        summary["editions"].append(s)
        (args.out/f"{edition}_imports.json").write_text(json.dumps(graph, indent=2)+"\n")
        (args.out/f"{edition}_source_inventory.json").write_text(json.dumps(inventory, indent=2)+"\n")
    (args.out/"static_audit.json").write_text(json.dumps(summary, indent=2)+"\n")
    print(json.dumps({
        "commit": summary["commit"],
        "audit_kind": summary["audit_kind"],
        "editions": [{k: s[k] for k in ["edition", "source_files", "source_files_by_top_module", "source_lines", "source_nonblank_lines", "source_nonblank_code_lines_approx", "source_declarations_approx", "source_watch_hits", "main_local_module_import_closure_count", "source_modules_outside_main_import_closure", "external_imports", "challenge_imported_from_source", "challenge_watch_hits", "lib_imports_new", "module_import_cycles"]} for s in summary["editions"]]
    }, indent=2))


if __name__ == "__main__":
    main()

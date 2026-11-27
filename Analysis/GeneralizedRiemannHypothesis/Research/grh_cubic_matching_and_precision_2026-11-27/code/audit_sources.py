#!/usr/bin/env python3
"""Reproduce the static provenance/import audit; this is not a Lean kernel check.

Usage:
  python3 code/audit_sources.py /path/to/ProveIt --output provenance/source_static_audit.json
  # Optional independently fetched upstream repository:
  python3 code/audit_sources.py /path/to/ProveIt --upstream-checkout /path/to/grh-lean

The ProveIt checkout must be at the pinned commit. No network is used. Tracked
working files are compared byte-for-byte by Git blob identity. Extra build
products outside src are harmless; untracked Lean source files are reported.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

PROVEIT_COMMIT = "2a9f8e3ee74a1824d57546f0b1b4f1cef5df93d6"
UPSTREAM_COMMIT = "72fead102f663d5c7a407964a13dc0cf9d977207"
VENDOR_PATH = "Analysis/GeneralizedRiemannHypothesis/vendor/grh-lean/grh"
EXPECTED_TREE = "2e133df63d7f4da6b3059c4195324f8e9187ba73"
TOKENS = ("sorry", "admit", "axiom", "constant", "opaque", "unsafe",
          "native_decide", "implemented_by", "sorryAx")


def git(repo: Path, *args: str) -> bytes:
    return subprocess.check_output(["git", "-C", str(repo), *args])


def strip_comments_and_strings(source: str) -> str:
    """Remove nested Lean comments and ordinary strings, preserving newlines.

    This is a lexical audit helper, not a Lean parser or proof checker.
    """
    out, pos, depth, in_string = [], 0, 0, False
    while pos < len(source):
        if depth:
            if source.startswith("/-", pos):
                depth += 1
                out.extend("  ")
                pos += 2
            elif source.startswith("-/", pos):
                depth -= 1
                out.extend("  ")
                pos += 2
            else:
                out.append("\n" if source[pos] == "\n" else " ")
                pos += 1
        elif in_string:
            if source[pos] == "\\" and pos + 1 < len(source):
                out.append(" ")
                out.append("\n" if source[pos + 1] == "\n" else " ")
                pos += 2
            elif source[pos] == '"':
                in_string = False
                out.append(" ")
                pos += 1
            else:
                out.append("\n" if source[pos] == "\n" else " ")
                pos += 1
        elif source.startswith("/-", pos):
            depth = 1
            out.extend("  ")
            pos += 2
        elif source.startswith("--", pos):
            stop = source.find("\n", pos)
            if stop < 0:
                stop = len(source)
            out.extend(" " * (stop - pos))
            pos = stop
        elif source[pos] == '"':
            in_string = True
            out.append(" ")
            pos += 1
        else:
            out.append(source[pos])
            pos += 1
    if depth or in_string:
        raise ValueError("Unterminated comment or ordinary string in lexical audit")
    return "".join(out)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout", type=Path)
    parser.add_argument("--upstream-checkout", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    repo = args.checkout.resolve()
    head = git(repo, "rev-parse", "HEAD").decode().strip()
    if head != PROVEIT_COMMIT:
        raise SystemExit(f"Expected ProveIt commit {PROVEIT_COMMIT}; got {head}")
    tree = git(repo, "rev-parse", f"HEAD:{VENDOR_PATH}").decode().strip()
    if tree != EXPECTED_TREE:
        raise SystemExit(f"Unexpected vendored Git tree: {tree}")
    if args.upstream_checkout:
        upstream_tree = git(args.upstream_checkout.resolve(), "rev-parse",
                            f"{UPSTREAM_COMMIT}:grh").decode().strip()
        if upstream_tree != tree:
            raise SystemExit("Upstream and vendored Git trees differ")
    base = repo / VENDOR_PATH
    entries = []
    for record in git(repo, "ls-tree", "-rz", tree).split(b"\0"):
        if not record:
            continue
        metadata, raw_name = record.split(b"\t", 1)
        mode, kind, oid = metadata.decode().split()
        if kind != "blob":
            raise SystemExit(f"Unexpected non-blob subtree entry: {record!r}")
        name = raw_name.decode()
        data = (base / name).read_bytes()
        computed = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        if computed != oid:
            raise SystemExit(f"Tracked working file differs from pinned source: {name}")
        entries.append((name, data))
    lean = [(name, data) for name, data in entries
            if name.startswith("src/") and name.endswith(".lean")]
    expected_sources = {name[4:] for name, _ in lean}
    observed_sources = {str(path.relative_to(base / "src"))
                        for path in (base / "src").rglob("*.lean")}
    extra_sources = sorted(observed_sources - expected_sources)
    imports, suspicious = {}, []
    pattern = re.compile(r"\b(?:" + "|".join(map(re.escape, TOKENS)) + r")\b")
    for name, data in lean:
        clean = strip_comments_and_strings(data.decode())
        module = name[4:-5].replace("/", ".")
        imports[module] = [item for match in re.finditer(r"^\s*import\s+([^\n]+)", clean, re.M)
                           for item in match.group(1).split()]
        for match in pattern.finditer(clean):
            suspicious.append({"file": name,
                               "line": clean[:match.start()].count("\n") + 1,
                               "token": match.group()})
    closure, external = set(), set()

    def visit(module: str) -> None:
        if module in closure:
            return
        if module not in imports:
            external.add(module)
            return
        closure.add(module)
        for dependency in imports[module]:
            visit(dependency)

    visit("Main")
    manifest = json.loads((base / "lake-manifest.json").read_text())
    mathlib = next(package["rev"] for package in manifest["packages"]
                   if package["name"] == "mathlib")
    result = {
        "audit_kind": "Static source/provenance audit, not a build or kernel replay",
        "proveit_commit": head, "vendor_relative_path": VENDOR_PATH,
        "upstream_repository": "lsernau/grh-lean", "upstream_commit": UPSTREAM_COMMIT,
        "vendor_git_tree": tree, "upstream_git_tree": EXPECTED_TREE,
        "upstream_tree_evidence": "GitHub Git trees API independently read during this research",
        "upstream_local_tree_rechecked": args.upstream_checkout is not None,
        "all_tracked_working_files_match_git_blobs": True,
        "tracked_files": len(entries), "src_lean_files": len(lean),
        "main_transitive_local_modules": len(closure),
        "outside_imports": sorted(external),
        "challenge_imported": "Challenge" in external or "Challenge" in closure,
        "untracked_lean_sources": extra_sources,
        "searched_code_tokens": list(TOKENS), "suspicious_code_tokens": suspicious,
        "lean_toolchain": (base / "lean-toolchain").read_text().strip(),
        "mathlib_commit": mathlib, "transitive_modules": sorted(closure),
    }
    rendered = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered)
        print(json.dumps({key: value for key, value in result.items()
                          if key != "transitive_modules"}, indent=2))
    else:
        print(rendered, end="")
    if extra_sources or suspicious:
        raise SystemExit(1)


if __name__ == "__main__":
    main()

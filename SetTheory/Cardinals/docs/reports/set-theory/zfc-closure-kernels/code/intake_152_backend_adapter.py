#!/usr/bin/env python3
"""Run intake 152 sources 32--34 with only their bulk manifests skipped.

The delivered sources are never changed.  Patches are selected by source number,
relative filename and exact AST shape.  No arbitrary digest assertion is removed.
In particular, engineering/reproduce.py is unchanged, including both published
table controls.  All generated-artifact comparisons, quotient equations and
whole-tape boot checks remain active.  Assertions must remain enabled.

Example (run with the recovered package as the current directory):
  python3 intake_152_backend_adapter.py --source 32 --root PACKAGE \
    --script verify_package.py
  python3 intake_152_backend_adapter.py --source 32 --root PACKAGE \
    --script optimization/reproduce.py -- --record /tmp/replay.json

Python child scripts within PACKAGE are routed through this same worker;
``python -m`` commands and non-Python commands are left alone.  The worker does
not compile Lean or Coq unless the caller explicitly chooses such a script.
"""

from __future__ import annotations

import argparse
import ast
import json
import os
from pathlib import Path
import subprocess
import sys


SKIPPED = "Skipped by the intake review: bulk checksum/size manifest only."


def _dump(node: ast.AST) -> str:
    return ast.unparse(node)


def adapt_source(source: int, relative: str, text: str) -> tuple[ast.Module, list[str]]:
    """Return a file-specific AST and a record of its narrowly scoped changes."""
    key = source, Path(relative).as_posix()
    tree = ast.parse(text, filename=relative)
    changes: list[str] = []
    seen: dict[str, int] = {}

    def record(node: ast.AST, label: str, replacement: ast.AST) -> ast.AST:
        seen[label] = seen.get(label, 0) + 1
        changes.append(f"{relative}:{node.lineno}: {label}")
        return ast.copy_location(replacement, node)

    class Adapter(ast.NodeTransformer):
        def visit_For(self, node: ast.For):
            iterator = _dump(node.iter)
            skip = (
                key == (32, "verify_package.py")
                and iterator in ("manifest['files']", "coq['files']")
            ) or (
                key == (32, "optimization/reproduce.py")
                and iterator == "manifest['files']"
            ) or (
                key == (33, "reproduce.py") and iterator == "upstream"
            ) or (
                key == (34, "verify_artifacts.py")
                and iterator == "manifest['files']"
            )
            if skip:
                return record(node, "skip " + iterator, ast.Pass())
            if key == (32, "verify_package.py") and iterator == "lean['modules']":
                # Keep the recorded build-return-code check, remove file hashes.
                expected = [stmt for stmt in node.body if isinstance(stmt, ast.Expr)
                            and isinstance(stmt.value, ast.Call)
                            and isinstance(stmt.value.func, ast.Name)
                            and stmt.value.func.id == "require"
                            and "returncode" in _dump(stmt.value.args[0])]
                if len(expected) != 1:
                    raise ValueError("Recorded Lean return-code check changed")
                node.body = expected
                record(node, "skip Lean source-identity checks; retain return codes", node)
                return node
            return self.generic_visit(node)

        def visit_Expr(self, node: ast.Expr):
            call = node.value
            if key == (32, "verify_package.py") and isinstance(call, ast.Call):
                if (isinstance(call.func, ast.Name) and call.func.id == "require"
                        and call.args
                        and _dump(call.args[0]) == "total == coq['total_bytes']"):
                    return record(node, "skip manifest byte-total check", ast.Pass())
            if isinstance(call, ast.Call) and isinstance(call.func, ast.Name) and call.func.id == "print" and call.args:
                first = call.args[0]
                rendered = _dump(first)
                replacements = {
                    (32, "verify_package.py"): (
                        ("Package manifest:", "SKIPPED: package size/checksum manifest."),
                        ("Coq inspection closure:", "SKIPPED: Coq source size/checksum manifest; no kernel run."),
                        ("Lean evidence:", "SKIPPED: Lean source identities; recorded return codes retained."),
                        ("PASS: package integrity,", "PASS: finite machine audit; bulk manifests were skipped."),
                    ),
                    (34, "verify_artifacts.py"): (
                        ("delivered file sizes and SHA-256 hashes", "SKIPPED: delivered size/checksum manifest."),
                    ),
                }
                for old, new in replacements.get(key, ()):
                    if old in rendered:
                        call.args[0] = ast.Constant(new)
                        return record(node, "report skipped manifest status", node)
            if key == (33, "reproduce.py") and isinstance(call, ast.Call):
                if (isinstance(call.func, ast.Attribute) and isinstance(call.func.value, ast.Name)
                        and call.func.value.id == "stages" and call.func.attr == "append"
                        and call.args and isinstance(call.args[0], ast.Dict)):
                    item = call.args[0]
                    fields = {k.value: v for k, v in zip(item.keys, item.values)
                              if isinstance(k, ast.Constant)}
                    if isinstance(fields.get("name"), ast.Constant) and fields["name"].value == "compiler_dependency_hashes":
                        call.args[0] = ast.parse(repr({"name": "compiler_dependency_hashes",
                            "skipped": True, "reason": SKIPPED}), mode="eval").body
                        return record(node, "report skipped dependency manifest", node)
            return self.generic_visit(node)

        def visit_Dict(self, node: ast.Dict):
            if key == (32, "optimization/reproduce.py"):
                for index, field in enumerate(node.keys):
                    if isinstance(field, ast.Constant) and field.value == "source_manifest_files_verified":
                        node.values[index] = ast.parse(repr({"skipped": True, "reason": SKIPPED}), mode="eval").body
                        record(node, "report skipped source manifest", node)
            return self.generic_visit(node)

    tree = Adapter().visit(tree)
    expected = {
        (32, "verify_package.py"): {
            "skip manifest['files']": 2, "skip coq['files']": 1,
            "skip Lean source-identity checks; retain return codes": 1,
            "skip manifest byte-total check": 1, "report skipped manifest status": 4,
        },
        (32, "optimization/reproduce.py"): {
            "skip manifest['files']": 1, "report skipped source manifest": 1,
        },
        (33, "reproduce.py"): {
            "skip upstream": 1, "report skipped dependency manifest": 1,
        },
        (34, "verify_artifacts.py"): {
            "skip manifest['files']": 1, "report skipped manifest status": 1,
        },
    }.get(key, {})
    if seen != expected:
        raise ValueError(f"Unexpected manifest adapter anchors in {key}: {seen}; expected {expected}")
    return ast.fix_missing_locations(tree), changes


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=int, choices=(32, 33, 34), required=True)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--script", type=Path, required=True)
    parser.add_argument("arguments", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    if not __debug__:
        parser.error("Assertions must remain enabled")
    root = args.root.resolve()
    target = (root / args.script).resolve()
    if not target.is_relative_to(root) or not target.is_file():
        parser.error("The script must be a file inside the recovered package")
    relative = target.relative_to(root).as_posix()
    forwarded = args.arguments[1:] if args.arguments[:1] == ["--"] else args.arguments
    worker = Path(__file__).resolve()
    original_popen = subprocess.Popen

    class RoutedPopen(original_popen):
        def __init__(self, command, *positional, **keywords):
            if isinstance(command, (list, tuple)) and command and Path(str(command[0])).name.startswith("python"):
                command = list(map(str, command))
                index = 1
                while index < len(command) and command[index].startswith("-") and command[index] != "-m":
                    index += 1
                if index < len(command) and command[index] != "-m":
                    child = Path(command[index])
                    if not child.is_absolute():
                        child = Path(keywords.get("cwd") or os.getcwd()) / child
                    child = child.resolve()
                    if child.is_file() and child.is_relative_to(root):
                        command = [command[0], "-B", str(worker), "--source", str(args.source),
                                   "--root", str(root), "--script", str(child), "--", *command[index + 1:]]
            super().__init__(command, *positional, **keywords)

    subprocess.Popen = RoutedPopen
    # The original source32 audit checked this regenerated summary only via a
    # release-manifest digest.  Preserve its functional identity directly.
    outputs = [root / "machine_audit/audit_summary.json"] if (args.source, relative) == (32, "verify_package.py") else []
    before = {path: path.read_bytes() for path in outputs}
    tree, changes = adapt_source(args.source, relative, target.read_text())
    sys.argv = [str(target), *forwarded]
    sys.path.insert(0, str(target.parent))
    sys.dont_write_bytecode = True
    namespace = {"__name__": "__main__", "__file__": str(target), "__package__": None, "__cached__": None}
    try:
        exec(compile(tree, str(target), "exec"), namespace)
        for path, data in before.items():
            if path.read_bytes() != data:
                raise AssertionError(f"Regenerated functional output changed: {path}")
    finally:
        if changes:
            print("INTAKE_MANIFEST_ADAPTER " + json.dumps({"source": args.source,
                "script": relative, "changes": changes,
                "functional_digest_assertions_preserved": True}), file=sys.stderr)


if __name__ == "__main__":
    main()

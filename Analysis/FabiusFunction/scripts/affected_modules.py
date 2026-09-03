#!/usr/bin/env python3
"""List the modules a change set can break, in dependency order.

After a wave of edits the question that matters is *did anything I changed
break anything downstream of it*, not *does the whole corpus still compile*.
Those differ by the several hundred untouched modules that make a full facade
build an overnight job on this machine, and only the first is answerable in a
reasonable time.  See the "Lake's job counter is not progress, and the facade
is not the gate" section of ``Analysis/FabiusFunction/AGENTS.md``.

This script computes, from the ``import FabiusFunction.*`` graph:

* the modules changed between a base commit and ``HEAD``;
* the closure of those under *reverse* imports, i.e. everything that could
  observe the change; and
* a topological order for that closure, so a driver can build one module per
  ``lake`` invocation with every dependency already compiled and nothing for
  Lake to fan out over.

Run from anywhere::

    python3 Analysis/FabiusFunction/scripts/affected_modules.py <base-commit>
    python3 Analysis/FabiusFunction/scripts/affected_modules.py <base> --out list.txt
    python3 Analysis/FabiusFunction/scripts/affected_modules.py <base> --stats

The companion driver ``validate_affected.sh`` consumes the ``--out`` file.
Exit status is 0 unless the repository cannot be read.
"""

from __future__ import annotations

import argparse
import io
import os
import re
import subprocess
import sys

REPO_SUBDIR = os.path.join("Analysis", "FabiusFunction", "Lean", "FabiusFunction")
IMPORT_RE = re.compile(r"^import FabiusFunction\.([A-Za-z0-9_']+)", re.M)


def repo_root() -> str:
    """The git top level containing this script."""
    here = os.path.dirname(os.path.abspath(__file__))
    out = subprocess.run(
        ["git", "-C", here, "rev-parse", "--show-toplevel"],
        capture_output=True, text=True, check=True)
    return out.stdout.strip()


def changed_modules(root: str, base: str) -> set[str]:
    """Module names whose sources differ between ``base`` and ``HEAD``."""
    out = subprocess.run(
        ["git", "-C", root, "diff", "--name-only", base, "HEAD", "--",
         REPO_SUBDIR.replace(os.sep, "/")],
        capture_output=True, text=True, check=True)
    names = set()
    for line in out.stdout.splitlines():
        if line.endswith(".lean"):
            names.add(os.path.basename(line)[:-5])
    return names


def import_graph(lean_dir: str) -> dict[str, set[str]]:
    """``module -> set of FabiusFunction modules it imports``."""
    graph: dict[str, set[str]] = {}
    for fn in sorted(os.listdir(lean_dir)):
        if not fn.endswith(".lean"):
            continue
        text = io.open(os.path.join(lean_dir, fn), encoding="utf-8",
                       errors="replace").read()
        graph[fn[:-5]] = set(IMPORT_RE.findall(text))
    return graph


def reverse_closure(graph: dict[str, set[str]], seed: set[str]) -> set[str]:
    """Everything reachable from ``seed`` along reverse import edges."""
    rev: dict[str, set[str]] = {m: set() for m in graph}
    for mod, deps in graph.items():
        for dep in deps:
            if dep in rev:
                rev[dep].add(mod)
    seen = {m for m in seed if m in graph}
    stack = list(seen)
    while stack:
        mod = stack.pop()
        for consumer in rev.get(mod, ()):
            if consumer not in seen:
                seen.add(consumer)
                stack.append(consumer)
    return seen


def topological(graph: dict[str, set[str]], subset: set[str]) -> list[str]:
    """Depth-first topological order of ``subset``, dependencies first."""
    order: list[str] = []
    mark: dict[str, int] = {}

    def visit(mod: str) -> None:
        if mark.get(mod) == 2:
            return
        mark[mod] = 1
        for dep in sorted(graph.get(mod, ())):
            if dep in subset and mark.get(dep) != 2:
                visit(dep)
        mark[mod] = 2
        order.append(mod)

    for mod in sorted(subset):
        visit(mod)
    return order


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("base", help="base commit to diff HEAD against")
    parser.add_argument("--out", help="write the topological order here")
    parser.add_argument("--stats", action="store_true",
                        help="also report how many lack a built olean")
    args = parser.parse_args()

    root = repo_root()
    lean_dir = os.path.join(root, REPO_SUBDIR)
    graph = import_graph(lean_dir)
    seed = changed_modules(root, args.base)
    present = {m for m in seed if m in graph}
    affected = reverse_closure(graph, present)
    order = topological(graph, affected)

    print(f"changed modules (still present) : {len(present)}")
    print(f"changed + transitive dependents : {len(order)}")

    if args.stats:
        build = os.path.join(root, ".lake", "build", "lib", "lean",
                             "FabiusFunction")
        missing = [m for m in order
                   if not os.path.exists(os.path.join(build, m + ".olean"))]
        print(f"of those, missing an olean     : {len(missing)}")

    if args.out:
        io.open(args.out, "w", encoding="utf-8", newline="\n").write(
            "\n".join(order) + "\n")
        print(f"wrote {args.out}")
    else:
        for mod in order:
            print(mod)
    return 0


if __name__ == "__main__":
    sys.exit(main())

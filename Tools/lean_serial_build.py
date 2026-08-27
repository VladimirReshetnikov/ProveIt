#!/usr/bin/env python3
"""Serial topological Lake driver: one Lean process at a time.

Why this exists
---------------
On a memory-constrained machine each ``lean.exe`` worker on a Mathlib-importing
file holds 1-1.5 GB, so a default parallel ``lake build`` exhausts RAM and then
fails with *misleading* errors of the form ::

    error: failed to read file '...\\Mathlib\\...\\Basic.olean'

which are swap-thrash symptoms, not corruption: the same module compiles on a
serial retry.  ``lake build -j1`` is not a workaround -- Lake 5.0.0 removed the
``-j`` flag and the invocation fails *with exit code 0* -- and neither is
``LAKE_JOBS=1``.  Even a single target parallelizes its own stale dependency
chain, so the only reliable serialization is one ``lake build`` invocation per
module, in topological order, with every dependency already built.

Usage
-----
::

    python Tools/lean_serial_build.py FabiusFunction
    python Tools/lean_serial_build.py FabiusFunction --from ThueMorseMoments
    python Tools/lean_serial_build.py PolynomialFormulas --srcdir Algebra/PolynomialFormulas/Lean

The library's source directory is guessed from ``lakefile.toml`` when possible;
pass ``--srcdir`` if the guess is wrong.  Run it in the background and watch the
log; a large library takes hours.
"""
from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
import time

IMPORT_RE = re.compile(r"^import\s+([A-Za-z0-9_.]+)\s*$")
TRANSIENT = "failed to read file"


def find_srcdir(root: str, lib: str) -> str:
    """Read lakefile.toml for the srcDir of ``lib``; default to the root."""
    path = os.path.join(root, "lakefile.toml")
    if not os.path.exists(path):
        return root
    name, srcdir = None, None
    with open(path, encoding="utf-8") as fh:
        for line in fh:
            line = line.strip()
            if line.startswith("name ="):
                name = line.split("=", 1)[1].strip().strip('"')
                srcdir = None
            elif line.startswith("srcDir ="):
                srcdir = line.split("=", 1)[1].strip().strip('"')
            if name == lib and srcdir is not None:
                return os.path.join(root, srcdir.replace("/", os.sep))
    return root


def read_deps(libdir: str, lib: str) -> dict[str, list[str]]:
    """Map each module of ``lib`` to its in-library imports."""
    deps: dict[str, list[str]] = {}
    prefix = lib + "."
    for entry in sorted(os.listdir(libdir)):
        if not entry.endswith(".lean"):
            continue
        module = entry[:-5]
        deps[module] = []
        with open(os.path.join(libdir, entry), encoding="utf-8") as fh:
            for line in fh:
                m = IMPORT_RE.match(line)
                if m and m.group(1).startswith(prefix):
                    deps[module].append(m.group(1)[len(prefix):])
    return deps


def toposort(deps: dict[str, list[str]]) -> list[str]:
    order: list[str] = []
    seen: set[str] = set()

    def visit(m: str) -> None:
        if m in seen or m not in deps:
            return
        seen.add(m)
        for d in deps[m]:
            visit(d)
        order.append(m)

    for m in sorted(deps):
        visit(m)
    return order


def build(root: str, target: str, retries: int, pause: float) -> str:
    """Return 'ok', 'fail' or 'giveup'; print diagnostics on failure."""
    for attempt in range(retries):
        proc = subprocess.run(
            ["lake", "build", "+" + target], cwd=root,
            capture_output=True, text=True, encoding="utf-8", errors="replace")
        out = (proc.stdout or "") + (proc.stderr or "")
        errors = [ln for ln in out.splitlines() if "error:" in ln]
        if not errors:
            return "ok"
        if any(TRANSIENT in e for e in errors):
            print(f"    transient (attempt {attempt + 1}); pausing {pause:.0f}s",
                  flush=True)
            time.sleep(pause)
            continue
        for line in errors[:8]:
            print("    " + line[:400], flush=True)
        return "fail"
    return "giveup"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("library", help="Lake library name, e.g. FabiusFunction")
    ap.add_argument("--root", default=os.getcwd(), help="repository root")
    ap.add_argument("--srcdir", default=None, help="override the source dir")
    ap.add_argument("--from", dest="start", default=None,
                    help="resume at this module (skip everything before it)")
    ap.add_argument("--retries", type=int, default=6,
                    help="attempts per module on the transient olean error")
    ap.add_argument("--pause", type=float, default=45.0,
                    help="seconds to wait between transient retries")
    args = ap.parse_args()

    root = os.path.abspath(args.root)
    libdir = args.srcdir or find_srcdir(root, args.library)
    libdir = os.path.join(libdir, args.library) if os.path.isdir(
        os.path.join(libdir, args.library)) else libdir
    if not os.path.isdir(libdir):
        print(f"no such source directory: {libdir}", file=sys.stderr)
        return 2

    deps = read_deps(libdir, args.library)
    order = toposort(deps)
    if args.start:
        if args.start not in order:
            print(f"--from {args.start}: not a module of {args.library}",
                  file=sys.stderr)
            return 2
        order = order[order.index(args.start):]

    print(f"{args.library}: {len(order)} modules, one Lean process at a time",
          flush=True)
    failed: list[str] = []
    for i, module in enumerate(order, 1):
        target = f"{args.library}.{module}"
        status = build(root, target, args.retries, args.pause)
        print(f"[{i}/{len(order)}] {status} {module}", flush=True)
        if status != "ok":
            failed.append(module)

    print("FAILED: " + (", ".join(failed) if failed else "(none)"), flush=True)
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())

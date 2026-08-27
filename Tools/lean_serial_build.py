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
``-j`` flag and rejects ``--jobs`` too -- so the worker limits have to be set
in the environment, and this driver sets both: ``LAKE_JOBS=1`` bounds how many
``lean.exe`` *processes* Lake starts, ``LEAN_NUM_THREADS=0`` bounds the worker
pool *inside* each one.

Both of those, plus one ``lake build`` invocation per module in topological
order with every dependency already built.  Belt and braces: the per-module
walk is what makes the peak memory predictable, and the environment limits are
what keep a single invocation from fanning out when its dependency chain turns
out to be stale.

A note on measuring this, because it is easy to conclude that ``LAKE_JOBS``
does nothing: several agent sessions build in this repository at once, so
``Get-Process lean`` counts *their* workers alongside yours.  Attribute by
parent process before drawing conclusions --

    Get-CimInstance Win32_Process -Filter "Name='lean.exe'" |
      Select-Object ProcessId, ParentProcessId, CommandLine

Measured 2026-08-27: a facade build with a stale dependency chain ran 11
concurrent ``lean.exe`` with no limits set, and exactly one of its own under
``LAKE_JOBS=1`` (a second worker seen machine-wide traced back to a ``lake.exe``
belonging to a different session).

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


def serial_env() -> dict:
    """The environment that keeps one `lake build` to a single Lean worker.

    `LAKE_JOBS` bounds how many `lean.exe` processes Lake starts;
    `LEAN_NUM_THREADS` bounds the worker pool inside each one.  They are
    independent, so both are set.  Lake 5.0.0 has no command-line equivalent.
    """
    env = dict(os.environ)
    env["LAKE_JOBS"] = "1"
    env["LEAN_NUM_THREADS"] = "0"
    return env


def build(root: str, target: str, retries: int, pause: float) -> str:
    """Return 'ok', 'fail' or 'giveup'; print diagnostics on failure."""
    env = serial_env()
    for attempt in range(retries):
        proc = subprocess.run(
            ["lake", "build", "+" + target], cwd=root, env=env,
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

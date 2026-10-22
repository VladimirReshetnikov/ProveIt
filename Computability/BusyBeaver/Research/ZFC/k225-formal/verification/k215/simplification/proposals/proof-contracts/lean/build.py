#!/usr/bin/env python3
"""Fresh, serial Lean build of the self-contained semantic coverage proposal.

No network, Lake, mathlib, precompiled objects, or native_decide is used.
Usage: python3 build.py --lean /path/to/lean --out /path/to/fresh-build
"""
from __future__ import annotations

import argparse
from contextlib import contextmanager
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
SRC = ROOT / "src"
TARGETS = [
    "BusyBeaver.ZFC.KSimCompatibility",
    "BusyBeaver.ZFC.KDecoderSuffix215Example",
]


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


@contextmanager
def build_lock(path: Path):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a+b") as stream:
        if os.name == "nt":
            import msvcrt
            if stream.tell() == 0:
                stream.write(b"0")
                stream.flush()
            stream.seek(0)
            msvcrt.locking(stream.fileno(), msvcrt.LK_LOCK, 1)
            try:
                yield
            finally:
                stream.seek(0)
                msvcrt.locking(stream.fileno(), msvcrt.LK_UNLCK, 1)
        else:
            import fcntl
            fcntl.flock(stream, fcntl.LOCK_EX)
            try:
                yield
            finally:
                fcntl.flock(stream, fcntl.LOCK_UN)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--lean", required=True, help="Lean 4.32.0 compiler executable")
    ap.add_argument("--out", required=True, type=Path, help="Separate build output directory")
    ap.add_argument("--lock", type=Path,
                    default=Path(os.environ.get("TEMP", "/tmp")) / "proveit-k215-proof-build.lock")
    args = ap.parse_args()
    out = args.out.resolve()
    if out == SRC or SRC in out.parents:
        ap.error("Build output must be outside src/.")
    out.mkdir(parents=True, exist_ok=True)
    (out / "logs").mkdir(exist_ok=True)
    order: list[tuple[str, Path]] = []
    seen: set[str] = set()
    active: set[str] = set()

    def visit(name: str):
        if name in active:
            raise ValueError(f"Import cycle through {name}")
        if name in seen:
            return
        source = SRC.joinpath(*name.split(".")).with_suffix(".lean")
        if not source.exists():
            if name in ("Init", "Std", "Lean"):
                return
            raise FileNotFoundError(f"Unresolved project import: {name}")
        active.add(name)
        for line in source.read_text().splitlines():
            if line.startswith("import "):
                for dependency in line.split()[1:]:
                    visit(dependency)
        active.remove(name)
        seen.add(name)
        order.append((name, source))

    for target in TARGETS:
        visit(target)
    env = dict(os.environ, LEAN_PATH=str(out))
    receipt = {"targets": TARGETS, "fresh_compilation": True, "modules": [],
               "all_passed": False, "full_K215_endpoint_rebuilt": False}
    with build_lock(args.lock):
        version = subprocess.run([args.lean, "--version"], text=True,
                                 capture_output=True, check=True).stdout.strip()
        receipt["lean"] = version
        if "version 4.32.0," not in version:
            raise RuntimeError("This pinned proposal requires Lean 4.32.0; found " + version)
        for name, source in order:
            obj = out.joinpath(*name.split(".")).with_suffix(".olean")
            obj.parent.mkdir(parents=True, exist_ok=True)
            command = [args.lean, "-o", str(obj), str(source.relative_to(SRC))]
            start = time.monotonic()
            completed = subprocess.run(command, cwd=SRC, env=env, text=True,
                                       capture_output=True)
            elapsed = time.monotonic() - start
            log = out / "logs" / (name + ".log")
            output = completed.stdout + completed.stderr
            log.write_text(output)
            allowed = {"propext", "Classical.choice", "Quot.sound"}
            audits = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output)
            unexpected = sorted({a.strip() for _, names in audits for a in names.split(",")
                                 if a.strip() and a.strip() not in allowed})
            entry = {
                "module": name,
                "source": str(source.relative_to(ROOT)),
                "source_sha256": sha(source),
                "exit_code": completed.returncode,
                "seconds": elapsed,
                "log": str(log.relative_to(out)),
                "log_sha256": sha(log),
                "unexpected_axioms": unexpected,
            }
            receipt["modules"].append(entry)
            print(f"{name}: exit {completed.returncode}, {elapsed:.3f}s", flush=True)
            if completed.returncode != 0 or unexpected:
                print(output, flush=True)
                break
        receipt["all_passed"] = (
            len(receipt["modules"]) == len(order)
            and all(m["exit_code"] == 0 and not m["unexpected_axioms"]
                    for m in receipt["modules"])
        )
    (out / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    return 0 if receipt["all_passed"] else 1


if __name__ == "__main__":
    sys.exit(main())

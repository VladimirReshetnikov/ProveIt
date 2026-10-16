"""Recover batch 143 to isolated scratch directories and run its Python suites."""
from __future__ import annotations

import argparse
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
from zipfile import ZipFile

ARRIVAL = "9e5b610259cd42c88e2cf6c862fb876a7c6d6fcd"
ARCHIVES = (
    "zfc_closure_research.zip",
    "zfc_closure_research (1).zip",
    "zfc_exact_fiber_hulls.zip",
)
COMMANDS = (
    (
        ("-m", "unittest", "discover", "-s", "code", "-v"),
        ("code/graph_audit.py",),
        ("code/bic.py", "--metrics"),
        ("code/bic.py", "examples/identity.json"),
    ),
    (("build.py", "--tests", "--skip-pdf"),),
    (("code/hull_templates.py",), ("code/finite_hulls.py",), ("code/test_templates.py",)),
)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prepare-only", action="store_true")
    args = parser.parse_args()
    repo = next(p for p in Path(__file__).resolve().parents if (p / ".git").exists())
    scratch = Path(tempfile.mkdtemp(prefix="zfc-closure-reproduce-"))
    results = []
    for number, (archive, commands) in enumerate(zip(ARCHIVES, COMMANDS), 1):
        raw = subprocess.check_output(
            ["git", "show", f"{ARRIVAL}:docs/incoming/{archive}"], cwd=repo
        )
        dest = scratch / f"{number:02d}" / Path(archive).stem
        with ZipFile(io.BytesIO(raw)) as package:
            for name in package.namelist():
                if Path(name).is_absolute() or ".." in Path(name).parts:
                    raise ValueError(f"Unsafe archive path: {name}")
            package.extractall(dest)
        root = next(p.parent for p in dest.rglob("build.py"))
        print(f"{number:02d}: {root}", flush=True)
        if args.prepare_only:
            continue
        for index, command in enumerate(commands, 1):
            run = subprocess.run(
                [sys.executable, *command], cwd=root, text=True, capture_output=True
            )
            log = scratch / f"{number:02d}-{index:02d}.log"
            log.write_text(run.stdout + run.stderr)
            results.append({"source": number, "command": list(command),
                            "returncode": run.returncode, "log": str(log)})
            print(f"  {' '.join(command)}: exit {run.returncode}", flush=True)
            if run.returncode:
                print(run.stdout + run.stderr, file=sys.stderr)
                raise SystemExit(run.returncode)
    (scratch / "reproduction.json").write_text(json.dumps(results, indent=2) + "\n")
    print(f"Evidence retained in {scratch}")


if __name__ == "__main__":
    main()

"""Recover batch145 outside the checkout and replay its finite Python checks.

No network is required. Release checksum manifests are excluded by the intake
procedure; pinned executable inputs and exact regenerated outputs retain the
delivered programs' own checks. PDF and Lean compilation are separate steps.
"""
from __future__ import annotations

import argparse
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
from zipfile import ZipFile


ARRIVALS = (
    ("9c98495586c2a3b49e76ccb0d4e29cebc824903b", "zfc_small_machine_research.zip"),
    ("96836f9eea3540e96322c3d28c7127a582aae223", "zfc_small_machines_20261016.zip"),
)


def main() -> None:
    if not __debug__:
        raise SystemExit("Run without -O/PYTHONOPTIMIZE: delivered checks use assertions.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prepare-only", action="store_true")
    parser.add_argument("--sources", type=int, choices=(1, 2), nargs="+", default=[1, 2])
    parser.add_argument("--searches", action="store_true",
                        help="repeat source01's 288- and 9,216-choice bounded searches")
    args = parser.parse_args()
    repo = next(p for p in Path(__file__).resolve().parents if (p / ".git").exists())
    scratch = Path(tempfile.mkdtemp(prefix="zfc-batch145-reproduce-"))
    records = []
    print(f"Scratch: {scratch}", flush=True)

    def run(number: int, root: Path, command: list[str]) -> None:
        result = subprocess.run([sys.executable, *map(str, command)], cwd=root,
                                capture_output=True, text=True)
        log = scratch / f"{number:02d}-{len(records) + 1:02d}.log"
        log.write_text(result.stdout + result.stderr)
        records.append(dict(source=number, command=list(map(str, command)),
                            returncode=result.returncode, log=str(log)))
        (scratch / "runs.json").write_text(json.dumps(records, indent=2) + "\n")
        print(f"{number:02d}: {command[0]} exit {result.returncode}", flush=True)
        if result.returncode:
            print(result.stdout + result.stderr, file=sys.stderr)
            raise SystemExit(result.returncode)

    for number in args.sources:
        arrival, archive = ARRIVALS[number - 1]
        dest = scratch / f"{number:02d}"
        raw = subprocess.check_output(["git", "show", f"{arrival}:docs/incoming/{archive}"],
                                      cwd=repo)
        with ZipFile(io.BytesIO(raw)) as zipped:
            for name in zipped.namelist():
                path = Path(name)
                if path.is_absolute() or ".." in path.parts:
                    raise ValueError(f"Archive path escapes scratch directory: {name}")
            zipped.extractall(dest)
        roots = [p for p in dest.iterdir() if p.is_dir()]
        if len(roots) != 1:
            raise ValueError(f"Expected one package root for source {number}")
        root = roots[0]
        print(f"{number:02d}: {root}", flush=True)

        if number == 1:
            # Recover executable inputs from the recorded Git pin, rather than
            # making the delivered downloader depend on a live public server.
            machine = root / "machine"
            manifest = json.loads((machine / "source-manifest.json").read_text())
            for item in manifest["files"]:
                path = Path(item["path"])
                if path.is_absolute() or ".." in path.parts:
                    raise ValueError(f"Pinned source path escapes scratch: {path}")
                target = machine / "repo" / path
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(subprocess.check_output(
                    ["git", "show", f"{manifest['commit']}:{path.as_posix()}"], cwd=repo))
            if args.prepare_only:
                continue
            run(number, root, ["code/logical_kernel_diagnostic.py", "--output",
                               str(scratch / "source10-logical.json")])
            run(number, root, ["code/base3_codec.py"])
            extra = ["--search-orders", "--search-conjunctions"] if args.searches else []
            run(number, machine, ["reproduce.py", "--offline", *extra])
            run(number, machine, ["translation_comparator.py"])
        else:
            if args.prepare_only:
                continue
            # Run the delivered entry point without its release-manifest check.
            # This changes one in-memory binding, never the recovered source.
            program = (
                "import runpy,sys; "
                "ns=runpy.run_path('reproduce.py',run_name='intake_reproduce_145'); "
                "main=ns['main']; main.__globals__['manifest_check']=lambda:0; "
                "sys.argv=['reproduce.py','--output',sys.argv[1]]; "
                "raise SystemExit(main())"
            )
            run(number, root, ["-c", program, str(scratch / "source11-reproduction.json")])
            auditor = root / "vendor/ProveIt/Computability/BusyBeaver/Research/ZFC/audit_tm.py"
            for variant in ("old_rho6", "dual_rho6"):
                extra = ["--self-test"] if variant == "old_rho6" else []
                run(number, root, [str(auditor), f"machines/raw-candidate-{variant}-248.tm",
                                   "--expected-states", "248", "--expected-halt", "248",
                                   "--window-radius", "4", "--macro-steps", "64",
                                   "--trace-steps", "1000000", *extra, "--output",
                                   str(scratch / f"source11-{variant}-audit.json")])


if __name__ == "__main__":
    main()

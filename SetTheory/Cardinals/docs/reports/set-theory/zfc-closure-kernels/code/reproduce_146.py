"""Recover batch 146 from Git and run finite checks outside the checkout.

No network or proof assistant is used. Delivered checksum-manifest checks are
excluded; compiler pin contracts and exact generated-table comparisons remain.
Each source runs in a separate Python process with its original package layout.
"""
from __future__ import annotations

import argparse
import io
import json
from pathlib import Path
import subprocess
import sys
import tarfile
import tempfile
from zipfile import ZipFile


ARRIVALS = (
    ("47f3a36029", "zfc_consistency_machine_research.zip"),
    ("47f3a36029", "zfc_consistency_proposal.zip"),
    ("af518abcf8", "zfc_empty_seed_research.zip"),
    ("af518abcf8", "zfc_small_machine_proposal.zip"),
)
PIN = "83dec60c249ca0f9e1b2e5ee3cf18fd1ce58c373"
DEPENDENCIES = (
    "Computability/BusyBeaver/Research/ZFC",
    "lib/jeff-busy-beaver-zfc254/ZF/generator",
    "lib/jeff-busy-beaver-zfc254/ZF/m254/coq/prog/Dag254.v",
    "lib/jeff-busy-beaver-zfc254/ZF/m254/tools/logic/spec.py",
)


def main() -> None:
    if not __debug__:
        raise SystemExit("Run without -O/PYTHONOPTIMIZE: delivered checks use assertions.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prepare-only", action="store_true")
    parser.add_argument("--sources", type=int, choices=range(1, 5), nargs="+",
                        default=[1, 2, 3, 4])
    parser.add_argument("--searches", action="store_true",
                        help="also repeat source 01's 288 and source 03's bounded searches")
    args = parser.parse_args()
    repo = next(p for p in Path(__file__).resolve().parents if (p / ".git").exists())
    scratch = Path(tempfile.mkdtemp(prefix="zfc-batch146-reproduce-"))
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

    dependencies = scratch / "pinned-repo"
    raw = subprocess.check_output(["git", "archive", PIN, *DEPENDENCIES], cwd=repo)
    with tarfile.open(fileobj=io.BytesIO(raw)) as archived:
        archived.extractall(dependencies, filter="data")

    for number in args.sources:
        arrival, archive = ARRIVALS[number - 1]
        dest = scratch / f"{number:02d}"
        raw = subprocess.check_output(["git", "show", f"{arrival}:docs/incoming/{archive}"],
                                      cwd=repo)
        with ZipFile(io.BytesIO(raw)) as zipped:
            for name in zipped.namelist():
                path = Path(name)
                if path.is_absolute() or ".." in path.parts:
                    raise ValueError(f"Archive path escapes scratch: {name}")
            zipped.extractall(dest)
        roots = [p for p in dest.iterdir() if p.is_dir()]
        if len(roots) != 1:
            raise ValueError(f"Expected one package root for source {number}")
        root = roots[0]
        print(f"{number:02d}: {root}", flush=True)
        if args.prepare_only:
            continue

        if number == 1:
            # Disable only the source-manifest audit, in memory. Clearing its
            # list also makes the delivered result accurately report zero.
            program = (
                "import runpy,sys; "
                "ns=runpy.run_path('verify.py',run_name='intake_146'); "
                "main=ns['main']; "
                "main.__globals__['source_hashes']=lambda root,m:m['files'].clear(); "
                "sys.argv=['verify.py','--root','.',*sys.argv[1:]]; main()"
            )
            extra = ["--full"] if args.searches else []
            run(number, root, ["-c", program, *extra, "--output",
                               str(scratch / "source12-verification.json")])
        elif number == 2:
            run(number, root, ["code/run_checks.py"])
            run(number, root, ["code/measure_psc_controls.py", "--repo",
                               "reference_sources/proveit", "--output",
                               str(scratch / "source13-controls")])
        elif number == 3:
            run(number, root, ["build.py"])
            extra = ["--search", "--seeds", "128"] if args.searches else []
            run(number, root, ["code/compress_full_equality.py", "--repo",
                               str(dependencies), "--incoming", "third_party/one_schema",
                               "--scratch", str(scratch / "source14-compression"), *extra])
            if args.searches:
                run(number, root, ["code/full_equality_epsc.py", "--repo",
                                   str(dependencies), "--scratch",
                                   str(scratch / "source14-arrangements")])
                for kernel in ("empty", "subset"):
                    run(number, root, ["code/psc_compile.py", "--repo", str(dependencies),
                                       "--scratch", str(scratch / f"source14-{kernel}"),
                                       "--kernel", kernel, "--grouped", "--search"])
        else:
            run(number, root, ["build.py", "--checks", "--machines", "--repo",
                               str(dependencies)])


if __name__ == "__main__":
    main()

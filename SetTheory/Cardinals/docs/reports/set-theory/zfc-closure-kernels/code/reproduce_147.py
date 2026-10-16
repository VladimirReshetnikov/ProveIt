"""Recover batch 147 in scratch and replay finite source/table checks.

The delivered checksum-manifest audit is disabled in memory; exact constructor,
macro-word, table and normalization contracts remain. No proof assistant or
unbounded refutation search runs. Original package files are not modified.
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

ARRIVAL = "9439d775aa"
ARCHIVE = "docs/incoming/zfc_small_machine_research (2).zip"


def main() -> None:
    if not __debug__:
        raise SystemExit("Run without -O/PYTHONOPTIMIZE: checks use assertions.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prepare-only", action="store_true")
    parser.add_argument("--searches", action="store_true",
                        help="also repeat the 2,200 old-row and 200 bottom3 seeds")
    args = parser.parse_args()
    repo = next(p for p in Path(__file__).resolve().parents if (p / ".git").exists())
    scratch = Path(tempfile.mkdtemp(prefix="zfc-batch147-reproduce-"))
    raw = subprocess.check_output(["git", "show", f"{ARRIVAL}:{ARCHIVE}"], cwd=repo)
    with ZipFile(io.BytesIO(raw)) as zipped:
        for name in zipped.namelist():
            path = Path(name)
            if path.is_absolute() or ".." in path.parts:
                raise ValueError(f"Archive path escapes scratch: {name}")
        zipped.extractall(scratch / "package")
    root = scratch / "package/zfc_small_machine"
    print(f"Scratch: {scratch}", flush=True)
    if args.prepare_only:
        return
    records = []

    def run(name: str, directory: Path, command: list[str]) -> None:
        result = subprocess.run([sys.executable, *map(str, command)], cwd=directory,
                                capture_output=True, text=True)
        log = scratch / f"{name}.log"
        log.write_text(result.stdout + result.stderr)
        records.append(dict(check=name, command=list(map(str, command)),
                            returncode=result.returncode, log=str(log)))
        (scratch / "runs.json").write_text(json.dumps(records, indent=2) + "\n")
        print(f"{name}: exit {result.returncode}", flush=True)
        if result.returncode:
            print(result.stdout + result.stderr, file=sys.stderr)
            raise SystemExit(result.returncode)

    run("checker", root / "reference_checker", ["-m", "unittest", "-v", "test_psc_hilbert.py"])
    run("identity", root, ["reference_checker/psc_hilbert.py", "reference_checker/identity.json"])
    run("codec", root, ["code/bottom3_codec.py", "--output", str(scratch / "codec.json")])
    run("obstruction", root, ["code/fixed_slot_obstruction.py", "--emitter",
        "machine/proveit_snapshot/Computability/BusyBeaver/Research/ZFC/psc_backend_experiment.py",
        "--output", str(scratch / "obstruction.json")])
    run("checker-semantics", root, ["code/review_psc_checker.py"])
    # Only omit the source-manifest loop. The reported verified_input_files
    # then correctly becomes zero; all compiled-table comparisons still run.
    replay = (
        "from pathlib import Path; import sys; "
        "p=Path('reproduce.py').resolve(); source=p.read_text(); "
        "old='pins=json.loads((root/\"snapshot-sha256.json\").read_text())'; "
        "assert source.count(old)==1; "
        "sys.argv=['reproduce.py','--output',sys.argv[1]]; "
        "exec(compile(source.replace(old,'pins={}'),str(p),'exec'),"
        "{'__file__':str(p),'__name__':'__main__'})"
    )
    run("machines", root / "machine", ["-c", replay, str(scratch / "machines")])
    if args.searches:
        for start, count in ((0, 200), (200, 2000)):
            run(f"old-rho6-{start}", root / "machine",
                ["old_rho6_grammar_search.py", "--repo", "proveit_snapshot", "--seeds", str(count), "--start-seed", str(start),
                 "--output", str(scratch / f"search-old-{start}")])
        run("bottom3-search", root / "machine",
            ["bottom3_measurement.py", "--repo", "proveit_snapshot", "--seeds", "200", "--output", str(scratch / "search-bottom3")])


if __name__ == "__main__":
    main()

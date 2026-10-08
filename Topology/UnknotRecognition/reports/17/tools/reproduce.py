"""Reproduce checks, optional timings and paper in a fresh run directory.

Default: integrated unit tests, independent mathematical oracles, replay
self-tests and example certificates. Use --all for benchmarks, the large
serialization check, and a fresh PDF build as well.
"""
import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import time


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--benchmarks", action="store_true")
    parser.add_argument("--paper", action="store_true")
    parser.add_argument("--large", action="store_true")
    parser.add_argument("--all", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S")
    run = (args.output or root / "reproduction_runs" / stamp).resolve()
    if run.exists():
        parser.error("output directory must be new")
    run.mkdir(parents=True)
    ignore = shutil.ignore_patterns("__pycache__", "*.pyc")
    for name in ("fast", "research", "benchmarks", "certificates"):
        shutil.copytree(root / name, run / name, ignore=ignore)
    logs = run / "logs"
    logs.mkdir()
    record = {"python": sys.version, "platform": platform.platform(), "steps": []}

    def execute(label, command, cwd=run):
        started = time.monotonic()
        print(label, flush=True)
        with (logs / (label + ".log")).open("w") as stream:
            result = subprocess.run(command, cwd=cwd, stdout=stream, stderr=subprocess.STDOUT)
        step = {"name": label, "command": command, "exit_code": result.returncode,
                "seconds": time.monotonic() - started}
        record["steps"].append(step)
        (run / "run_record.json").write_text(json.dumps(record, indent=2) + "\n")
        if result.returncode:
            raise SystemExit("Failed: " + label + "; see " + str(logs / (label + ".log")))

    py = sys.executable
    execute("unit_tests", [py, "-m", "unittest", "discover", "-s", "tests", "-v"], run / "fast")
    for name in ("check_residue_ch", "check_potts_independent",
                 "check_potts_factorized_adversarial", "check_jones_finite_menu"):
        execute(name, [py, str(run / "research" / (name + ".py"))])
    execute("certificate_selftest", [py, str(run / "research/verify_potts_certificate.py"),
                                    "--large-self-test" if args.large or args.all else "--self-test"])
    for path in sorted((run / "certificates").glob("*_certificate.json")):
        execute("replay_" + path.stem,
                [py, str(run / "research/verify_potts_certificate.py"), str(path)])
    if args.benchmarks or args.all:
        for stem in ("benchmark_potts", "pipeline_benchmark"):
            execute(stem, [py, str(run / "benchmarks" / (stem + ".py")),
                           "--fast-dir", str(run / "fast"),
                           "--output", str(run / "benchmarks" / (stem + "_rerun.json"))])
    if args.paper or args.all:
        shutil.copytree(root / "paper", run / "paper", ignore=ignore)
        execute("paper_figures", [py, str(run / "benchmarks/make_paper_figures.py"),
                                 "--paper-dir", str(run / "paper")])
        if shutil.which("latexmk") is None:
            raise SystemExit("PDF build requires latexmk, pdflatex, and BibTeX")
        execute("paper", ["latexmk", "-pdf", "-interaction=nonstopmode",
                          "-halt-on-error", "unknot_potts_frontiers.tex"], run / "paper")
    record["status"] = "PASS"
    (run / "run_record.json").write_text(json.dumps(record, indent=2) + "\n")
    print("Completed: " + str(run))


if __name__ == "__main__":
    main()

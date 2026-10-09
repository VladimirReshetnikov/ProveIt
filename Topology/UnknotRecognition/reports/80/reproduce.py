#!/usr/bin/env python3
"""Verify the package and reproduce exact checks without changing its evidence.

Default: checksums, 39 regression tests, and independent replay of 17 retained
coverage certificates. Optional audits and benchmarks write only to a new
output directory. No Regina installation is needed for the default checks.
"""
import argparse
from datetime import datetime, timezone
from hashlib import sha256
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent

def verify_manifest():
    manifest = json.loads((ROOT / "MANIFEST.json").read_text())
    failures = []
    for entry in manifest["files"]:
        path = ROOT / entry["path"]
        if not path.is_file():
            failures.append([entry["path"], "missing"])
        elif sha256(path.read_bytes()).hexdigest() != entry["sha256"]:
            failures.append([entry["path"], "digest mismatch"])
    if failures:
        raise RuntimeError("Package manifest failed: " + repr(failures))
    return len(manifest["files"])

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--audit", action="store_true",
                        help="Repeat the 9,995-support frozen-corpus audit.")
    parser.add_argument("--family", action="store_true",
                        help="Repeat exact family formulas and native topology census.")
    parser.add_argument("--fresh-regina", action="store_true",
                        help="Add fresh complete Regina oracles; implies --audit --family.")
    parser.add_argument("--differential", action="store_true",
                        help="Repeat the 1,646-sector and 240-abstract-cone audits.")
    parser.add_argument("--benchmark", action="store_true",
                        help="Repeat paired timings, including capped 40-second arms.")
    parser.add_argument("--sparse-benchmark", action="store_true",
                        help="Repeat the nine-case constructor comparison.")
    parser.add_argument("--pdf", action="store_true",
                        help="Compile an isolated copy of the supplied TeX article.")
    args = parser.parse_args()
    checked = verify_manifest()
    out = args.output_dir or ROOT / (
        "reproduction_" + datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ"))
    out = out.resolve()
    if out == ROOT or out in ROOT.parents:
        parser.error("Output must not be the package directory or one of its parents.")
    if out.exists() and any(out.iterdir()):
        parser.error("Choose a new or empty output directory to preserve evidence.")
    out.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ)
    env["PYTHONPATH"] = str(ROOT / "code")
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    records = []
    print(f"Verified {checked} manifest entries. Results: {out}", flush=True)

    def run(name, command, cwd=None):
        print(name, flush=True)
        start = time.perf_counter()
        log = out / (name + ".log")
        with log.open("w") as stream:
            answer = subprocess.run(command, cwd=cwd or ROOT / "code",
                                    env=env, stdout=stream,
                                    stderr=subprocess.STDOUT)
        record = dict(name=name, command=list(map(str, command)),
                      status="PASS" if answer.returncode == 0 else "FAIL",
                      seconds=time.perf_counter()-start, log=log.name)
        records.append(record)
        (out / "reproduction_summary.json").write_text(
            json.dumps(dict(manifest_files_checked=checked, runs=records), indent=2)+"\n")
        if answer.returncode:
            print(log.read_text()[-6000:], file=sys.stderr)
            raise SystemExit(answer.returncode)

    py = sys.executable
    run("regression_tests", [py, "-m", "unittest", "discover", "-s", "tests",
                            "-p", "test_*.py", "-v"])
    for name in ["planar_coverage_certificates", "double_cap_coverage_certificates"]:
        run(name + "_replay", [py, "-m", "planar_sector_research.replay",
            "--certificates", str(ROOT / "evidence" / (name + ".json")),
            "--output", str(out / (name + "_replay.json"))])
    if args.audit or args.fresh_regina:
        cmd = [py, "-m", "planar_sector_research.audit",
               "--corpus", str(ROOT / "fixtures/discovery_corpus.json"),
               "--output", str(out / "corpus_audit.json")]
        if args.fresh_regina:
            cmd.append("--fresh-regina")
        run("frozen_corpus", cmd)
        result = json.loads((out / "corpus_audit.json").read_text())
        expected = json.loads((ROOT / "evidence/corpus_audit_summary.json").read_text())
        if result["complete_output_sha256"] != expected["complete_output_sha256"]:
            raise AssertionError("Complete corpus output digest changed")
    if args.family or args.fresh_regina:
        cmd = [py, "-m", "planar_sector_research.family_audit",
               "--sizes", "1", "2", "4", "8",
               "--output", str(out / "double_cap_family_audit.json")]
        if args.fresh_regina:
            cmd.append("--fresh-regina")
        run("family_audit", cmd)
    if args.differential:
        run("independent_differential", [
            py, str(ROOT / "scripts/planar_differential_audit.py"),
            "--fast-root", str(ROOT / "code"), "--output-dir", str(out)])
    if args.benchmark:
        run("paired_benchmark", [
            py, "-m", "planar_sector_research.benchmark",
            "--prior-envelope", str(ROOT / "reference/sector_envelope.py"),
            "--output", str(out / "planar_benchmark.json")])
    if args.sparse_benchmark:
        run("sparse_constructor_benchmark", [
            py, str(ROOT / "scripts/sparse_builder_benchmark.py"),
            "--fast-root", str(ROOT / "code"),
            "--output", str(out / "sparse_builder_timings.json"), "--rounds", "5"])
    if args.pdf:
        article = out / "article"
        shutil.copytree(ROOT / "article", article,
                        ignore=shutil.ignore_patterns("*.aux", "*.log", "*.out",
                                                     "*.toc", "*.fls", "*.fdb_latexmk"))
        run("article_pdf", ["latexmk", "-pdf", "-interaction=nonstopmode",
                           "-halt-on-error", "planar_sectors.tex"], cwd=article)
    print("All requested checks completed.", flush=True)

if __name__ == "__main__":
    main()

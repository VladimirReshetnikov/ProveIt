"""Reproduce the bundled exact-sector checks without changing historical evidence.

With no mode flag, run the quick tests, independent audits, and Euler-corner comparison.
Every invocation creates a fresh directory below results/reproduction.
The optional corpus audit and benchmark retain their original scope.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
from hashlib import sha256
import json
from pathlib import Path
import platform
import subprocess
import sys
import tempfile
import time


ROOT = Path(__file__).resolve().parent


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")


def snapshot_check(fast, provenance):
    """Check the bundled snapshot; external checkouts record key hashes."""
    if fast == (ROOT / "code").resolve():
        problems = []
        for relative, record in provenance["code_files"].items():
            path = fast / relative
            if not path.is_file():
                problems.append({"file": relative, "problem": "missing"})
            elif digest(path) != record["sha256"]:
                problems.append({"file": relative, "problem": "hash differs"})
        if problems:
            raise ValueError("bundled code differs from PROVENANCE.json: "
                             + json.dumps(problems))
        return {"mode": "bundled", "verified_files": len(provenance["code_files"]),
                "status": "PASS"}
    files = {}
    for name in ("normal_sector.py", "normal_sector_verify.py",
                 "sector_planar.py", "sector_planar_verify.py",
                 "sector_planar_certificate.py"):
        path = fast / "fastunknot" / name
        files[name] = digest(path)
    return {"mode": "external checkout", "path": str(fast), "source_sha256": files,
            "status": "RECORDED", "baseline_byte_identity_asserted": False}


def arguments():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quick", action="store_true",
                        help="run quick checks (the default; also included in other modes)")
    parser.add_argument("--full-audit", action="store_true",
                        help="also replay all declared eligible sectors against the frozen corpus")
    parser.add_argument("--fresh-regina", action="store_true",
                        help="also freshly enumerate the corpus with optional Regina; implies --full-audit")
    parser.add_argument("--benchmark", action="store_true",
                        help="also run the paired benchmark and new-only capacity rows")
    parser.add_argument("--fast", type=Path, default=ROOT / "code",
                        help="fastunknot package directory (default: the bundled snapshot)")
    parser.add_argument("--output-dir", type=Path, default=ROOT / "results" / "reproduction",
                        help="parent directory for a new unique run directory")
    return parser.parse_args()


def main():
    args = arguments()
    fast = args.fast.resolve()
    if not (fast / "fastunknot").is_dir():
        raise SystemExit("No fastunknot package at " + str(fast))
    provenance = json.loads((ROOT / "PROVENANCE.json").read_text(encoding="utf-8"))
    checked = snapshot_check(fast, provenance)
    args.output_dir = args.output_dir.resolve()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ_")
    run_dir = Path(tempfile.mkdtemp(prefix=stamp, dir=args.output_dir))
    report = {
        "schema": "planar-sector-reproduction-v1",
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "python": platform.python_version(),
        "platform": platform.platform(),
        "baseline_commit": provenance["baseline_commit"],
        "scope": "Supplied-sector tests and audits; no whole-recognizer complexity claim.",
        "source_snapshot": checked,
        "package_provenance_sha256": digest(ROOT / "PROVENANCE.json"),
        "corpus_sha256": digest(ROOT / "fixtures" / "discovery_corpus.json"),
        "reproduction_driver_sha256": digest(Path(__file__).resolve()),
        "script_sha256": {
            str(path.relative_to(ROOT)): digest(path)
            for path in sorted((ROOT / "experiments").glob("*.py"))
        },
        "requested": {"full_audit": args.full_audit or args.fresh_regina,
                      "fresh_regina": args.fresh_regina,
                      "benchmark": args.benchmark},
        "steps": [],
        "status": "RUNNING",
    }
    summary_path = run_dir / "summary.json"
    write_json(summary_path, report)
    print("Fresh reproduction directory:", run_dir, flush=True)

    def run_step(name, command, cwd=ROOT):
        log = run_dir / (name + ".log")
        started = time.perf_counter()
        print("RUN", name, flush=True)
        with log.open("w", encoding="utf-8") as stream:
            result = subprocess.run(command, cwd=cwd, stdout=stream,
                                    stderr=subprocess.STDOUT, check=False)
        record = {"step": name, "returncode": result.returncode,
                  "seconds": time.perf_counter() - started, "log": log.name,
                  "command": [str(item) for item in command], "cwd": str(cwd)}
        report["steps"].append(record)
        write_json(summary_path, report)
        if result.returncode:
            report["status"] = "FAILED"
            report["finished_utc"] = datetime.now(timezone.utc).isoformat()
            write_json(summary_path, report)
            print(log.read_text(encoding="utf-8", errors="replace"), file=sys.stderr)
            raise SystemExit("Step failed; complete log: " + str(log))
        print("PASS", name, f"{record['seconds']:.3f}s", flush=True)

    # -S demonstrates that the native quick path needs no installed packages.
    # -B keeps bytecode files out of the immutable source snapshot.
    native = [sys.executable, "-B", "-S"]
    run_step("new_tests", native + [
        "-m", "unittest", "discover", "-s", "tests",
        "-p", "test_sector_planar*.py", "-v"], cwd=fast)
    run_step("baseline_integration", native + [
        "-m", "unittest", "discover", "-s", "tests",
        "-p", "test_normal_sector_integration.py", "-v"], cwd=fast)
    run_step("abstract_audit", native + [
        str(ROOT / "experiments" / "audit_abstract.py"),
        "--fast", str(fast), "--output", str(run_dir / "abstract_audit.json")])
    run_step("certificate_audit", native + [
        str(ROOT / "experiments" / "audit_certificates.py"),
        "--fast", str(fast), "--output", str(run_dir / "certificate_audit.json")])

    run_step("euler_corner_audit", native + [
        str(ROOT / "experiments" / "audit_euler_corners.py"),
        "--fast", str(fast), "--output", str(run_dir / "euler_corner_audit.json")])

    if args.full_audit or args.fresh_regina:
        interpreter = [sys.executable, "-B"] if args.fresh_regina else native
        command = interpreter + [str(ROOT / "experiments" / "audit.py"),
            "--fast", str(fast), "--output", str(run_dir / "corpus_audit.json")]
        if args.fresh_regina:
            command.append("--fresh-regina")
        run_step("corpus_audit", command)

    if args.benchmark:
        # The historical audit fixes benchmark case selection, independently
        # of which optional checks were requested in this invocation.
        run_step("benchmark", native + [
            str(ROOT / "experiments" / "benchmark.py"),
            "--fast", str(fast), "--output", str(run_dir / "paired_benchmark.json"),
            "--audit", str(ROOT / "results" / "corpus_audit.json"),
            "--mode", "paired", "--with-capacity"])
        report["benchmark_interpretation"] = (
            "Read individual result statuses. Reaching a configured deadline "
            "does not imply a mathematical negative result. Capacity rows "
            "have no baseline ratio; independent replays have separate limits.")

    report["status"] = "PASS"
    report["finished_utc"] = datetime.now(timezone.utc).isoformat()
    write_json(summary_path, report)
    print("PASS; full logs and machine-readable evidence:", run_dir, flush=True)


if __name__ == "__main__":
    main()


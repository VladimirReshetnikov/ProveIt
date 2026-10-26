#!/usr/bin/env python3
"""Offline replay of the complete release; standard library only."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def check_manifest(skip):
    if skip:
        return {"skipped_for_release_preparation": True}
    manifest = ROOT / "MANIFEST.sha256"
    require(manifest.is_file(), "Release manifest is missing")
    listed = set()
    for line in manifest.read_text().splitlines():
        expected, name = line.split("  ", 1)
        path = ROOT / name
        require(path.is_file(), "Missing release file: " + name)
        require(path.resolve().is_relative_to(ROOT), "Unsafe manifest path")
        require(hashlib.sha256(path.read_bytes()).hexdigest() == expected,
                "Changed release file: " + name)
        require(name not in listed, "Duplicate manifest entry")
        listed.add(name)
    require(len(listed) > 100, "Unexpectedly incomplete release manifest")
    return {"files_authenticated": len(listed)}


def replay(name, arguments):
    command = [sys.executable, "-B"]
    if not __debug__:
        command.append("-O")
    command.extend(str(a) for a in arguments)
    done = subprocess.run(command, cwd=ROOT, text=True,
                          capture_output=True, timeout=600)
    require(done.returncode == 0,
            name + " failed:\n" + done.stdout[-6000:] + done.stderr[-6000:])
    try:
        evidence = json.loads(done.stdout)
    except json.JSONDecodeError as error:
        raise ValueError(name + " did not emit a JSON receipt") from error
    return name, evidence


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--receipt", type=Path)
    parser.add_argument("--skip-manifest", action="store_true",
                        help="Release preparation only; omit for final verification")
    args = parser.parse_args()
    integrity = check_manifest(args.skip_manifest)
    with tempfile.TemporaryDirectory(prefix="conzfc-replay-") as temp:
        jobs = [
            ("positive", [ROOT / "positive/verify.py"]),
            ("direct", [ROOT / "direct/verify.py"]),
            ("direct_independent", [
                ROOT / "direct/check_independent.py",
                "--receipt", Path(temp) / "direct-independent.json"]),
            ("direct_byte_rebuild", [ROOT / "direct/rebuild.py"]),
            ("direct_factored", [
                ROOT / "direct/factored83/check_factored.py", "--rebuild"]),
            ("direct_printed_definition", [
                ROOT / "direct/check_printed_definition.py"]),
            ("pell_finite_diagnostics", [ROOT / "direct/check_lemma.py"]),
            ("frame_sources", [ROOT / "check_frame_sources.py"]),
            ("report_sources", [ROOT / "check_report.py"]),
            ("calibration_evidence", [ROOT / "check_calibration.py"]),
        ]
        with ThreadPoolExecutor(max_workers=4) as pool:
            futures = [pool.submit(replay, name, argv) for name, argv in jobs]
            checks = dict(f.result() for f in futures)
    result = {
        "status": "PASS",
        "python_optimized": not __debug__,
        "source_snapshot": "cdfea7d90176775d74c1c30afbe49fa78ade9897",
        "integrity": integrity,
        "checks": checks,
        "scope": "Exact finite arithmetic and reproducibility. Unbounded arithmetic "
                 "and inherited refutation calibration are ordinary proofs; "
                 "no new end-to-end proof-assistant build is claimed.",
    }
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.receipt:
        args.receipt.write_text(rendered)
    print(rendered, end="")


if __name__ == "__main__":
    main()

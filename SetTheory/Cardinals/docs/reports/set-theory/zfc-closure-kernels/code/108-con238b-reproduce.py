#!/usr/bin/env python3
"""Portable replay of the 238-state construction.

Default: complete new-table unbounded runtime, source, local fold and startup.
--quick omits unbounded runtime; --with-guard also reruns the independent
predecessor guard proof. All generated files go to a fresh output directory.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def check_manifest():
    manifest = ROOT / "SHA256SUMS"
    require(manifest.is_file(), "Missing SHA256SUMS")
    count = 0
    for line in manifest.read_text().splitlines():
        expected, name = line.split("  ", 1)
        relative = Path(name)
        require(not relative.is_absolute() and ".." not in relative.parts, "Unsafe manifest path")
        path = ROOT / relative
        require(path.is_file(), "Missing artifact: " + name)
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        require(actual == expected, "Artifact digest mismatch: " + name)
        count += 1
    return count


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--with-guard", action="store_true")
    ap.add_argument("--output", type=Path)
    a = ap.parse_args()
    require(__debug__ and not sys.flags.optimize and not os.environ.get("PYTHONOPTIMIZE"),
            "Use assertions: remove -O/-OO and unset PYTHONOPTIMIZE.")
    count = check_manifest()
    if a.output is None:
        output = Path(tempfile.mkdtemp(prefix="zfc238-replay-"))
    else:
        output = a.output.resolve()
        require(not output.exists() or not any(output.iterdir()), "Output must be new or empty")
        output.mkdir(parents=True, exist_ok=True)
    require(output != ROOT, "Output must not replace the package root")
    print(f"Verified {count} artifact hashes. Replay directory: {output}", flush=True)
    source = ROOT / "reference/source"
    verification = ROOT / "verification"
    records = []
    started = time.monotonic()

    def run(name, script, arguments, receipt, status):
        command = [sys.executable, "-B", str(script), *map(str, arguments)]
        logfile = output / (name + ".log")
        start = time.monotonic()
        print("Checking " + name + "...", flush=True)
        with logfile.open("w") as log:
            process = subprocess.Popen(command, cwd=ROOT, stdout=subprocess.PIPE,
                                       stderr=subprocess.STDOUT, text=True)
            for line in process.stdout:
                log.write(line)
                if line.lower().startswith(("proved ", "guarded ", "four exact", "all four")):
                    print(line.rstrip(), flush=True)
            code = process.wait()
        require(code == 0, f"{name} failed; inspect {logfile}")
        data = json.loads(receipt.read_text())
        require(data.get("status") == status, f"{name} did not prove its full stated contract")
        records.append({"name": name, "status": status, "receipt": str(receipt.relative_to(output)),
                        "seconds": time.monotonic() - start})
        print(name + ": PASS", flush=True)
        return data

    construction = run("construction", verification / "check_construction.py",
        ["--output-dir", output / "construction"], output / "construction/construction.json",
        "EXACT_238_CONSTRUCTION_AND_INITIALIZATION_PASS")
    run("source_certificate", source / "formalism/extra/check_rotation_certificate.py",
        ["--report", output / "source_certificate.json"], output / "source_certificate.json",
        "PASS_EXACT_SOURCE_CONTROL_CERTIFICATE")
    run("source_interface", source / "source_interface/check_source_interface.py",
        ["--output", output / "source_interface.json"], output / "source_interface.json",
        "EXACT_LEAN_SOURCE_DATA_AND_SEED_IDENTITY_PASS")
    run("source_intervals", verification / "check_source_intervals.py",
        ["--baseline", source / "baseline/rotation240/sites_logical.json",
         "--rotations", source / "formalism/extra/rotation_certificate.json",
         "--candidate", ROOT / "machines/sites_logical.json",
         "--output", output / "source_intervals.json"], output / "source_intervals.json",
        "PASS_INDEPENDENT_DYADIC_SOURCE_AND_FRAME_INTERFACE")
    run("local_fold", verification / "verify_fold238_local.py",
        ["--baseline", ROOT / "reference/boundary239_old.tm",
         "--candidate", ROOT / "machines/zfc_combined238_old.tm",
         "--output", output / "local_fold.json"], output / "local_fold.json",
        "INDEPENDENT_BOUNDARY239_TO_COMBINED238_LOCAL_PASS")
    if not a.quick:
        runtime = run("runtime238", verification / "verify_runtime238.py",
            ["--output", output / "runtime238.json"], output / "runtime238.json",
            "UNIVERSAL_238_MATHEMATICAL_PASS")
        require(runtime["cases"] == 8386 and runtime["symbolic_steps"] == 2255513,
                "Wrong runtime census")
    if a.with_guard:
        guard = run("predecessor_guard", verification / "verify_guard238.py",
            ["--table", ROOT / "reference/boundary239_old.tm",
             "--sites", ROOT / "machines/sites_logical.json",
             "--engine", verification / "symbolic_runtime.py",
             "--output-dir", output / "guard238"], output / "guard238/guard238_receipt.json",
            "BOUNDARY239_UNBOUNDED_NEXT_ONE_GUARD_PASS")
        require((guard["complete_cases"], guard["symbolic_rules"], guard["runtime_guard_events"],
                 guard["minimum_right_one_run_constant"]) == (8386, 2247513, 32, 23),
                "Wrong predecessor guard census")
    final = {
        "status": "QUICK_238_REPLAY_PASS" if a.quick else "FULL_238_MATHEMATICAL_REPLAY_PASS",
        "with_guard": a.with_guard, "artifact_hashes_checked": count,
        "canonical_sha256": construction["canonical_sha256"],
        "source_sha256": construction["source_sha256"],
        "jobs": records, "seconds": time.monotonic() - started,
        "python": sys.version, "assertions_enabled": True,
        "scope": "New mathematical certificate replay; inherited Lean/Rocq consistency proofs are identified but not rebuilt.",
    }
    (output / "REPLAY.json").write_text(json.dumps(final, indent=2) + "\n")
    print(json.dumps(final, indent=2))


if __name__ == "__main__":
    main()

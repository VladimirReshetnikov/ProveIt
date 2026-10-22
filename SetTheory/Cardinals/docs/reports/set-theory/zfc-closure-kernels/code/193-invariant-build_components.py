#!/usr/bin/env python3
"""Compile the two proposed Rocq components in a fresh private directory.

This is a component check, not the production K215/ZFC endpoint check.
The caller selects coqc and the matching coqchk, and supplies any compiler
environment (e.g. COQLIB and OCAMLFIND_CONF). Only standard Python is used.
"""
from pathlib import Path
import argparse
import fcntl
import hashlib
import json
import shutil
import subprocess
import time


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--coqc", default="coqc")
    parser.add_argument("--coqchk", default="coqchk")
    parser.add_argument("--lock", type=Path,
                        default=Path("/tmp/proveit-k215-proof-build.lock"))
    args = parser.parse_args()
    src = Path(__file__).resolve().parent
    work = args.out.resolve()
    work.mkdir(parents=True, exist_ok=False)
    coqc = shutil.which(args.coqc)
    coqchk = shutil.which(args.coqchk)
    if not coqc or not coqchk:
        raise SystemExit("Both coqc and the matching coqchk are required.")
    for module in ("BusyCoq", "K215F"):
        (work / module).mkdir()
        for path in sorted((src / "relabel" / module).glob("*.v")):
            shutil.copyfile(path, work / module / path.name)
    shutil.copyfile(src / "TerminalDrain.v", work / "TerminalDrain.v")
    flags = ["-Q", str(work / "BusyCoq"), "BusyCoq",
             "-Q", str(work / "K215F"), "K215F"]
    receipt = {
        "scope": "Standalone terminal drain and concrete dense/sparse relabeling; no full ZFC rebuild",
        "version": subprocess.check_output([coqc, "--version"], text=True).strip(),
        "compiler_sha256": digest(Path(coqc)),
        "checker_sha256": digest(Path(coqchk)),
        "sources": {str(p.relative_to(work)): digest(p)
                    for p in sorted(work.rglob("*.v"))},
        "commands": [],
    }
    targets = [
        "TerminalDrain", "BusyCoq/LibTactics", "BusyCoq/Helper", "BusyCoq/TM",
        "K215F/Table230", "K215F/TM230", "K215F/Table215",
        "K215F/StateRelabel", "K215F/Dense215",
    ]
    commands = [("compile-" + target.replace("/", "."),
                 [coqc, *flags, str(work / (target + ".v"))]) for target in targets]
    commands += [("kernel-TerminalDrain", [coqchk, *flags, "-silent", "-o", "TerminalDrain"]),
                 ("kernel-Dense215", [coqchk, *flags, "-silent", "-o", "K215F.Dense215"])]
    for label, command in commands:
        with args.lock.open("a") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            started = time.monotonic()
            result = subprocess.run(command, cwd=work, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            elapsed = time.monotonic() - started
        log = work / (label + ".log")
        log.write_text(result.stdout)
        row = {"label": label, "command": command, "returncode": result.returncode,
               "seconds": elapsed, "log": log.name, "log_sha256": digest(log),
               "closed_reports": result.stdout.count("Closed under the global context")}
        receipt["commands"].append(row)
        (work / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
        print(label, "PASS" if result.returncode == 0 else "FAIL", flush=True)
        if result.returncode:
            raise SystemExit(result.stdout)
        if label == "compile-TerminalDrain" and row["closed_reports"] != 3:
            raise SystemExit("Expected three closed standalone assumption reports.")
        if label == "compile-K215F.Dense215" and row["closed_reports"] != 1:
            raise SystemExit("Expected the concrete relabeling endpoint to be closed.")
    receipt["status"] = "PASS_COMPONENTS_COQCHK"
    (work / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")


if __name__ == "__main__":
    main()

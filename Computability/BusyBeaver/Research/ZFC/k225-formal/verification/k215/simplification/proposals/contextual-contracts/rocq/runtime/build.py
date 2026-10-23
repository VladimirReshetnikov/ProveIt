#!/usr/bin/env python3
"""Replay the actual-runtime guarded left-frame component and 35 local templates.

This is a ten-source component build, not a rebuild of the K215 ZFC endpoint.
Use --toolchain for an unpacked Ubuntu Coq installation; otherwise coqc/coqchk
must be on PATH. The delivered run uses Coq 8.18.0 / OCaml 4.14.1.
"""
from pathlib import Path
import argparse
import fcntl
import hashlib
import json
import os
import shutil
import subprocess
import time

HERE = Path(__file__).resolve().parent
ORDER = ["BusyCoq/LibTactics.v", "BusyCoq/Helper.v", "BusyCoq/TM.v", "K215F/Table230.v", "K215F/TM230.v", "K215F/Zip.v", "K215F/Boot230.v", "K215F/Runtime230Core.v", "Refactor/LeftFrame.v", "Refactor/LeftFrame215.v"]


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--toolchain", type=Path)
    ap.add_argument("--lock", type=Path,
                    default=Path("/tmp/proveit-k215-proof-build.lock"))
    args = ap.parse_args()
    out = args.out.resolve()
    if out.exists() and any(out.iterdir()):
        raise SystemExit("Use a fresh empty output directory.")
    work, logs = out / "sources", out / "logs"
    work.mkdir(parents=True)
    logs.mkdir()
    env = os.environ.copy()
    if args.toolchain:
        tc = args.toolchain.resolve()
        env.update(OCAMLFIND_CONF=str(tc / "ocamlfind.conf"),
                   COQLIB=str(tc / "usr/lib/ocaml/coq"))
        coqc, coqchk = str(tc / "usr/bin/coqc"), str(tc / "usr/bin/coqchk")
    else:
        coqc, coqchk = shutil.which("coqc"), shutil.which("coqchk")
    if not coqc or not coqchk:
        raise SystemExit("Both coqc and coqchk are required.")
    options = ["-Q", "BusyCoq", "BusyCoq", "-Q", "K215F", "K215F",
               "-Q", "Refactor", "Refactor"]
    receipt = {"schema": "k215-guarded-left-frame-v1", "status": "RUNNING",
               "scope": "Actual Runtime230Core framing component; no full endpoint or concrete Home composition",
               "toolchain": subprocess.check_output([coqc, "--version"], env=env,
                                                     text=True).strip(),
               "coqc_sha256": sha(coqc), "coqchk_sha256": sha(coqchk),
               "sources": {}, "commands": []}
    for name in ORDER:
        src, dest = HERE / "src" / name, work / name
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(src, dest)
        receipt["sources"][name] = {"sha256": sha(src), "bytes": src.stat().st_size,
                                    "lines": len(src.read_text().splitlines())}

    def save():
        (out / "result.json").write_text(json.dumps(receipt, indent=2) + "\n")

    def run(label, command):
        start = time.monotonic()
        p = subprocess.run(command, cwd=work, env=env, stdout=subprocess.PIPE,
                           stderr=subprocess.STDOUT, text=True)
        log = logs / (label + ".log")
        log.write_text(p.stdout)
        receipt["commands"].append({"command": command, "exit_code": p.returncode,
                                    "elapsed_seconds": time.monotonic() - start,
                                    "log": str(log.relative_to(out)),
                                    "log_sha256": sha(log),
                                    "closed_reports": p.stdout.count("Closed under the global context")})
        if p.returncode:
            receipt["status"] = "FAILED"
            save()
            print(p.stdout)
            raise SystemExit(p.returncode)
        save()
        print(label, "PASS", flush=True)

    with args.lock.open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        for name in ORDER:
            run(name.replace("/", "_"), [coqc, *options, name])
        run("recursive_coqchk", [coqchk, *options, "-silent", "Refactor.LeftFrame215"])
    receipt["objects"] = {str(p.relative_to(work)): sha(p) for p in sorted(work.rglob("*.vo"))}
    count = sum(r["closed_reports"] for r in receipt["commands"])
    if count != 6:
        raise SystemExit(f"Expected six closed reports, observed {count}.")
    receipt["status"] = "PASS_COMPONENT_CLOSED_RECURSIVE_KERNEL"
    save()
    print(receipt["status"])


if __name__ == "__main__":
    main()

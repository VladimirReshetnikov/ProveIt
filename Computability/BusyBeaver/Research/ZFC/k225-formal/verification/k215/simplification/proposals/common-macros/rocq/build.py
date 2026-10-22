#!/usr/bin/env python3
"""Fresh, serial Coq build and recursive kernel recheck of the macro prototype.

This writes only into the chosen build directory. No remote access is used.
Run: python3 build.py --build-dir build-checked
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import time

MODULES = [
    "K230/RM", "K230S/KCode230", "K230L/Codes230",
    "KLocal/LocalProgram", "KLocal/MacroProgram", "KLocal/MacroInterface",
    "K215F/DagPerm", "KLocal/Macro215Binding", "KLocal/MacroLibrary",
    "KLocal/Macro215Contracts", "K217F/DagDom", "KLocal/Macro217Binding",
    "KLocal/MacroBindings",
]
NAMESPACES = ["K230", "K230S", "K230L", "K215F", "K217F", "KLocal"]


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--coqc", default="coqc")
    parser.add_argument("--coqchk", default="coqchk")
    parser.add_argument("--build-dir", default="build-checked")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    out = Path(args.build_dir).resolve()
    if out.exists():
        raise SystemExit(f"Fresh build requires a new directory: {out}")
    out.mkdir(parents=True)
    (out / "logs").mkdir()
    shutil.copytree(root / "src", out / "src", ignore=shutil.ignore_patterns(
        "*.vo", "*.vos", "*.vok", "*.glob", ".*.aux"))
    flags = [piece for ns in NAMESPACES for piece in ["-Q", "src/" + ns, ns]]
    version = subprocess.run([args.coqc, "--version"], capture_output=True,
                             text=True, check=True).stdout
    result = {"status": "RUNNING", "toolchain": version,
              "input_hashes": {m + ".v": sha(root / "src" / (m + ".v"))
                               for m in MODULES}, "compilations": []}
    (out / "toolchain.txt").write_text(version)

    def save() -> None:
        (out / "result.json").write_text(json.dumps(result, indent=2) + "\n")

    save()
    for module in MODULES:
        argv = [args.coqc, *flags, "src/" + module + ".v"]
        start = time.monotonic()
        run = subprocess.run(argv, cwd=out, capture_output=True, text=True)
        log = run.stdout + run.stderr
        logname = module.replace("/", ".") + ".log"
        (out / "logs" / logname).write_text(log)
        result["compilations"].append({"module": module.replace("/", "."),
            "argv": argv, "returncode": run.returncode,
            "elapsed_seconds": round(time.monotonic() - start, 3),
            "closed_reports": log.count("Closed under the global context"),
            "log": "logs/" + logname})
        if run.returncode:
            result["status"] = "COMPILE_FAILED"
            save()
            raise SystemExit(f"Failed: {module}; see {out / 'logs' / logname}")
        save()
        print(f"PASS {module}", flush=True)
    contracts = next(c for c in result["compilations"]
                     if c["module"] == "KLocal.Macro215Contracts")
    if contracts["closed_reports"] != 58:
        result["status"] = "ASSUMPTION_REPORT_MISMATCH"
        save()
        raise SystemExit("Expected 58 closed contract reports")
    argv = [args.coqchk, "-silent", "-o", *flags,
            "KLocal.Macro215Contracts", "KLocal.MacroBindings"]
    start = time.monotonic()
    run = subprocess.run(argv, cwd=out, capture_output=True, text=True)
    (out / "kernel.log").write_text(run.stdout + run.stderr)
    result["kernel"] = {"argv": argv, "returncode": run.returncode,
        "elapsed_seconds": round(time.monotonic() - start, 3), "log": "kernel.log"}
    result["status"] = "PASS_CLOSED_KERNEL" if run.returncode == 0 else "KERNEL_FAILED"
    save()
    print(result["status"], flush=True)
    if run.returncode:
        raise SystemExit(run.returncode)


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Serial fresh compilation and recursive kernel checking of marker certificates."""
from pathlib import Path
import argparse, fcntl, hashlib, json, shutil, subprocess, time

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--coqc", default="coqc")
    ap.add_argument("--coqchk", default="coqchk")
    args = ap.parse_args()
    root = Path(__file__).resolve().parent
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    names = ("MarkerFold.v", "MarkerTables.v", "MarkerInstances.v")
    for name in names:
        shutil.copy2(root / name, out / name)
    receipt = {"sources": {n: digest(root / n) for n in names}, "commands": []}
    receipt["compiler"] = subprocess.check_output([args.coqc, "--version"], text=True)
    for name in names:
        command = [args.coqc, name]
        with open("/tmp/proveit-proof-compiler.lock", "w") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            start = time.monotonic()
            p = subprocess.run(command, cwd=out, text=True, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT)
            elapsed = time.monotonic() - start
        (out / (name + ".log")).write_text(p.stdout)
        receipt["commands"].append({"command": command, "returncode": p.returncode,
                                    "seconds": elapsed})
        if p.returncode:
            (out / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
            raise SystemExit(p.stdout)
    command = [args.coqchk, "-silent", "MarkerInstances"]
    with open("/tmp/proveit-proof-compiler.lock", "w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        start = time.monotonic()
        p = subprocess.run(command, cwd=out, text=True, stdout=subprocess.PIPE,
                           stderr=subprocess.STDOUT)
        elapsed = time.monotonic() - start
    (out / "coqchk.log").write_text(p.stdout)
    receipt["commands"].append({"command": command, "returncode": p.returncode,
                                "seconds": elapsed})
    receipt["closed_assumption_reports"] = sum((out / (n + ".log")).read_text().count(
        "Closed under the global context") for n in names)
    receipt["success"] = p.returncode == 0
    receipt["objects"] = {p.name: digest(p) for p in out.glob("*.vo")}
    (out / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    if p.returncode:
        raise SystemExit(p.stdout)
    print(json.dumps(receipt, indent=2))

if __name__ == "__main__":
    main()

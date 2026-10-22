#!/usr/bin/env python3
"""Compile the six-module prototype and run recursive kernel checking."""
import hashlib
import json
import os
import subprocess
import time
from pathlib import Path

here = Path(__file__).resolve().parent
flags = []
for namespace in ("K230", "K215F", "K217F", "K218F"):
    flags += ["-Q", "deps/" + namespace, namespace]
coqc, coqchk = os.environ.get("COQC", "coqc"), os.environ.get("COQCHK", "coqchk")
files = ["deps/K230/RM.v", "deps/K215F/DagPerm.v", "deps/K217F/DagDom.v",
         "deps/K218F/Dag219.v", "RMSlice.v", "K215MacroSlice.v"]
commands = [[coqc, "--version"]] + [[coqc, *flags, f] for f in files]
commands.append([coqchk, "-silent", *flags, "K215MacroSlice"])
records = []
for command in commands:
    start = time.monotonic()
    result = subprocess.run(command, cwd=here, text=True, capture_output=True)
    record = {"command": command, "returncode": result.returncode,
              "seconds": time.monotonic() - start, "stdout": result.stdout,
              "stderr": result.stderr}
    records.append(record)
    print(command[-1] + ": " + str(result.returncode), flush=True)
    (here / "build_receipt.json").write_text(json.dumps({"records": records,
        "sha256": {f: hashlib.sha256((here/f).read_bytes()).hexdigest() for f in files}}, indent=2) + "\n")
    if result.returncode:
        print(result.stdout + result.stderr)
        raise SystemExit(result.returncode)

"""Rebuild and replay the finite differential audit in a temporary directory.

No search executable or test executable is shipped with this package.
Pass --release-root to also replay arithmetic/orbit/run-record checks.
"""
import argparse
import json
import os
from pathlib import Path
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--compiler", default=os.environ.get("CXX", "g++"))
parser.add_argument("--sanitize", action="store_true", help="Enable address and undefined-behavior sanitizers")
parser.add_argument("--release-root", type=Path, help="Frozen release folder, for structural checks")
args = parser.parse_args()
with tempfile.TemporaryDirectory(prefix="lattice_audit_") as temporary:
    for implementation in range(3):
        binary = str(Path(temporary) / ("audit_" + str(implementation)))
        flags = ["-std=c++17", "-O1" if args.sanitize else "-O2"]
        if args.sanitize:
            flags += ["-g", "-fsanitize=address,undefined", "-fno-omit-frame-pointer"]
        subprocess.run([args.compiler, *flags, "-DAUDIT_IMPL=" + str(implementation),
                        str(HERE / "differential_audit.cpp"), "-o", binary], check=True)
        result = subprocess.run([binary], check=True, capture_output=True, text=True)
        actual = json.loads(result.stdout)
        expected = json.loads((HERE / ("differential_audit_" + str(implementation) + ".json")).read_text())
        if actual != expected:
            raise RuntimeError("Recorded summary mismatch for implementation " + str(implementation))
        if result.stderr:
            print(result.stderr, end="")
            raise RuntimeError("Unexpected audit diagnostics")
        print(json.dumps(actual), flush=True)
    if args.release_root is not None:
        result = subprocess.run([os.sys.executable, str(HERE / "structural_audit.py"),
                                 str(args.release_root.resolve())], check=True, capture_output=True, text=True)
        actual = json.loads(result.stdout)
        expected = json.loads((HERE / "structural_audit.json").read_text())
        if actual != expected:
            raise RuntimeError("Recorded structural summary mismatch")
        print(json.dumps(actual, indent=2))

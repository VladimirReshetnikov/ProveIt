#!/usr/bin/env python3
"""Replay the reported Lean checks in a configured ProveIt Lake environment.

Run from a complete checkout with its locked dependencies already available:
  lake env python3 /path/to/packet/scripts/replay.py --repo . --work /tmp/lean-replay

The work directory must be new. This script never patches the checkout and
does not claim to compile the production ObjectPolynomial/NativeBinaryScale
patches or the complete object-model clients of polynomial transport.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--work", type=Path, required=True)
    args = parser.parse_args()
    packet = Path(__file__).resolve().parents[1]
    repo = args.repo.resolve()
    work = args.work.resolve()
    lean = shutil.which("lean")
    if lean is None or not os.environ.get("LEAN_PATH"):
        parser.error("Run this script through 'lake env python3' in the configured checkout.")
    if work.exists():
        parser.error("--work must name a new directory; existing output is never overwritten.")
    provenance = json.loads((packet / "evidence/source-provenance.json").read_text())
    for record in provenance["source_records"]:
        source = repo / record["path"]
        if not source.is_file():
            parser.error(f"Missing source: {source}")
        actual = hashlib.sha256(source.read_bytes()).hexdigest()
        if actual != record["sha256"]:
            parser.error(f"Baseline bytes differ: {source}; use the recorded source snapshot.")
    version = subprocess.check_output([lean, "--version"], text=True).strip()
    if "4.32.0" not in version:
        parser.error(f"Expected the pinned Lean 4.32.0 toolchain, found {version}")

    work.mkdir(parents=True)
    (work / "logs").mkdir()
    build = work / "build"
    build.mkdir()
    env = os.environ.copy()
    # Resolve Lake's possibly relative entries before switching to the work dir.
    inherited = [str(Path(p).resolve()) for p in env["LEAN_PATH"].split(os.pathsep) if p]
    env["LEAN_PATH"] = os.pathsep.join([str(build), *inherited])
    receipts = []

    def compile_one(label, source, module, audit_endpoint=None):
        stage = work / "sources" / label / (module.replace(".", "/") + ".lean")
        stage.parent.mkdir(parents=True, exist_ok=True)
        original = source.read_bytes()
        stage.write_bytes(original)
        if audit_endpoint:
            with stage.open("a") as handle:
                handle.write(f"\n#print axioms {audit_endpoint}\n")
        target = build / (module.replace(".", "/") + ".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        command = [lean, str(stage), "-o", str(target)]
        start = time.monotonic()
        result = subprocess.run(command, cwd=work, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        elapsed = time.monotonic() - start
        output = result.stdout + f"\nLEAN_EXIT={result.returncode}; ELAPSED_SECONDS={elapsed:.3f}\n"
        (work / "logs" / f"{label}.log").write_text(output)
        receipts.append({"label": label, "source": str(source),
                         "source_sha256": hashlib.sha256(original).hexdigest(),
                         "exit_code": result.returncode, "elapsed_seconds": elapsed,
                         "log": f"logs/{label}.log"})
        (work / "replay.json").write_text(json.dumps({"toolchain": version,
            "scope": "Targeted checks only; full object-model integration remains pending.",
            "records": receipts}, indent=2) + "\n")
        print(f"{label}: {'PASS' if result.returncode == 0 else 'FAIL'}", flush=True)
        if result.returncode:
            print(output, file=sys.stderr)
            raise SystemExit(result.returncode)

    source_root = repo / "Computability/DiophantineConsistency/Lean/DiophantineConsistency"
    for name in ("Representation", "ArithmeticRepresentation", "NaturalExpression",
                 "NaturalExpressionSemiring"):
        compile_one(name, source_root / f"{name}.lean", f"DiophantineConsistency.{name}")
    for name in ("PolynomialZeroTransport", "PolynomialZeroTransportClients",
                 "EnvironmentRestriction", "WidthDivisibilityBefore",
                 "WidthDivisibilityAfter", "PrimeRadix"):
        compile_one(name, packet / "lean" / f"{name}.lean", name)
    for name, directory in (("SyntaxCoefficients-before", "baseline"),
                            ("SyntaxCoefficients-after", "candidates")):
        compile_one(name, packet / directory / "SyntaxCoefficients.lean",
                    "DiophantineConsistency.SyntaxCoefficients",
                    "DiophantineConsistency.SyntaxCoefficients.coefficient_expand")
    print(f"Completed {len(receipts)} targeted checks. Receipts: {work / 'replay.json'}")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Check every folded source site and the literal controller endpoint."""
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys


if len(sys.argv) != 6:
    raise SystemExit("usage: check-folded-coverage.py REPO SOURCE OUTPUT STAGES JOBS")
repo, source, out, manifest = (Path(arg).resolve() for arg in sys.argv[1:5])
jobs = int(sys.argv[5])
stages = [Path(line).resolve() for line in manifest.read_text().splitlines() if line]
if out.exists():
    raise SystemExit(f"Output already exists: {out}")
if any(not stage.is_dir() for stage in stages):
    raise SystemExit("A staged dependency directory is missing")
src = out / "sources"
src.mkdir(parents=True)
lake_path = subprocess.check_output(
    ["lake", "env", "printenv", "LEAN_PATH"], cwd=repo, text=True
).strip()
env = os.environ | {"LEAN_PATH": ":".join(map(str, [out, *stages])) + ":" + lake_path}


def compile_module(module):
    with (out / f"{module}.log").open("w") as log:
        result = subprocess.run(
            ["lean", "-R", str(src), "-j1", "-M6000", "-o", str(out / f"{module}.olean"),
             str(src / f"{module}.lean")],
            cwd=repo, env=env, stdout=log, stderr=subprocess.STDOUT,
        )
    return result.returncode


def run(start):
    stop = min(start + 100, 3673)
    module = f"PA194FoldedBatch{start}_{stop}"
    lines = [
        "import PA194FoldedChecks",
        "set_option maxRecDepth 65536",
        "set_option maxHeartbeats 0",
        "namespace PA194FoldedCoverageBatches",
        "open PA194FoldedChecks",
    ]
    for i in range(start, stop, 10):
        lines.append(f"theorem c{i} : blockCheck {i} {min(10, stop-i)} = true := by decide +kernel")
    lines.append("end PA194FoldedCoverageBatches")
    (src / (module + ".lean")).write_text("\n".join(lines) + "\n")
    result = compile_module(module)
    print(f"{start}-{stop} exit {result}", flush=True)
    return result


with ThreadPoolExecutor(max_workers=jobs) as workers:
    statuses = list(workers.map(run, range(0, 3673, 100)))
if any(statuses):
    raise SystemExit("At least one folded source interval failed")

subprocess.run(
    [sys.executable, str(source / "generate-folded-coverage-aggregate.py"),
     str(src / "PA194FoldedAllCoverage.lean")],
    cwd=repo, check=True,
)
controllers = ("PA194LiteralControllerCorrectness", "PA194NativeControllerCorrectness")
for controller in controllers:
    (src / f"{controller}.lean").write_bytes((source / f"{controller}.lean").read_bytes())
audit = [("PA194FoldedAllCoverage", "all"), *((controller, "endpoint") for controller in controllers)]
for module, theorem in audit:
    result = compile_module(module)
    report = (out / f"{module}.log").read_text()
    print(report, end="")
    if result or "sorryAx" in report or "Lean.ofReduceBool" in report:
        raise SystemExit(f"{module} failed")
    if f"'{module}.{theorem}' depends on axioms:" not in report:
        raise SystemExit(f"Missing axiom audit for {module}.{theorem}")
receipt = {
    path.name: hashlib.sha256(path.read_bytes()).hexdigest()
    for path in sorted(src.glob("*.lean"))
}
(out / "coverage-receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
print("PASS: all 3673 folded source sites and both forms of the literal controller endpoint")

#!/usr/bin/env python3
"""Replay PA194HX's literal blank startup and its IΣ₁ model lift."""

from concurrent.futures import ThreadPoolExecutor
import os
from pathlib import Path
import resource
import subprocess
import sys

if len(sys.argv) != 4:
    raise SystemExit("usage: check.py PRIMARY_LITERAL_STAGE PA194B_STAGE NEW_OUTPUT")
literal, shared, out = (Path(arg).resolve() for arg in sys.argv[1:])
here = Path(__file__).resolve().parent
repo = Path(subprocess.check_output(
    ["git", "-C", here, "rev-parse", "--show-toplevel"], text=True
).strip())
if not (literal / "PA194NativeLiteralFinal.olean").is_file():
    raise SystemExit("expected checked primary literal stage")
if not (shared / "PA194BNative.olean").is_file():
    raise SystemExit("expected checked PA194B stage")
out.mkdir(parents=True)
resource.setrlimit(resource.RLIMIT_STACK, (resource.RLIM_INFINITY, resource.RLIM_INFINITY))
resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
env = os.environ | {"LEAN_PATH": ":".join((str(out), str(shared), (literal / "leanpath.txt").read_text().strip()))}


def check(source):
    name = source.stem
    log = out / (name + ".log")
    with log.open("w") as stream:
        result = subprocess.run(
            ["lean", "-j1", "-M6000", "-R", source.parent, "-o", out / (name + ".olean"), source],
            cwd=repo, env=env, stdout=stream, stderr=subprocess.STDOUT,
        )
    report = log.read_text()
    forbidden = ("error:", "sorryAx", "Lean.ofReduceBool", "declaration uses 'sorry'")
    if result.returncode or any(mark in report for mark in forbidden):
        raise RuntimeError(f"{name} failed\n{report}")
    print(f"PASS {name}", flush=True)


for generator in ("generate-table.py", "generate-startup.py"):
    subprocess.run([sys.executable, "-I", here / generator, repo, out], check=True)

foundation = repo / "Computability/BusyBeaver/Research/PA/shared/isigma1-machine"
check(foundation / "ConPAMachineNumerals.lean")
check(here.parent / "PA194IndexedNumerals.lean")
for module in ("PA194HXLiteral", "PA194HXRows", "PA194HXDenseStartupData"):
    check(out / (module + ".lean"))
for module in ("PA194HXDispatch", "PA194HXZipBridge", "PA194HXAllocation"):
    check(here / (module + ".lean"))

blocks = sorted(out.glob("PA194HXDenseStartupBlock*.lean"))
if len(blocks) != 44:
    raise SystemExit("expected 44 startup blocks")
with ThreadPoolExecutor(max_workers=2) as pool:
    list(pool.map(check, blocks))

check(out / "PA194HXDenseStartupComplete.lean")
check(here / "PA194HXModelStartup.lean")
check(here / "PA194HXSharedStartup.lean")
endpoint = "'PA194HXSharedStartup.sharedSeed' depends on axioms: [propext, Classical.choice, Quot.sound]"
report = (out / "PA194HXSharedStartup.log").read_text().splitlines()
if endpoint not in report:
    raise SystemExit("missing the expected shared-seed axiom audit")
print(endpoint)

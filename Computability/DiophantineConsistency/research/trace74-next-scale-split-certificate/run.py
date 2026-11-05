#!/usr/bin/env python3
"""Serial bounded split replay; stops on the first failed stage."""
import hashlib
import json
import pathlib
import subprocess
import sys
import time

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit("use python3 -I -S -B without optimization")
HERE = pathlib.Path(__file__).resolve().parent
OUT = pathlib.Path("/tmp/trace74-b65537-split-run01")
manifest = json.loads((HERE / "manifest.json").read_text())
stages = manifest["stages"]
assert len(stages) == 34 and stages[0]["module"] == "Trace74SplitCommon" and stages[-1]["module"] == "Trace74SplitFinal"
if OUT.exists() or (HERE / "observations").exists():
    raise SystemExit("refusing to overwrite output or observations")
OUT.mkdir()
(OUT / "lib").mkdir()
(HERE / "observations").mkdir()
outer = HERE / "observations" / "outer"
outer.mkdir()
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
manifest_sha = sha(HERE / "manifest.json")
runner_sha = sha(HERE / "run.py")
stage_sha = sha(HERE / "stage.py")
records = []
for i, stage in enumerate(stages):
    name = stage["module"]
    print(f"START {i+1}/{len(stages)} {name}", flush=True)
    command = ["systemd-run", "--user", "--scope", "--quiet", "--property=MemoryMax=2147483648",
               "--property=MemorySwapMax=0", "python3", "-I", "-S", "-B", str(HERE / "stage.py"), str(i), str(OUT)]
    start = time.monotonic()
    try:
        proc = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60, check=False)
        output, code = proc.stdout, proc.returncode
    except subprocess.TimeoutExpired as exc:
        output, code = (exc.stdout or b"")+b"\nOuter scope-launch timeout after 60 seconds.\n", 124
    log = outer / (name+".log")
    log.write_bytes(output)
    receipt = HERE / "observations" / name / "result.json"
    stage_result = json.loads(receipt.read_text()) if receipt.is_file() else None
    guards_ok = sha(HERE / "manifest.json") == manifest_sha and sha(HERE / "run.py") == runner_sha and sha(HERE / "stage.py") == stage_sha
    ok = code == 0 and stage_result is not None and stage_result["status"] == "PASS" and guards_ok
    records.append({"module": name, "outer_exit": code, "outer_seconds": round(time.monotonic()-start, 3),
                    "outer_log_sha256": sha(log), "stage_result_sha256": sha(receipt) if receipt.is_file() else None,
                    "status": "PASS" if ok else "FAIL"})
    (HERE / "observations" / "outer-state.json").write_text(json.dumps(records, indent=2, sort_keys=True)+"\n")
    print(f"{'PASS' if ok else 'FAIL'} {name}", flush=True)
    if not ok:
        print(output.decode(errors="replace")[-3000:], flush=True)
        raise SystemExit(1)
print("PASS: all 34 bounded stages including final closed Nat certificate", flush=True)

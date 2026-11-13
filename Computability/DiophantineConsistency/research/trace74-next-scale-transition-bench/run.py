#!/usr/bin/env python3
"""Run one extracted Lean declaration inside a preconfigured 2 GiB cgroup."""
import hashlib
import json
import os
import pathlib
import resource
import subprocess
import sys
import time

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit("use python3 -I -S -B without optimization")
if len(sys.argv) != 2 or sys.argv[1] not in ("transition00", "transition15", "transition31", "bezout"):
    raise SystemExit("usage: run.py transition00|transition15|transition31|bezout")
name = sys.argv[1]
root = pathlib.Path(__file__).resolve().parent
out = root / "observations" / name
source = out / "Certificate.lean"
manifest = root / "manifest.json"
parent = root.parent / "trace74-next-scale-kernel-certificate/observations/B65537/Certificate.lean"
if (out / "result.json").exists():
    raise SystemExit("refusing to overwrite an existing result")
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
spec = json.loads(manifest.read_text())
if sha(parent) != spec["parent_sha256"] or sha(source) != spec["declarations"][name]["source_sha256"]:
    raise SystemExit("parent or extracted source hash mismatch")
scope = next(line.split(":", 2)[2] for line in pathlib.Path("/proc/self/cgroup").read_text().splitlines() if line.startswith("0::"))
cgroup = pathlib.Path("/sys/fs/cgroup") / scope.lstrip("/")
limit = (cgroup / "memory.max").read_text().strip()
swap_limit = (cgroup / "memory.swap.max").read_text().strip()
if limit != str(2 * 1024**3) or swap_limit != "0":
    raise SystemExit(f"unexpected actual cgroup limits: memory.max={limit}, swap.max={swap_limit}")
before = (cgroup / "memory.events").read_text()
lean = "/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean"
library_path = "/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib"
cmd = [lean, "-M1800", "-j1", "-DElab.async=false", "--root=" + str(out), str(source), "-o", "/tmp/Trace74B65537-" + name + ".olean"]
env = dict(os.environ, LEAN_PATH=library_path)
start = time.monotonic()
timed_out = False
try:
    proc = subprocess.run(cmd, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=30, check=False)
    output = proc.stdout
    exit_code = proc.returncode
except subprocess.TimeoutExpired as exc:
    timed_out = True
    output = exc.stdout or b""
    exit_code = None
elapsed = time.monotonic()-start
(out / "lean.log").write_bytes(output)
result = {
    "declaration": name, "B": 65537, "scope": scope, "memory_max_bytes": int(limit), "swap_max_bytes": int(swap_limit),
    "lean_peak_rss_kib": resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
    "cgroup_memory_peak_available": (cgroup / "memory.peak").exists(),
    "memory_events_before": before, "memory_events_after": (cgroup / "memory.events").read_text(),
    "wall_limit_seconds": 30, "elapsed_seconds": round(elapsed, 3),
    "timed_out": timed_out, "lean_exit_code": exit_code,
    "lean_memory_option_mb": 1800, "lean_path": library_path, "lean_binary": lean,
    "lean_binary_sha256": sha(pathlib.Path(lean)), "source_sha256": sha(source),
    "manifest_sha256": sha(manifest), "parent_source_sha256": sha(parent),
    "log_sha256": sha(out / "lean.log"), "command": cmd,
}
(out / "result.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
print(json.dumps(result, sort_keys=True))
if timed_out:
    raise SystemExit(124)
raise SystemExit(exit_code if exit_code is not None and exit_code >= 0 else 128-(exit_code or 0))

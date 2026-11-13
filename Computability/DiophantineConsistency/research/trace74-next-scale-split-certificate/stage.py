#!/usr/bin/env python3
"""One guarded Lean stage; must run inside an enforced 2 GiB cgroup."""
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
if len(sys.argv) != 3:
    raise SystemExit("usage: stage.py INDEX OUTPUT_ROOT")
index = int(sys.argv[1])
outroot = pathlib.Path(sys.argv[2])
HERE = pathlib.Path(__file__).resolve().parent
manifest_path = HERE / "manifest.json"
manifest = json.loads(manifest_path.read_text())
stages = manifest["stages"]
assert 0 <= index < len(stages) == 34
stage = stages[index]
name = stage["module"]
source = HERE / "src" / (name+".lean")
observation = HERE / "observations" / name
observation.mkdir(parents=True, exist_ok=False)
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
parent = HERE.parent / "trace74-next-scale-kernel-certificate/observations/B65537"
assert sha(parent / "Certificate.lean") == manifest["parent_source_sha256"]
assert sha(parent / "trace.json") == manifest["trace_sha256"]
for item in stages:
    assert sha(HERE / "src" / (item["module"]+".lean")) == item["source_sha256"]
if index:
    progress = json.loads((outroot / "progress.json").read_text())
    assert len(progress) == index
else:
    progress = []
for i, record in enumerate(progress):
    assert record["module"] == stages[i]["module"] and record["status"] == "PASS"
    path = pathlib.Path(record["object"])
    assert path.is_file() and not path.is_symlink() and sha(path) == record["object_sha256"]
prev = None if index == 0 else outroot / "lib" / (stages[index-1]["module"]+".olean")
assert (stage["predecessor"] is None) == (prev is None)
if prev is not None:
    assert prev.is_file() and not prev.is_symlink() and sha(prev) == progress[-1]["object_sha256"]
library_path = "/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib"
mathlib = pathlib.Path("/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib/Mathlib/Data/Nat/GCD/Basic.olean")
mathlib_sha = "823dbab0d8c4e79d9bfc8aaa5637d880364bb11374210059fbd1884e94197e6f"
assert sha(mathlib) == mathlib_sha
module_import = "Mathlib.Data.Nat.GCD.Basic" if index == 0 else stage["predecessor"]
assert source.read_text().splitlines()[0] == "import "+module_import
roots = [outroot / "lib"] + [pathlib.Path(p) for p in library_path.split(":")]
rel = pathlib.Path(module_import.replace(".", "/")+".olean")
resolved = next((p / rel for p in roots if (p / rel).is_file()), None)
assert resolved == (mathlib if index == 0 else prev)
direct_sha = sha(resolved)
lean = pathlib.Path("/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean")
lean_sha = "e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550"
assert sha(lean) == lean_sha
scope = next(line.split(":", 2)[2] for line in pathlib.Path("/proc/self/cgroup").read_text().splitlines() if line.startswith("0::"))
cgroup = pathlib.Path("/sys/fs/cgroup") / scope.lstrip("/")
limit = (cgroup / "memory.max").read_text().strip()
swap_limit = (cgroup / "memory.swap.max").read_text().strip()
assert limit == str(2*1024**3) and swap_limit == "0"
before = (cgroup / "memory.events").read_text()
obj = outroot / "lib" / (name+".olean")
assert not obj.exists() and not obj.is_symlink()
cmd = [str(lean), "-M1800", "-j1", "-DElab.async=false", "--root="+str(HERE / "src"), str(source), "-o", str(obj)]
env = dict(os.environ, LEAN_PATH=str(outroot / "lib")+":"+library_path)
start = time.monotonic()
timed_out = False
try:
    proc = subprocess.run(cmd, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=30, check=False)
    output, code = proc.stdout, proc.returncode
except subprocess.TimeoutExpired as exc:
    output, code, timed_out = exc.stdout or b"", None, True
elapsed = time.monotonic()-start
(observation / "lean.log").write_bytes(output)
text = output.decode(errors="replace")
bad = any(s in text for s in ("sorryAx", "error:", "warning:"))
if name.startswith("Trace74SplitStep"):
    suffix = name.removeprefix("Trace74SplitStep")
    bad |= f"'Trace74ScaledCertificate.transition{suffix}' does not depend on any axioms" not in text
elif name == "Trace74SplitFinal":
    bad |= "'Trace74ScaledCertificate.full_certificate' depends on axioms: [propext, Quot.sound]" not in text
guards_ok = sha(parent / "Certificate.lean") == manifest["parent_source_sha256"] and sha(parent / "trace.json") == manifest["trace_sha256"] and sha(mathlib) == mathlib_sha and sha(lean) == lean_sha
guards_ok &= all(sha(HERE / "src" / (x["module"]+".lean")) == x["source_sha256"] for x in stages)
guards_ok &= all(sha(pathlib.Path(r["object"])) == r["object_sha256"] for r in progress)
ok = code == 0 and not timed_out and not bad and guards_ok and obj.is_file() and not obj.is_symlink()
record = {"module": name, "index": index, "status": "PASS" if ok else "FAIL", "timed_out": timed_out,
    "lean_exit_code": code, "elapsed_seconds": round(elapsed, 3), "lean_peak_rss_kib": resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
    "memory_max_bytes": int(limit), "swap_max_bytes": int(swap_limit), "memory_events_before": before,
    "memory_events_after": (cgroup / "memory.events").read_text(), "scope": scope, "command": cmd,
    "source_sha256": sha(source), "manifest_sha256": sha(manifest_path), "lean_sha256": lean_sha,
    "predecessor": None if prev is None else {"path": str(prev), "sha256": sha(prev)},
    "direct_import": {"module": module_import, "path": str(resolved), "sha256": direct_sha},
    "mathlib_direct_import_sha256": mathlib_sha, "all_guards_ok_after": bool(guards_ok),
    "log_sha256": sha(observation / "lean.log"), "object": str(obj), "object_sha256": sha(obj) if obj.is_file() else None}
(observation / "result.json").write_text(json.dumps(record, indent=2, sort_keys=True)+"\n")
if ok:
    (outroot / "progress.json").write_text(json.dumps(progress+[record], indent=2, sort_keys=True)+"\n")
print(json.dumps(record, sort_keys=True))
raise SystemExit(0 if ok else 1)

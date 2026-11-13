#!/usr/bin/env python3
"""Read-only independent graph/linkage cross-check; prints JSON to stdout."""
import collections
import hashlib
import json
import pathlib
import re
import subprocess

if not __debug__:
    raise RuntimeError("assertions required")
HERE = pathlib.Path(__file__).resolve().parent
ROOT = pathlib.Path(subprocess.check_output(["git", "-C", str(HERE), "rev-parse", "--show-toplevel"], text=True).strip())
FRONT = ROOT / "Computability/DiophantineConsistency/research/current14-source-frontier"
HIST = ROOT / "Computability/DiophantineConsistency/reviews/ipra-standard-current14-historical-pair-terminal"
PLAN = pathlib.Path("/tmp/ipra-current14-historical-paired-run-01/strict-plan.json")
read = lambda p: json.loads(p.read_text())
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
m = read(FRONT / "historical-manifest.json")
old = read(FRONT / "result.json")
cur = json.loads(subprocess.check_output(["python3", "-I", "-S", "-B", str(FRONT / "audit.py")], text=True))
prep = read(HIST / "preparation.json")
freezer = read(HIST / "freezer-observation.json")
pair = read(HIST / "pair-state.json")
outer = read(HIST / "outer-terminal-observation.json")
assert sha(FRONT / "historical-manifest.json") == prep["new_snapshot_sha256"] == freezer["snapshot_manifest_sha256"]
assert sha(HIST / "freezer-observation.json") == prep["freezer_observation_sha256"]
assert sha(HIST / "preparation.json") == pair["preparation_sha256"]
assert sha(HIST / "pair-state.json") == outer["pair_state_sha256"]
assert outer["observed_exit_code"] == 0 and pair["status"] == "MATCHED_SELECTIVE_PASS"
for name in ("author-rebuild-state.json", "peer-rebuild-state.json"):
    state = read(HIST / name)
    assert state["new_snapshot_sha256"] == sha(FRONT / "historical-manifest.json")
    assert state["preparation_sha256"] == sha(HIST / "preparation.json")
    assert state["status"] == "PASS" and len(state["records"]) == 16
sources, target = m["sources"], m["target"]
seen, outside, reverse = set(), set(), collections.defaultdict(set)
queue = collections.deque([target])
while queue:
    module = queue.popleft()
    if module not in sources:
        outside.add(module)
        continue
    if module in seen:
        continue
    seen.add(module)
    for dep in sources[module]["imports"]:
        reverse[dep].add(module)
        queue.append(dep)
changed, missing = [], []
for module in sorted(seen):
    path = ROOT / sources[module]["workspace_path"]
    if not path.is_file():
        missing.append(module)
    elif sha(path) != sources[module]["sha256"]:
        changed.append(module)
affected = set(changed + missing)
queue = collections.deque(affected)
while queue:
    for child in reverse[queue.popleft()]:
        if child not in affected:
            affected.add(child)
            queue.append(child)
assert set(changed) == {x["module"] for x in old["changed"]} == {x["module"] for x in cur["changed"]}
assert missing == [] and old["import_drifts"] == cur["import_drifts"] == []
for module in changed:
    header = []
    for line in (ROOT / sources[module]["workspace_path"]).read_text().splitlines():
        if not line.strip():
            continue
        match = re.fullmatch(r"import[ \t]+([^\n]+)", line)
        if not match:
            break
        header.extend(match.group(1).split("--", 1)[0].split())
    assert header == sources[module]["imports"]
assert affected == set(old["affected_on_historical_graph"]) == set(cur["affected_on_historical_graph"])
assert outside == set(m["external_modules"])
assert set(x.split(".")[0] for x in outside) == {"Foundation", "Mathlib", "Lean", "Init"}
plan = read(PLAN)
assert sha(PLAN) == m["strict_plan_sha256"]
assert set(plan["sources"]) == seen
assert all(plan["sources"][n]["imports"] == sources[n]["imports"] and
           plan["sources"][n]["source_sha256"] == sources[n]["sha256"] for n in seen)
assert outside == set(plan["external_modules"])
print(json.dumps({
    "status": "PASS_QUALIFIED_SOURCE_FRONTIER_ONLY", "historical_manifest_sha256": sha(FRONT / "historical-manifest.json"),
    "preparation_sha256": sha(HIST / "preparation.json"), "strict_plan_sha256": sha(PLAN),
    "recorded_head": old["workspace_head"], "rerun_head": cur["workspace_head"],
    "project_ancestors": len(seen), "external_imports": len(outside), "changed": len(changed),
    "missing": len(missing), "reported_import_drifts": len(cur["import_drifts"]), "changed_headers_checked": len(changed),
    "reverse_closure": len(affected), "target_affected": target in affected,
    "original_audit_sha256": sha(FRONT / "audit.py"),
}, indent=2, sort_keys=True))

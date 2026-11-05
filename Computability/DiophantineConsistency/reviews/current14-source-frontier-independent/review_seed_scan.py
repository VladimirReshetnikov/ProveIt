#!/usr/bin/env python3
"""Review recorded seed-scan structure; hash only one sample per used provider."""
import collections
import hashlib
import json
import pathlib
import subprocess

if not __debug__:
    raise RuntimeError("assertions required")
HERE = pathlib.Path(__file__).resolve().parent
ROOT = pathlib.Path(subprocess.check_output(["git", "-C", str(HERE), "rev-parse", "--show-toplevel"], text=True).strip())
FRONT = ROOT / "Computability/DiophantineConsistency/research/current14-source-frontier"
HIST = ROOT / "Computability/DiophantineConsistency/reviews/ipra-standard-current14-historical-pair-terminal"
read = lambda p: json.loads(p.read_text())
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
manifest = read(FRONT / "historical-manifest.json")
frontier = read(FRONT / "result.json")
prep = read(HIST / "preparation.json")
scan = read(FRONT / "seed-scan-result.json")
assert sha(FRONT / "historical-manifest.json") == prep["new_snapshot_sha256"]
assert sha(FRONT / "result.json") == "5392cded531449193da23a695a165eaf1cefcdae2df3a1f9a1700c83acd234a7"
assert sha(HIST / "preparation.json") == "53cedecdd1e357cbb800a51a783fa4cf7c0c01591e493080e7c7576bb2767d9d"
seen, stack = set(), [manifest["target"]]
while stack:
    mod = stack.pop()
    if mod in seen or mod not in manifest["sources"]:
        continue
    seen.add(mod)
    stack.extend(manifest["sources"][mod]["imports"])
need = seen-set(frontier["affected_on_historical_graph"])
paths = scan["paths"]
matched = [m for m, _ in paths]
unmatched = scan["unmatched"]
assert len(need) == scan["checked"] == 793
assert len(matched) == len(set(matched)) == scan["matched"] == 489
assert len(unmatched) == len(set(unmatched)) == 304
assert set(matched).isdisjoint(unmatched) and set(matched).union(unmatched) == need
providers = [pathlib.Path(s) for s in (
    "/tmp/direct80-coherent-rebuild-u2iz4c67/lib",
    "/tmp/trace74-direct-four-block-1zltaw2f/lib",
    "/tmp/p65-post-merge-replay/lib",
    "/tmp/derivation-endpoint-combined-20261031",
    "/tmp/adaptive13-main-orientation-ke21opyr/lib",
)]
groups = collections.defaultdict(list)
seeds = prep["seeds"]["author"]
for module, name in paths:
    rel = module.replace(".", "/")+".olean"
    assert rel in seeds
    found = [p for p in providers if p / rel == pathlib.Path(name)]
    assert len(found) == 1
    groups[str(found[0])].append((module, pathlib.Path(name)))
assert all(m.replace(".", "/")+".olean" in seeds for m in need)
samples = []
for provider, entries in sorted(groups.items()):
    module, path = entries[0]
    actual = sha(path)
    assert actual == seeds[module.replace(".", "/")+".olean"]
    samples.append({"provider": provider, "module": module, "sha256": actual})
print(json.dumps({"status": "RECORDED_SCAN_STRUCTURE_AND_TWO_SAMPLES_PASS",
    "checked": len(need), "matched": len(matched), "unmatched": len(unmatched),
    "recorded_provider_counts": {p: len(v) for p, v in sorted(groups.items())},
    "samples": samples, "scan_script_sha256": sha(FRONT / "scan_seed_objects.py"),
    "scan_result_sha256": sha(FRONT / "seed-scan-result.json"),
    "scope": "Structural consistency and two samples only; no full hash rescan or ancestry authentication."
}, indent=2, sort_keys=True))

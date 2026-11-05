#!/usr/bin/env python3
"""Static checks of the P64 screen and stored result; no search rerun."""
import hashlib
import json
import pathlib
import subprocess

HERE = pathlib.Path(__file__).resolve().parent
ROOT = pathlib.Path(subprocess.check_output(["git", "-C", str(HERE), "rev-parse", "--show-toplevel"], text=True).strip())
PACKET = ROOT / "Computability/DiophantineConsistency/research/p64-local-rewrite-search"
GRAPH = ROOT / "Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/positive14/polynomial.json"
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
graph = json.loads(GRAPH.read_text())
result = json.loads((PACKET / "result.json").read_text())
assert sha(GRAPH) == result["graph_sha256"] == "b9731360a30bcbcfd6f9161241cafb01b8c5d68aa40b84ddc50ba689a0745d0e"
assert sha(PACKET / "search.py") == result["source_sha256"] == "772c02d5cca78720adcbf4602ebcf0652b70ac1e928655d590f00bb548687196"
assert sha(PACKET / "result.json") == "b9a90f77bf85a9f3c0e97697297213ac3d41b726f9992426be0d1bfb9d6f079a"
rows = graph["source"]
available = set(graph["witnesses"] + graph["fixed_numerals"]) | set(range(5))
assert len(available) == 23 and len(rows) == 83
initial = len(available)
deps = {}
for name, op, a, b in rows:
    assert name not in available and op in ("+", "-", "*") and a in available and b in available
    deps[name] = (a, b)
    available.add(name)
live, stack = set(), [graph["output"]]
while stack:
    name = stack.pop()
    if name in deps and name not in live:
        live.add(name)
        stack.extend(deps[name])
assert len(live) == result["exact_target"]["original_live"] == 83
counts = result["exact_target"]["counts"]
first = sum(2*(initial+i)**2+(initial+i) for i in range(len(rows)))
second = sum(4*(initial+i)-1 for i in range(len(rows)))
assert counts["first_gates"] == first == 780532
assert counts["second_queries"] == second == 21165
assert counts["targets"] == 83 and counts["targets_with_sample_zero"] == 0
assert counts["sample_zero_nonconstant"] == 0 and counts["square_root_queries"] == 192
assert not result["exact_target"]["one_gate_candidates"] and not result["exact_target"]["two_gate_candidates"]
assert not result["extras"]["aliases"] and not result["extras"]["square_only_negations"]
assert result["positive_control"]["one_gate_candidates"] or result["positive_control"]["two_gate_candidates"]
assert result["square_sign_control"]["square_only_negations"]
print(json.dumps({"status": "STATIC_SCREEN_SANITY_PASS", "graph_sha256": sha(GRAPH),
    "screen_sha256": sha(PACKET / "search.py"), "recorded_result_sha256": sha(PACKET / "result.json"),
    "initial_inputs": initial, "topological_rows": len(rows), "live_rows": len(live),
    "first_gate_count": first, "second_query_count_given_no_zero_divisors": second,
    "square_queries_recorded": counts["square_root_queries"],
    "scope": "Static source/recorded-output checks only; full modular search was not rerun."}, indent=2, sort_keys=True))

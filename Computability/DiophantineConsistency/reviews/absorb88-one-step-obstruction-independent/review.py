#!/usr/bin/env python3
"""Read-only digest and finite-illustration check; no Lean invocation."""
import hashlib
import json
import pathlib
import subprocess

HERE = pathlib.Path(__file__).resolve().parent
ROOT = pathlib.Path(subprocess.check_output(["git", "-C", str(HERE), "rev-parse", "--show-toplevel"], text=True).strip())
PACKET = ROOT / "Computability/DiophantineConsistency/research/ordinary12-absorb88-one-step-conditional-obstruction"
GRAPH = ROOT / "Computability/DiophantineConsistency/research/ordinary12-absorb88-probe/graph-dag.json"
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(PACKET / "check.py") == "d0f039d0707e5217d1459f7145c84ce1ad237a30cfbad6ebc1ad95ca666f5a64"
assert sha(PACKET / "result.json") == "0b75c2eba58d26e2df2abe08b40e42686187302d13ffdaba965e9cc1f9db3c3a"
assert sha(GRAPH) == "84a9a529636d6cadcf0f0c673c0728aa7b6fcbc0e2f2ac562a377553de831b25"
actual = subprocess.check_output(["python3", "-I", "-S", "-B", str(PACKET / "check.py")])
assert actual == (PACKET / "result.json").read_bytes()
data = json.loads(actual)
assert data["status"] == "PASS" and data["old"]["A0"] == data["new"]["A0"] == 0
assert data["old"]["Bt"] == 12 and data["new"]["Bt"] == -24
assert data["main_residual_unchanged_and_nonzero"] and data["ordinary_residual_unchanged_and_nonzero"]
print(json.dumps({"status": "ILLUSTRATION_REPRODUCED", "checker_sha256": sha(PACKET / "check.py"),
    "result_sha256": sha(PACKET / "result.json"), "graph_sha256": sha(GRAPH),
    "scope": "Finite first-factor illustration only; no Lean invocation or full graph zero."}, indent=2, sort_keys=True))

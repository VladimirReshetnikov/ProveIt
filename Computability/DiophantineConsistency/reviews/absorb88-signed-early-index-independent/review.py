#!/usr/bin/env python3
"""Read-only digest check of the stated source and two direct objects."""
import hashlib
import json
import pathlib
import subprocess

HERE = pathlib.Path(__file__).resolve().parent
ROOT = pathlib.Path(subprocess.check_output(["git", "-C", str(HERE), "rev-parse", "--show-toplevel"], text=True).strip())
items = {
    "source": (ROOT / "Computability/DiophantineConsistency/research/ordinary12-absorb88-signed-early-index-draft/Absorb88SignedEarlyIndex.lean", "90af476ee496d974a46c3292afb3850ae281dbc12726c3b9919b84a0605765d8"),
    "output_object": (pathlib.Path("/tmp/Absorb88SignedEarlyIndex.olean"), "28ab57f0fd4b9ad797288688903f2b8b933f2fbe7d43e3b36234c1bfc2fdaad5"),
    "rank_congruence_object": (pathlib.Path("/tmp/Absorb88SignedRankCongruence.olean"), "d8265fec7e027b457ba69b9d29199092a5ebac6947249705e5be58f96761e88a"),
    "graph_gap_object": (pathlib.Path("/tmp/Absorb88GraphGap.olean"), "4221086c49220f43faaab42cb0159aade3b847c3f9369edc9844e976f820b7f3"),
}
out = {}
for name, (path, expected) in items.items():
    actual = hashlib.sha256(path.read_bytes()).hexdigest()
    assert actual == expected
    out[name] = {"path": str(path), "sha256": actual}
print(json.dumps({"status": "DIGESTS_MATCH_ONLY", "files": out,
                  "scope": "No Lean invocation or object ancestry authentication."}, indent=2, sort_keys=True))

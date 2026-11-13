#!/usr/bin/env python3
"""Read-only pins and exact row cut; does not replay any witness proof."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
PINS = {
    "research/current14-carrier64-current-full-zero/README.md": "81a50389d94021a08dd878fa6d8e006a57297afe12a53cdcc69b62b4d397b5c0",
    "research/current14-carrier64-current-full-zero/result.json": "a9ce4a69a82e58009e65895f00fd8e61c869e98c3fe68540ed32b0e57d686194",
    "reviews/current14-carrier64-current-full-zero-independent/README.md": "517414af485e9505406c11227ad4e908f5cdcdb363d2e77f2385dbcaccd92b14",
    "research/current14-carrier64-transport-proposal/README.md": "0c14ee32ec78e23fb770852ba5bfc89ac222303e16585734e5a780a17a06da96",
    "research/current14-carrier64-transport-proposal/graph.json": "f3bc67492c0aa88c9881bf7e2c39e1586e38b3324305b025b010c0912625af43",
    "candidates/one-page-padding-staircase-carrier65-2011/polynomial.json": "f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e",
    "research/current14-mf-base-only-endpoint-attempt02/README.md": "a81aba0739339af6f265122091d6c8fdfa1fce12136fa3371b72607a1e848df6",
    "research/current14-mf-translated-endpoint/README.md": "363261f518301f712705cfd84a6533b0bf7d96d3f24e2fe894c114a28348b107",
}
for path, expected in PINS.items():
    if hashlib.sha256((ROOT / path).read_bytes()).hexdigest() != expected:
        raise RuntimeError(f"source pin changed: {path}")
old = json.loads((ROOT / "candidates/one-page-padding-staircase-carrier65-2011/polynomial.json").read_bytes())
new = json.loads((ROOT / "research/current14-carrier64-transport-proposal/graph.json").read_bytes())
receipt = json.loads((ROOT / "research/current14-carrier64-current-full-zero/result.json").read_bytes())
if len(old["source"]) != 65 or len(new["source"]) != 64:
    raise RuntimeError("unexpected graph lengths")
if old["fixed_numerals"] != new["fixed_numerals"] or old["output"] != new["output"]:
    raise RuntimeError("port or output mismatch")
if old["witnesses"][:2] != new["witnesses"][:2] or old["witnesses"][2] != "alpha" or new["witnesses"][2] != "C" or old["witnesses"][3:] != new["witnesses"][3:]:
    raise RuntimeError("witness coordinate mismatch")
if [row for row in old["source"] if row not in new["source"]] != [["C", "-", "qF", "alpha"], ["gap_product", "*", "qm", "qF"], ["gap", "+", "gap_product", "alpha"]]:
    raise RuntimeError("unexpected old-only rows")
if [row for row in new["source"] if row not in old["source"]] != [["gap_product", "*", "q", "qF"], ["gap", "-", "gap_product", "C"]]:
    raise RuntimeError("unexpected candidate-only rows")
if receipt["pins"]["research/current14-carrier64-transport-proposal/graph.json"] != PINS["research/current14-carrier64-transport-proposal/graph.json"]:
    raise RuntimeError("witness receipt candidate mismatch")
if receipt["pins"]["candidates/one-page-padding-staircase-carrier65-2011/polynomial.json"] != PINS["candidates/one-page-padding-staircase-carrier65-2011/polynomial.json"]:
    raise RuntimeError("witness receipt 2011 port binding mismatch")
print("PASS: source pins, 2011 witness binding and exact graph row cut; no witness proof replayed")

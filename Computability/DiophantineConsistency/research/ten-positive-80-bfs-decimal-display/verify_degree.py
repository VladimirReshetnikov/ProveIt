#!/usr/bin/env python3
"""Certify degree using a modular leading-coefficient witness on the diagonal."""
import gzip
import hashlib
import json
from pathlib import Path
import sys

if sys.flags.optimize:
    raise RuntimeError("optimized Python is not supported")

HERE = Path(__file__).resolve().parent
EXPECTED = "fcc5e40f5d22320541ec2af5857725ceafaa69d0df36708ec60d6b9a40a71f01"
MOD = 1000000007
GRAPH_ROOT = HERE.parent / "ten-positive-unshift-t-finite"
raw_json = (GRAPH_ROOT / "data/equation_qcube_V2.json").read_bytes()
if hashlib.sha256(raw_json).hexdigest() != EXPECTED:
    raise ValueError("candidate graph changed")
data = json.loads(raw_json)
env = {name: (1, 1) for name in data["witnesses"]}
for name, info in data["coefficient_binding"]["ports"].items():
    payload = (GRAPH_ROOT / "coefficients" / info["file"]).read_bytes()
    raw = gzip.decompress(payload)
    if hashlib.sha256(payload).hexdigest() != info["gzip_sha256"] or hashlib.sha256(raw).hexdigest() != info["raw_sha256"]:
        raise ValueError("coefficient bytes changed: " + name)
    env[name] = (0, int.from_bytes(raw, "little") % MOD)


def operand(value):
    if type(value) is int:
        return (0, value % MOD)
    return env[value]


for name, op, a, b in data["source"]:
    da, ca = operand(a)
    db, cb = operand(b)
    if op == "*":
        value = da + db, ca * cb % MOD
    elif op in ("+", "-"):
        degree = max(da, db)
        value = degree, ((ca if da == degree else 0) +
                         (1 if op == "+" else -1) * (cb if db == degree else 0)) % MOD
    else:
        raise ValueError("unexpected operation")
    env[name] = value

degree, coefficient = env[data["output"]]
if degree != 750 or coefficient == 0:
    raise ValueError("degree witness did not certify the claimed degree")
print(json.dumps({"status": "PASS_MODULAR_DEGREE_WITNESS", "upper_bound": degree,
                  "diagonal_leading_coefficient_mod_prime": coefficient,
                  "prime": MOD, "equation_sha256": EXPECTED,
                  "scope": "external exact-degree certificate, not a Lean theorem"}, sort_keys=True))

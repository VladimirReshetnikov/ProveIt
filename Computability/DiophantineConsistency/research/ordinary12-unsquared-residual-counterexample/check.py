#!/usr/bin/env python3
"""Evaluate the pinned 94-operation graph at a natural-valued counterexample."""
from hashlib import sha256
from pathlib import Path
import json
import operator

path = Path(__file__).resolve().parent.parent / "ordinary12-sum-of-squares-candidate" / "candidate.json"
data = path.read_bytes()
expected = "dc13e87a45a687e99e9bcb1cd3276e7c80d3e014bb7f51074084ca3214ac45ee"
if sha256(data).hexdigest() != expected:
    raise SystemExit("candidate.json hash mismatch")
graph = json.loads(data)
witnesses = (0, 0, 1, 1, 1, 0, 0, 1, 1, 4, 2, 1)
ports = (1, 1, 1, 1)
if graph["witnesses"] != ["J", "F", "alpha", "t", "T", "X", "Y", "r", "eta", "zeta", "n", "gamma"]:
    raise SystemExit("unexpected witness order")
if graph["fixed_numerals"] != ["beta", "K0", "MC", "MF"]:
    raise SystemExit("unexpected port order")
env = dict(zip(graph["witnesses"], witnesses))
env.update(zip(graph["fixed_numerals"], ports))
ops = {"+": operator.add, "-": operator.sub, "*": operator.mul}
for name, op, left, right in graph["source"]:
    left = env[left] if isinstance(left, str) else left
    right = env[right] if isinstance(right, str) else right
    env[name] = ops[op](left, right)
a, b, c = (env[name] for name in ("A0", "A1", "N"))
if (a, b, c) != (0, 144, -20736):
    raise SystemExit("unexpected residuals")
if a*a + b*b + c != 0 or env["P12"] != 430002432:
    raise SystemExit("counterexample failed")
print("A0 =", a, "; A1 =", b, "; N =", c)
print("A0² + A1² + N =", a*a + b*b + c)
print("A0² + A1² + N² =", env["P12"])

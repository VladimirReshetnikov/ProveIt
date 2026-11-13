#!/usr/bin/env python3
"""Read-only exact check of trace74's retained beta/K0 payload binding.

This does not formalize JSON, gzip, Lean or PDF semantics in Lean.
"""
import gzip
import hashlib
import json
import math
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit("use python3 -I -S -B without optimization")

BASE = Path(__file__).resolve().parents[2]
CANDIDATE = BASE / "research/trace74-mask-coordinate-probe/candidate.json"
COEFFICIENTS = BASE / "candidates/ten-positive-qcube-product-square/coefficients"
EXPECTED_CANDIDATE = "dafefaa40173c9f75c414171896e19ddcf5f5eec82a0612d82a4e23988ee7353"
EXPECTED_K0 = "0a86821a704294199c2e1a50379d242c96840a3366e9d965689ba3d74605203f"
data = CANDIDATE.read_bytes()
assert hashlib.sha256(data).hexdigest() == EXPECTED_CANDIDATE
candidate = json.loads(data)
assert candidate["fixed_numerals"] == ["beta", "K0", "MC", "MF"]
ports = candidate["coefficient_binding"]["ports"]
values, pins = {}, {}
for label in ("beta", "K0", "MC", "MF"):
    record = ports[label]
    compressed = (COEFFICIENTS / record["file"]).read_bytes()
    raw = gzip.decompress(compressed)
    assert hashlib.sha256(compressed).hexdigest() == record["parent_gzip_sha256"]
    digest = hashlib.sha256(raw).hexdigest()
    assert digest == record["raw_sha256"]
    value = int.from_bytes(raw, "little")
    assert value.bit_length() == record["bits"]
    values[label], pins[label] = value, digest
assert pins["K0"] == EXPECTED_K0
B = 67 * 8807
assert B == 590069 and values["beta"] == (1 << B) - 1
q, h = 1 << B, values["beta"]
r = 3056651345
assert r >= B
wmod = 1 << ((r - B) % B)
assert math.gcd(values["K0"] + wmod, h) == 1
# If raw beta is mutated, the exact symbolic equality must fail.
assert (values["beta"] ^ 1) != (1 << B) - 1
# A changed K0 byte cannot pass the pinned raw-byte hash check.
mutated = bytearray(gzip.decompress((COEFFICIENTS / ports["K0"]["file"]).read_bytes()))
mutated[0] ^= 1
assert hashlib.sha256(mutated).hexdigest() != EXPECTED_K0
print(json.dumps({
    "status": "PASS", "candidate_sha256": EXPECTED_CANDIDATE,
    "raw_sha256": pins, "beta_bits": values["beta"].bit_length(),
    "K0_bits": values["K0"].bit_length(), "symbolic_beta": "2^(67*8807)-1",
    "w_mod_h_exponent": (r-B) % B, "gcd_K0_plus_w_h": 1,
    "scope": "external retained-payload bytes and fixed-beta/K0 gcd only; no Lean port or graph-zero theorem"
}, sort_keys=True))

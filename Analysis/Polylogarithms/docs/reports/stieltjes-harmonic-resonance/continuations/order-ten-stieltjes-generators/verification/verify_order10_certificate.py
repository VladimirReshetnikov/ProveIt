#!/usr/bin/env python3
from __future__ import annotations
import json
from pathlib import Path
from order10_core import (
    A, B_MAX, B_MIN, B_RETAINED_MIN, MAX_FACTORIAL, MAX_MATRIX_FACTORIAL, PRIME,
    compute_all_residues, is_prime, residue_digest,
)

HERE = Path(__file__).resolve().parent
CERT = HERE / "order10_modular_certificate.json"
obj = json.loads(CERT.read_text(encoding="utf-8"))

assert obj["schema"] == "proveit.order-ten-modular-certificate.v2"
assert obj["prime"] == PRIME and is_prime(PRIME)
assert obj["a"] == A
assert obj["b_min"] == B_MIN and obj["b_max"] == B_MAX
assert obj["direct_matrix_range"] == [B_MIN, B_RETAINED_MIN - 1]
assert obj["retained_matrix_range"] == [B_RETAINED_MIN, B_MAX]
assert obj["max_factorial_argument"] == MAX_MATRIX_FACTORIAL < PRIME
assert obj["factorial_table_limit"] == MAX_FACTORIAL < PRIME
assert obj["max_bernoulli_index_used"] == 2 * (B_MAX - 1) < PRIME - 1
assert obj["max_bernoulli_index_generated"] == 2 * B_MAX < PRIME - 1
assert obj["max_multiplier_factorial_argument"] == 4 * (B_MAX - 1) + 2 < PRIME

assert obj["repository_snapshot"] == "04bf92d507588a26abadbaee1beb1e7350c8bffb"
assert "det(M_{5,b}) modulo P" in obj["residue_definition"]["6<=b<=9"]
assert "det(A^[5]" in obj["residue_definition"]["10<=b<=1919"]
assert "no terminal newline" in obj["canonical_encoding"]

expected = compute_all_residues()
recorded = [int(x) for x in obj["residues"]]
assert expected == recorded
assert len(recorded) == obj["count"] == B_MAX - B_MIN + 1
assert all(0 < x < PRIME for x in recorded)
assert obj["all_residues_nonzero"] is True
assert residue_digest(recorded) == obj["residue_sha256"]

sentinels = {
    "b=6": recorded[6 - B_MIN],
    "b=8": recorded[8 - B_MIN],
    "b=10": recorded[10 - B_MIN],
    "b=962": recorded[962 - B_MIN],
    "b=1919": recorded[1919 - B_MIN],
}
assert sentinels == obj["sentinels"]

print("PASS: exact one-prime certificate")
print(f"  modulus: {PRIME}")
print(f"  cases:   {len(recorded)} ({B_MIN} <= b <= {B_MAX})")
print(f"  zeros:   {sum(x == 0 for x in recorded)}")
print(f"  sha256:  {obj['residue_sha256']}")
print(f"  sentinels: {sentinels}")

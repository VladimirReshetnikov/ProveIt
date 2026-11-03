#!/usr/bin/env python3
"""Externally compare the pinned retained beta gzip payload to the Lean byte recipe."""
from hashlib import sha256
from pathlib import Path
import gzip
import json

here = Path(__file__).resolve().parent
repo = here.parents[4]
payload = repo / 'Computability/DiophantineConsistency/candidates/free-j-polarized-positive/source/positive/coefficients/payloads/beta.bin.gz'
binding = payload.parent.parent / 'BINDING.json'
binding_before = binding.read_bytes()
binding_hash = sha256(binding_before).hexdigest()
binding_pin = 'dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01'
meta = json.loads(binding_before)['ports']['beta']
compressed_before = payload.read_bytes()
raw = gzip.decompress(compressed_before)
compressed_after = payload.read_bytes()
expected = bytes([255]) * 73758 + bytes([31])
actual_raw_hash = sha256(raw).hexdigest()
expected_raw_hash = '0664a868cbfef9869ea05c40a1c445563f685ff857092594c1c1223bc4b21f9d'
checks = {
    'binding_sha256': binding_hash,
    'binding_sha_matches_pin': binding_hash == binding_pin,
    'binding_unchanged': binding_before == binding.read_bytes(),
    'compressed_sha256': sha256(compressed_before).hexdigest(),
    'compressed_sha_matches_binding': sha256(compressed_before).hexdigest() == meta['sha256_gzip'],
    'compressed_unchanged': compressed_before == compressed_after,
    'raw_sha256': actual_raw_hash,
    'expected_raw_sha256': expected_raw_hash,
    'raw_length': len(raw),
    'recipe_length': len(expected),
    'raw_equals_recipe': raw == expected,
    'raw_sha_matches_pin': actual_raw_hash == expected_raw_hash,
    'raw_sha_matches_binding': actual_raw_hash == meta['sha256_raw'],
    'length_matches_binding': len(raw) == meta['raw_bytes'],
    'minimal_length_and_bits_match_binding': int.from_bytes(raw, 'little').bit_length() == meta['bits'],
}
print(json.dumps(checks, indent=2, sort_keys=True))
if not all((checks['compressed_unchanged'], checks['raw_equals_recipe'], checks['raw_sha_matches_pin'],
            checks['binding_sha_matches_pin'], checks['binding_unchanged'],
            checks['compressed_sha_matches_binding'], checks['raw_sha_matches_binding'],
            checks['length_matches_binding'], checks['minimal_length_and_bits_match_binding'])):
    raise SystemExit(1)

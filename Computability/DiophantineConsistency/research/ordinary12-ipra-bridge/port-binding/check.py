#!/usr/bin/env python3
"""Recheck manuscript-98's recorded full tuple against available payloads."""
import copy
import gzip
import hashlib
import json
from pathlib import Path

if not __debug__:
    raise RuntimeError('port checks require Python assertions enabled')
ROOT = Path(__file__).resolve().parents[5]
base = ROOT / 'Computability/DiophantineConsistency'
manuscript = base / 'con-zfc-diophantine-forms/104-valuation-signed/supplemental/ordinary98'
binding_path = base / 'con-zfc-diophantine-forms/69-cones-pell/positive/native/ACTIVE_BINDING.json'
candidate_path = base / 'research/ordinary-unit-products/p12_ordinary_degree70.json'
payload_dir = base / 'candidates/ten-positive-shifted-strong/coefficients'
other_dir = base / 'research/ten-positive-saturated-pell/coefficients/compact44_bfs'
H = lambda raw: hashlib.sha256(raw).hexdigest()
provenance_raw = (manuscript / 'PROVENANCE.json').read_bytes()
binding_raw = binding_path.read_bytes()
parent_raw = (manuscript / 'ordinary12_parent100.json').read_bytes()
candidate_raw = candidate_path.read_bytes()
assert H(provenance_raw) == '9c0acb74354694aca7b2e5311aa3cb87fc67cc3b7b03ce31ea2fc1ca10af3be5'
assert H(binding_raw) == 'adc0967f90b2f9e1f44aca708987d2c844dda82193e4e8d9b9a7a031b4a69d18'
assert H(parent_raw) == 'dba57288cdc5dec5c106480d6e8663b203c6a969891e2a29ed5f5d35dc5149e9'
assert H(candidate_raw) == '444c25b68fbfee600ae174cb5bad1931897a55ffe2f9570fd22f3281f6e97010'
provenance = json.loads(provenance_raw)
binding = json.loads(binding_raw)
parent, candidate = json.loads(parent_raw), json.loads(candidate_raw)
for key in ('witnesses', 'fixed_numerals', 'source', 'output', 'operations', 'operation_breakdown', 'exact_degree'):
    assert parent[key] == candidate[key], key
assert len(candidate['witnesses']) == 12 and len(candidate['source']) == 100
assert candidate['fixed_numerals'] == ['beta', 'K0', 'MC', 'MF']
recorded = {row['path']: row['sha256'] for row in provenance['copied_native_files']}
assert recorded['native/ACTIVE_BINDING.json'] == H(binding_raw)

def accepted(rows):
    for port, row in binding['ports'].items():
        data = rows[port]
        if H(data) != row['sha256_gzip']: return False
        raw = gzip.decompress(data)
        if H(raw) != row['sha256_raw'] or len(raw) != row['raw_bytes']: return False
        if recorded['native/' + row['file']] != H(data): return False
    return True

payloads = {port: (payload_dir / Path(row['file']).name).read_bytes() for port, row in binding['ports'].items()}
assert accepted(payloads)
values = {port: int.from_bytes(gzip.decompress(data), 'little') for port, data in payloads.items()}
assert values['beta'] == (1 << 590069) - 1
assert 0 < values['MC'] < values['beta'] < values['MF'] < 2 * values['beta'] and values['K0'] >= 1
assert binding['ports']['K0']['upstream_port'] == 'K'
assert binding['ports']['MF']['upstream_port'] == 'MF_source'
other = {port: (other_dir / Path(row['file']).name).read_bytes() for port, row in binding['ports'].items()}
raw_hashes = {port: H(gzip.decompress(data)) for port, data in payloads.items()}
alternate_raw_hashes = {port: H(gzip.decompress(data)) for port, data in other.items()}
assert all(raw_hashes[p] == alternate_raw_hashes[p] for p in ('beta', 'MC', 'MF'))
assert raw_hashes['K0'] == 'c6d523bd32af8dd0345db843cdadf6932bfcad186912a6d112314b60657c554e'
assert alternate_raw_hashes['K0'] == '4364134a56b54cf132beeb9acd8e832be68f9083f4359ace4a588a1ea76a60f7'
wrong = copy.copy(payloads)
wrong['K0'] = other['K0']
assert not accepted(wrong)
wrong = copy.copy(payloads)
wrong['MF'] = payloads['MC']
assert not accepted(wrong)
print('PASS_MANUSCRIPT98_WHOLE_TUPLE_AND_PARENT100', json.dumps({
    'provenance_sha256': H(provenance_raw), 'binding_sha256': H(binding_raw),
    'parent100_sha256': H(parent_raw), 'candidate_sha256': H(candidate_raw),
    'raw_hashes': raw_hashes, 'alternate_K0_sha256': alternate_raw_hashes['K0'],
    'alternate_K0_and_swapped_MF_rejected': True}, sort_keys=True))
